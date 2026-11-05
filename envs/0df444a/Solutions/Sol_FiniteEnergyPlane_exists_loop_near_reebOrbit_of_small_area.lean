-- Prove2me | solution 1 for FiniteEnergyPlane.exists_loop_near_reebOrbit_of_small_area
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:21:55.063915+00:00
-- url     : https://prove2.me/submissions/ee03748f-0015-4a14-a6a9-e89636d4751a

import Definitions.Def_FiniteEnergyPlane_Compactness
import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le
import Theorems.Thm_FiniteEnergyPlane_exists_reebOrbit_loop_of_cylinder
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

variable {n : ℕ}

/-- The partner index `2i ↔ 2i+1`. -/
def pairIdx (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

theorem pairIdx_involutive : Function.Involutive (pairIdx (n := n)) := by
  intro k
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp; omega

theorem j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

theorem j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := j0_add, map_smul' := j0_smul }

@[simp] theorem j0L_apply (u : V n) : j0L u = j0 u := rfl

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply]

theorem omega0_antisymm (u v : V n) : omega0 u v = -omega0 v u := by
  have e := Equiv.sum_comp (Function.Involutive.toPerm _ (pairIdx_involutive (n := n)))
    (fun k => j0 u k * v k)
  simp only [omega0, dot]
  rw [← e, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Involutive.coe_toPerm, pairIdx, j0]
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) + 1 - 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp
    rw [this]; ring
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp; omega
    rw [this]; ring

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Radial scaling in the symplectization: `proj` is invariant and `a` shifts by `log c / 2`. -/
theorem proj_aCoord_smul_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (hc : 0 < c) (y : V n) (hy : y ≠ 0) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
    ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
  have h1 : scaleToS H y = r := by
    unfold scaleToS
    rw [dif_pos e1]
    exact hru _ (Classical.choose_spec e1)
  have h2 : scaleToS H (c • y) = r / c := by
    unfold scaleToS
    rw [dif_pos e2]
    have hs2 := Classical.choose_spec e2
    have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
    rw [← this, mul_div_cancel_right₀ _ hc.ne']
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  · unfold aCoord
    rw [h1, h2, Real.log_div hr0.ne' hc.ne']
    ring

/-- Uniform convergence on `[0, 1]` of `1`-periodic functions is uniform convergence on `ℝ`. -/
theorem tendstoUniformly_of_periodic_aux {F : Type*} [NormedAddCommGroup F] (f : ℕ → ℝ → F)
    (g : ℝ → F) (hf : ∀ k, Function.Periodic (f k) 1) (hg : Function.Periodic g 1)
    (h : TendstoUniformlyOn f g atTop (Set.Icc 0 1)) : TendstoUniformly f g atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h ε hε] with k hk t
  have ht : Int.fract t ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have e1 : f k t = f k (Int.fract t) := by
    rw [Int.fract, ← (hf k).sub_int_mul_eq ⌊t⌋, mul_one]
  have e2 : g t = g (Int.fract t) := by
    rw [Int.fract, ← hg.sub_int_mul_eq ⌊t⌋, mul_one]
  rw [e1, e2]
  exact hk _ ht

/-- Iterated derivatives of a `1`-periodic function are `1`-periodic. -/
theorem periodic_iteratedDeriv_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : Function.Periodic f 1) (m : ℕ) :
    Function.Periodic (iteratedDeriv m f) 1 := by
  intro t
  have h := congrFun (iteratedDeriv_comp_add_const (n := m) (f := f) (s := (1 : ℝ))) t
  rw [← h]
  congr 1
  funext x
  exact hf x

/-- Pointwise convergence from `C^∞_loc` convergence. -/
theorem tendsto_of_tendstoCInftyLocOn_aux {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : ℕ → X → Y) (g : X → Y) (U : Set X)
    (h : JHolomorphic.TendstoCInftyLocOn f g U) (x : X) (hx : x ∈ U) :
    Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
  have h0 := (h {x} (Set.singleton_subset_iff.2 hx) isCompact_singleton 0).tendsto_at
    (Set.mem_singleton x)
  have hc := ((continuousMultilinearCurryFin0 ℝ X Y).continuous.tendsto _).comp h0
  simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using hc

/-- Uniform convergence of iterated derivatives of curves from `C^∞_loc` convergence on `ℝ`. -/
theorem tendstoUniformlyOn_iteratedDeriv_aux {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℕ → ℝ → Y) (g : ℝ → Y) (h : JHolomorphic.TendstoCInftyLocOn f g Set.univ) (m : ℕ)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun k => iteratedDeriv m (f k)) (iteratedDeriv m g) atTop K := by
  have h0 := h K (Set.subset_univ _) hK m
  have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ) Y
    (fun _ => 1)).uniformContinuous.comp_tendstoUniformlyOn h0
  have e : ∀ F : ℝ → Y, iteratedDeriv m F = fun x => iteratedFDeriv ℝ m F x (fun _ => 1) :=
    fun F => funext fun x => iteratedDeriv_eq_iteratedFDeriv
  simp only [e]
  exact hc

/-- Loop actions converge under `C¹` convergence of the loops on `[0, 1]`. -/
theorem tendsto_loopAction_aux {n : ℕ} (F : ℕ → ℝ → V n) (F₀ : ℝ → V n) (hF0c : Continuous F₀)
    (hF1c : Continuous (deriv F₀)) (hFc : ∀ k, Continuous (F k) ∧ Continuous (deriv (F k)))
    (h0 : TendstoUniformlyOn F F₀ atTop (Set.Icc 0 1))
    (h1 : TendstoUniformlyOn (fun k => deriv (F k)) (deriv F₀) atTop (Set.Icc 0 1)) :
    Tendsto (fun k => ∫ t in (0 : ℝ)..1, liouville (F k t) (deriv (F k) t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, liouville (F₀ t) (deriv F₀ t))) := by
  have hl : ∀ x v : V n, liouville x v = omegaL x v / 2 := fun x v => by
    rw [omegaL_apply]; rfl
  simp_rw [hl]
  set K := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hK
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF0c.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF1c.continuousOn
  have ev0 := Metric.tendstoUniformlyOn_iff.1 h0 1 one_pos
  have ev1 := Metric.tendstoUniformlyOn_iff.1 h1 1 one_pos
  have hsub : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
    rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => K * (A + 1) * (B + 1) / 2) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun k => ?_
    exact ((omegaL.continuous₂.comp₂ (hFc k).1 (hFc k).2).div_const 2).aestronglyMeasurable
  · filter_upwards [ev0, ev1] with k hk0 hk1
    refine Eventually.of_forall fun t ht => ?_
    have htI := hsub ht
    have hx : ‖F k t‖ ≤ A + 1 := by
      have := hk0 t htI
      rw [dist_eq_norm] at this
      have h2 := norm_sub_norm_le (F k t) (F₀ t)
      rw [norm_sub_rev] at this
      linarith [hA t htI]
    have hv : ‖deriv (F k) t‖ ≤ B + 1 := by
      have := hk1 t htI
      rw [dist_eq_norm] at this
      have h2 := norm_sub_norm_le (deriv (F k) t) (deriv F₀ t)
      rw [norm_sub_rev] at this
      linarith [hB t htI]
    rw [norm_div, Real.norm_two]
    have hKn : 0 ≤ K := norm_nonneg (omegaL (n := n))
    have := (ContinuousLinearMap.le_opNorm₂ (omegaL (n := n)) (F k t) (deriv (F k) t))
    have hA1 : 0 ≤ A + 1 := by linarith [(norm_nonneg _).trans (hA 0 ⟨le_rfl, zero_le_one⟩)]
    have : K * ‖F k t‖ * ‖deriv (F k) t‖ ≤ K * (A + 1) * (B + 1) := by
      gcongr
    linarith
  · refine Eventually.of_forall fun t ht => ?_
    have htI := hsub ht
    have ha := h0.tendsto_at htI
    have hb := h1.tendsto_at htI
    exact ((omegaL.continuous₂.tendsto _).comp (ha.prodMk_nhds hb)).div_const 2

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem sacm_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → Y) (U : Set X) :
    JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => g) g U := fun K _ _ m =>
  Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by simpa using hε

theorem sacm_ccw_periodic (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem sacm_ccw_contDiff (R : ℝ) : ContDiff ℝ ∞ (ccwLoop R) := by
  unfold ccwLoop
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => ((2 * π * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact contDiff_const.mul (Complex.contDiff_exp.comp (h1.mul contDiff_const))

theorem sacm_ccw_norm (s t : ℝ) (hs : 0 < s) : ‖ccwLoop s t‖ = s := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

theorem sacm_fe_mono {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n)
    {U U' : Set ℂ} (hsub : U' ⊆ U) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) :
    IsFiniteEnergyCurve H J U' u := by
  refine ⟨hu.1.mono hsub, fun z hz => hu.2.1 z (hsub hz), fun z hz => hu.2.2.1 z (hsub hz), ?_⟩
  refine lt_of_le_of_lt ?_ hu.2.2.2
  exact iSup₂_mono fun φ _ => lintegral_mono_set hsub

/-- `C^∞` convergence of the circle loops along a sequence converging on an annulus around the
circle. -/
theorem sacm_loops {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (s : ℝ) (hs : 0 < s)
    (W : Set ℂ) (hWo : IsOpen W) (hWs : ∀ t, ccwLoop s t ∈ W)
    (Vk : ℕ → ℂ → V n) (w : ℂ → V n)
    (hV : ∀ j, ContDiffOn ℝ ∞ (Vk j) W ∧ ∀ z ∈ W, Vk j z ≠ 0)
    (hw : ContDiffOn ℝ ∞ w W) (hw0 : ∀ z ∈ W, w z ≠ 0)
    (hconv : JHolomorphic.TendstoCInftyLocOn Vk w W) :
    (∀ j, ContDiff ℝ ∞ (loopInS H (Vk j) (ccwLoop s))) ∧
      ContDiff ℝ ∞ (loopInS H w (ccwLoop s)) ∧
      ∀ m, TendstoUniformlyOn (fun j => iteratedDeriv m (loopInS H (Vk j) (ccwLoop s)))
        (iteratedDeriv m (loopInS H w (ccwLoop s))) atTop (Set.Icc 0 1) := by
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set γ : ℝ → ℂ := ccwLoop s with hγdef
  have hγ : ContDiff ℝ ∞ γ := sacm_ccw_contDiff s
  have hc1 := tendstoCInftyLocOn_comp (X := ℝ) (Y := ℂ) (Z := V n) isOpen_univ
    hWo (fun _ => γ) γ Vk w (fun _ => hγ.contDiffOn)
    hγ.contDiffOn (fun j => (hV j).1) hw (fun _ t _ => hWs t) (fun t _ => hWs t)
    (sacm_const γ _) hconv
  have hVγ : ∀ j, ContDiff ℝ ∞ (Vk j ∘ γ) := fun j => (hV j).1.comp_contDiff hγ hWs
  have hwγ : ContDiff ℝ ∞ (w ∘ γ) := hw.comp_contDiff hγ hWs
  have hc2 := tendstoCInftyLocOn_comp (X := ℝ) (Y := V n) (Z := V n) isOpen_univ
    (isOpen_ne : IsOpen {y : V n | y ≠ 0}) (fun j => Vk j ∘ γ) (w ∘ γ) (fun _ => proj H) (proj H)
    (fun j => (hVγ j).contDiffOn) hwγ.contDiffOn (fun _ => hprojs) hprojs
    (fun j t _ => (hV j).2 _ (hWs t)) (fun t _ => hw0 _ (hWs t)) hc1 (sacm_const _ _)
  refine ⟨fun j => hprojs.comp_contDiff (hVγ j) fun t => (hV j).2 _ (hWs t),
    hprojs.comp_contDiff hwγ fun t => hw0 _ (hWs t), fun m => ?_⟩
  exact tendstoUniformlyOn_iteratedDeriv_aux _ _ hc2 m _ (isCompact_Icc (a := (0 : ℝ)) (b := 1))

/-- Hryniewicz 2012, Lemma 4.11. -/
theorem exists_loop_near_reebOrbit_of_small_area_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (C e η : ℝ) (he : 0 < e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T)
    (he₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ C → Q₂.T ≤ C → Q₁.T ≠ Q₂.T → e < |Q₁.T - Q₂.T|)
    (hη : 0 < η) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∀ (R : ℝ) (u : ℂ → V n), 0 < R →
      IsFiniteEnergyCurve H J {z | R < ‖z‖} u →
      energy H {z | R < ‖z‖} u ≤ ENNReal.ofReal C →
      dlambdaEnergy H {z | R < ‖z‖} u ≤ ENNReal.ofReal e →
      (∀ ρ : ℝ, R < ρ → η ≤ loopAction H u (ccwLoop ρ)) →
      ∀ ρ : ℝ, R * Real.exp (2 * π * h) ≤ ρ →
        ∃ Q : ReebOrbit H, Q.T ≤ C ∧ ∃ c : ℝ, ∀ k ≤ m, ∀ t : ℝ,
          ‖iteratedDeriv k (loopInS H u (ccwLoop ρ)) t -
            iteratedDeriv k (fun t => Q.x (Q.T * t + c)) t‖ ≤ ε := by
  classical
  by_contra hcon
  push_neg at hcon
  have hseq := fun k : ℕ => hcon ((k : ℝ) + 1) (by positivity)
  choose R u hR0 hfe hEu hdu hau ρ hρ hfar using hseq
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  -- the radii
  set r : ℕ → ℝ := fun k => Real.exp (-(2 * π * ((k : ℝ) + 1))) with hr
  have hrpos : ∀ k, 0 < r k := fun k => Real.exp_pos _
  have hranti : Antitone r := by
    intro a b hab
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have := Real.pi_pos
    nlinarith
  have hrlim : Tendsto r atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hρpos : ∀ k, 0 < ρ k := fun k =>
    lt_of_lt_of_le (mul_pos (hR0 k) (Real.exp_pos _)) (hρ k)
  have hrρ : ∀ k, R k ≤ r k * ρ k := by
    intro k
    have h1 := hρ k
    have h2 : r k * Real.exp (2 * π * ((k : ℝ) + 1)) = 1 := by
      rw [← Real.exp_add]; simp [hr]
    calc R k = r k * (R k * Real.exp (2 * π * ((k : ℝ) + 1))) := by
          rw [mul_left_comm, h2, mul_one]
      _ ≤ r k * ρ k := mul_le_mul_of_nonneg_left h1 (hrpos k).le
  have hrlt1 : ∀ k, r k < 1 := by
    intro k
    calc r k < Real.exp 0 := Real.exp_lt_exp.2 (neg_lt_zero.2 (by positivity))
      _ = 1 := Real.exp_zero
  -- the domains
  set U : ℕ → Set ℂ := fun k => {z | r k < ‖z‖} with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => isOpen_lt continuous_const continuous_norm
  have hUm : Monotone U := fun a b hab z hz => lt_of_le_of_lt (hranti hab) hz
  have hUu : ⋃ k, U k = {z : ℂ | z ≠ 0} := by
    ext z
    simp only [hU, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk⟩
      exact norm_pos_iff.1 (lt_trans (hrpos k) hk)
    · intro hz
      exact (hrlim.eventually (gt_mem_nhds (norm_pos_iff.2 hz))).exists
  -- the rescalings
  set c : ℕ → ℝ := fun k => Real.exp (-2 * aCoord H (u k ((ρ k : ℝ) : ℂ))) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k z => c k • u k (0 + ρ k • z) with hv
  have hres := fun k => rescale_isFiniteEnergyCurve H hH J hJ {z | R k < ‖z‖}
    (isOpen_lt continuous_const continuous_norm) (u k) (hfe k) 0 (ρ k) (hρpos k) (c k) (hcpos k)
  have hnormρ : ∀ k (z : ℂ), ‖(0 : ℂ) + ρ k • z‖ = ρ k * ‖z‖ := fun k z => by
    rw [zero_add, norm_smul, Real.norm_of_nonneg (hρpos k).le]
  have hUD : ∀ k, U k ⊆ {w : ℂ | (0 : ℂ) + ρ k • w ∈ {z : ℂ | R k < ‖z‖}} := by
    intro k z hz
    show R k < ‖(0 : ℂ) + ρ k • z‖
    rw [hnormρ]
    calc R k ≤ r k * ρ k := hrρ k
      _ < ‖z‖ * ρ k := mul_lt_mul_of_pos_right hz (hρpos k)
      _ = ρ k * ‖z‖ := mul_comm _ _
  have hvfe : ∀ k, IsFiniteEnergyCurve H J (U k) (v k) := fun k =>
    sacm_fe_mono H J (hUD k) _ (hres k).1
  have hvE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C := fun k => by
    refine le_trans ?_ (((hres k).2.2.2 _ subset_rfl
      (isOpen_lt continuous_const continuous_norm).measurableSet).1.le.trans (hEu k))
    exact iSup₂_mono fun φ _ => lintegral_mono_set (hUD k)
  have hvd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e := fun k => by
    refine le_trans ?_ (((hres k).2.2.2 _ subset_rfl
      (isOpen_lt continuous_const continuous_norm).measurableSet).2.le.trans (hdu k))
    exact lintegral_mono_set (hUD k)
  have hRρ : ∀ k, R k < ρ k := fun k =>
    lt_of_le_of_lt (hrρ k) (by
      have := hrlt1 k
      have := hρpos k
      nlinarith)
  have hρ1 : ∀ k, (0 : ℂ) + ρ k • (1 : ℂ) = ((ρ k : ℝ) : ℂ) := fun k => by
    simp [Complex.real_smul]
  have ha1 : ∀ k, aCoord H (v k 1) = 0 := by
    intro k
    have h1 := (hres k).2.1 1 (by
      show R k < ‖(0 : ℂ) + ρ k • (1 : ℂ)‖
      rw [hnormρ, norm_one, mul_one]; exact hRρ k)
    simp only [hv]
    rw [h1, hρ1, hc, Real.log_exp]
    ring
  obtain ⟨φ, hφ, w, hwfe, hEw, hdw, hconv⟩ :=
    exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le H hH J hJ U hUo hUm hUu v hvfe C e hvE hvd
      he₁ ha1
  have hφt := hφ.tendsto_atTop
  -- loops of the rescalings are loops of `u`
  have hloop_eq : ∀ k (s : ℝ), 0 < s → r k < s →
      loopInS H (v k) (ccwLoop s) = loopInS H (u k) (ccwLoop (ρ k * s)) := by
    intro k s hs hrs
    funext t
    have hmem : ccwLoop s t ∈ U k := by
      show r k < ‖ccwLoop s t‖
      rw [sacm_ccw_norm s t hs]; exact hrs
    have hne : u k (0 + ρ k • ccwLoop s t) ≠ 0 := (hfe k).2.1 _ (hUD k hmem)
    simp only [loopInS, hv]
    rw [(proj_aCoord_smul_aux H hH (c k) (hcpos k) _ hne).1]
    congr 2
    simp only [ccwLoop, zero_add, Complex.real_smul]
    push_cast
    ring
  -- the common loop statement
  have hkey : ∀ s : ℝ, 0 < s → ∃ N : ℕ,
      (∀ j, r (φ (j + N)) < s) ∧
      (∀ j, ContDiff ℝ ∞ (loopInS H (v (φ (j + N))) (ccwLoop s))) ∧
      ContDiff ℝ ∞ (loopInS H w (ccwLoop s)) ∧
      ∀ m', TendstoUniformlyOn (fun j => iteratedDeriv m' (loopInS H (v (φ (j + N))) (ccwLoop s)))
        (iteratedDeriv m' (loopInS H w (ccwLoop s))) atTop (Set.Icc 0 1) := by
    intro s hs
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((hrlim.comp hφt).eventually (gt_mem_nhds (half_pos hs)))
    have hNr : ∀ j, r (φ (j + N)) < s / 2 := fun j => hN _ (Nat.le_add_left _ _)
    set W : Set ℂ := {z | s / 2 < ‖z‖} with hW
    have hWo : IsOpen W := isOpen_lt continuous_const continuous_norm
    have hWs : ∀ t, ccwLoop s t ∈ W := fun t => by
      show s / 2 < ‖ccwLoop s t‖
      rw [sacm_ccw_norm s t hs]; exact half_lt_self hs
    have hW0 : W ⊆ {z : ℂ | z ≠ 0} := fun z hz =>
      norm_pos_iff.1 (lt_trans (half_pos hs) hz)
    have hWU : ∀ j, W ⊆ U (φ (j + N)) := fun j z hz => (hNr j).trans hz
    obtain ⟨h1, h2, h3⟩ := sacm_loops H hH J hJ s hs W hWo hWs (fun j => v (φ (j + N))) w
      (fun j => ⟨(hvfe _).1.mono (hWU j), fun z hz => (hvfe _).2.1 z (hWU j hz)⟩)
      (hwfe.1.mono hW0) (fun z hz => hwfe.2.1 z (hW0 hz))
      (fun K hK hKc m' => by
        have h0 := hconv K (hK.trans hW0) hKc m'
        rw [Metric.tendstoUniformlyOn_iff] at h0 ⊢
        exact fun ε' hε' => (tendsto_add_atTop_nat N).eventually (h0 ε' hε'))
    exact ⟨N, fun j => (hNr j).trans (half_lt_self hs), h1, h2, h3⟩
  -- actions of the limit
  have hact : ∀ s : ℝ, 0 < s → η ≤ loopAction H w (ccwLoop s) := by
    intro s hs
    obtain ⟨N, hNr, hsm, hsm0, hun⟩ := hkey s hs
    have hlim := tendsto_loopAction_aux (fun j => loopInS H (v (φ (j + N))) (ccwLoop s))
      (loopInS H w (ccwLoop s)) hsm0.continuous (hsm0.continuous_deriv (by simp))
      (fun j => ⟨(hsm j).continuous, (hsm j).continuous_deriv (by simp)⟩)
      (by simpa using hun 0) (by simpa [iteratedDeriv_one] using hun 1)
    refine ge_of_tendsto hlim ?_
    -- the radius `ρ s` exceeds `R` for large indices
    filter_upwards with j
    set k := φ (j + N) with hk
    have hrs := hNr j
    have hval : loopAction H (v k) (ccwLoop s) = loopAction H (u k) (ccwLoop (ρ k * s)) := by
      simp only [loopAction, hloop_eq k s hs hrs]
    have hR' : R k < ρ k * s := by
      calc R k ≤ r k * ρ k := hrρ k
        _ < s * ρ k := mul_lt_mul_of_pos_right hrs (hρpos k)
        _ = ρ k * s := mul_comm _ _
    show η ≤ loopAction H (v k) (ccwLoop s)
    rw [hval]
    exact hau k _ hR'
  -- the limit loop
  obtain ⟨Q, hQT, c₀, hQ⟩ :=
    exists_reebOrbit_loop_of_cylinder H hH J hJ w hwfe C e η he he₂ hη hEw hdw hact
  obtain ⟨N, hNr, hsm, hsm0, hun⟩ := hkey 1 one_pos
  have hF₀ : loopInS H w (ccwLoop 1) = fun t => Q.x (Q.T * t + c₀) := funext hQ
  have hper : ∀ j, Function.Periodic (loopInS H (v (φ (j + N))) (ccwLoop 1)) 1 := fun j t => by
    simp only [loopInS]
    rw [sacm_ccw_periodic]
  have hper0 : Function.Periodic (loopInS H w (ccwLoop 1)) 1 := fun t => by
    simp only [loopInS]
    rw [sacm_ccw_periodic]
  have huniv : ∀ m', TendstoUniformly
      (fun j => iteratedDeriv m' (loopInS H (v (φ (j + N))) (ccwLoop 1)))
      (iteratedDeriv m' (loopInS H w (ccwLoop 1))) atTop := fun m' =>
    tendstoUniformly_of_periodic_aux _ _ (fun j => periodic_iteratedDeriv_aux _ (hper j) m')
      (periodic_iteratedDeriv_aux _ hper0 m') (hun m')
  have hev : ∀ᶠ j in atTop, ∀ k' ∈ Finset.range (m + 1), ∀ t : ℝ,
      dist (iteratedDeriv k' (loopInS H w (ccwLoop 1)) t)
        (iteratedDeriv k' (loopInS H (v (φ (j + N))) (ccwLoop 1)) t) < ε := by
    rw [Filter.eventually_all_finset]
    exact fun k' _ => Metric.tendstoUniformly_iff.1 (huniv k') ε hε
  obtain ⟨j, hj⟩ := hev.exists
  set k := φ (j + N) with hk
  obtain ⟨k', hk', t, ht⟩ := hfar k Q hQT c₀
  have hle := hj k' (Finset.mem_range.2 (Nat.lt_succ_of_le hk')) t
  have hl1 : loopInS H (v k) (ccwLoop 1) = loopInS H (u k) (ccwLoop (ρ k)) := by
    rw [hloop_eq k 1 one_pos (hNr j), mul_one]
  rw [hl1, hF₀, dist_comm, dist_eq_norm] at hle
  exact absurd ht (not_lt.2 hle.le)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (C e η : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate) (he : 0 < e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T)
    (he₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ C → Q₂.T ≤ C → Q₁.T ≠ Q₂.T → e < |Q₁.T - Q₂.T|)
    (hη : 0 < η) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∀ (R : ℝ) (u : ℂ → V n), 0 < R →
      IsFiniteEnergyCurve H J {z | R < ‖z‖} u →
      energy H {z | R < ‖z‖} u ≤ ENNReal.ofReal C →
      dlambdaEnergy H {z | R < ‖z‖} u ≤ ENNReal.ofReal e →
      (∀ ρ : ℝ, R < ρ → η ≤ loopAction H u (ccwLoop ρ)) →
      ∀ ρ : ℝ, R * Real.exp (2 * π * h) ≤ ρ →
        ∃ Q : ReebOrbit H, Q.T ≤ C ∧ ∃ c : ℝ, ∀ k ≤ m, ∀ t : ℝ,
          ‖iteratedDeriv k (loopInS H u (ccwLoop ρ)) t -
            iteratedDeriv k (fun t => Q.x (Q.T * t + c)) t‖ ≤ ε :=
  exists_loop_near_reebOrbit_of_small_area_aux H hH J hJ C e η he he₁ he₂ hη m ε hε
