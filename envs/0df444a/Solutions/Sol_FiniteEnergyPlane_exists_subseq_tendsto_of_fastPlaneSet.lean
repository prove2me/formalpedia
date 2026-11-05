-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendsto_of_fastPlaneSet
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T22:04:39.333241+00:00
-- url     : https://prove2.me/submissions/3429ca0c-fc8d-4c96-b92f-01f5d4846287

import Definitions.Def_FiniteEnergyPlane_Compactness
import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_loopAction_ccwLoop_eq_dlambdaEnergy
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_energy_univ_eq_dlambdaEnergy_of_plane
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_mem_fastPlaneSet
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_cylEndAt_of_gradNorm_tendsto
import Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_one_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_exists_eq_singleton_of_dlambdaEnergy_eq_zero
import Theorems.Thm_FiniteEnergyPlane_not_forall_exists_aCoord_le_of_gradNorm_bounded
import Theorems.Thm_FiniteEnergyPlane_exists_not_isCZAtLeast_three_of_windInf_le_one
import Theorems.Thm_FiniteEnergyPlane_ofReal_loopAction_ccwLoop_le_energy
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_iff_hasWindInfAt_one



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

theorem lh_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → Y) (U : Set X) :
    JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => g) g U := fun K _ _ m =>
  Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by simpa using hε

theorem lh_ccw_periodic (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem lh_ccw_contDiff (R : ℝ) : ContDiff ℝ ∞ (ccwLoop R) := by
  unfold ccwLoop
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => ((2 * π * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact contDiff_const.mul (Complex.contDiff_exp.comp (h1.mul contDiff_const))

theorem lh_ccw_norm (s t : ℝ) (hs : 0 < s) : ‖ccwLoop s t‖ = s := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

theorem lh_fe_mono {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n)
    {U U' : Set ℂ} (hsub : U' ⊆ U) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) :
    IsFiniteEnergyCurve H J U' u := by
  refine ⟨hu.1.mono hsub, fun z hz => hu.2.1 z (hsub hz), fun z hz => hu.2.2.1 z (hsub hz), ?_⟩
  refine lt_of_le_of_lt ?_ hu.2.2.2
  exact iSup₂_mono fun φ _ => lintegral_mono_set hsub

/-- `C^∞` convergence along a loop `γ` of a sequence converging on a neighbourhood of `γ`. -/
theorem lh_loops {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (γ : ℝ → ℂ)
    (hγ : ContDiff ℝ ∞ γ)
    (W : Set ℂ) (hWo : IsOpen W) (hWs : ∀ t, γ t ∈ W)
    (Vk : ℕ → ℂ → V n) (w : ℂ → V n)
    (hV : ∀ j, ContDiffOn ℝ ∞ (Vk j) W ∧ ∀ z ∈ W, Vk j z ≠ 0)
    (hw : ContDiffOn ℝ ∞ w W) (hw0 : ∀ z ∈ W, w z ≠ 0)
    (hconv : JHolomorphic.TendstoCInftyLocOn Vk w W) :
    (∀ j, ContDiff ℝ ∞ (loopInS H (Vk j) γ)) ∧
      ContDiff ℝ ∞ (loopInS H w γ) ∧
      ∀ m, TendstoUniformlyOn (fun j => iteratedDeriv m (loopInS H (Vk j) γ))
        (iteratedDeriv m (loopInS H w γ)) atTop (Set.Icc 0 1) := by
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hc1 := tendstoCInftyLocOn_comp (X := ℝ) (Y := ℂ) (Z := V n) isOpen_univ
    hWo (fun _ => γ) γ Vk w (fun _ => hγ.contDiffOn)
    hγ.contDiffOn (fun j => (hV j).1) hw (fun _ t _ => hWs t) (fun t _ => hWs t)
    (lh_const γ _) hconv
  have hVγ : ∀ j, ContDiff ℝ ∞ (Vk j ∘ γ) := fun j => (hV j).1.comp_contDiff hγ hWs
  have hwγ : ContDiff ℝ ∞ (w ∘ γ) := hw.comp_contDiff hγ hWs
  have hc2 := tendstoCInftyLocOn_comp (X := ℝ) (Y := V n) (Z := V n) isOpen_univ
    (isOpen_ne : IsOpen {y : V n | y ≠ 0}) (fun j => Vk j ∘ γ) (w ∘ γ) (fun _ => proj H) (proj H)
    (fun j => (hVγ j).contDiffOn) hwγ.contDiffOn (fun _ => hprojs) hprojs
    (fun j t _ => (hV j).2 _ (hWs t)) (fun t _ => hw0 _ (hWs t)) hc1 (lh_const _ _)
  refine ⟨fun j => hprojs.comp_contDiff (hVγ j) fun t => (hV j).2 _ (hWs t),
    hprojs.comp_contDiff hwγ fun t => hw0 _ (hWs t), fun m => ?_⟩
  exact tendstoUniformlyOn_iteratedDeriv_aux _ _ hc2 m _ (isCompact_Icc (a := (0 : ℝ)) (b := 1))

/-- Loop actions converge along a sequence converging near the loop. -/
theorem lh_tendsto_loopAction {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (γ : ℝ → ℂ)
    (hγ : ContDiff ℝ ∞ γ)
    (W : Set ℂ) (hWo : IsOpen W) (hWs : ∀ t, γ t ∈ W)
    (Vk : ℕ → ℂ → V n) (w : ℂ → V n)
    (hV : ∀ j, ContDiffOn ℝ ∞ (Vk j) W ∧ ∀ z ∈ W, Vk j z ≠ 0)
    (hw : ContDiffOn ℝ ∞ w W) (hw0 : ∀ z ∈ W, w z ≠ 0)
    (hconv : JHolomorphic.TendstoCInftyLocOn Vk w W) :
    Tendsto (fun j => loopAction H (Vk j) γ) atTop (𝓝 (loopAction H w γ)) := by
  obtain ⟨hsm, hsm0, hun⟩ := lh_loops H hH J hJ γ hγ W hWo hWs Vk w hV hw hw0 hconv
  exact tendsto_loopAction_aux (fun j => loopInS H (Vk j) γ)
      (loopInS H w γ) hsm0.continuous (hsm0.continuous_deriv (by simp))
      (fun j => ⟨(hsm j).continuous, (hsm j).continuous_deriv (by simp)⟩)
      (by simpa using hun 0) (by simpa [iteratedDeriv_one] using hun 1)

/-- Restriction of a `C^∞_loc` convergence to a smaller set. -/
theorem lh_conv_mono {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O O' : Set X}
    (h : O' ⊆ O) (hc : JHolomorphic.TendstoCInftyLocOn f g O) :
    JHolomorphic.TendstoCInftyLocOn f g O' :=
  fun K hK hKc m => hc K (hK.trans h) hKc m

/-- `C^∞_loc` convergence passes to subsequences. -/
theorem lh_conv_subseq {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    JHolomorphic.TendstoCInftyLocOn (fun k => f (φ k)) g O := fun K hK hKc m =>
  Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
    hφ.eventually (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc m) ε hε)

/-- Pointwise convergence and convergence of first derivatives. -/
theorem lh_conv_pointwise {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) {z : X} (hz : z ∈ O) :
    Tendsto (fun k => f k z) atTop (𝓝 (g z)) ∧
      Tendsto (fun k => fderiv ℝ (f k) z) atTop (𝓝 (fderiv ℝ g z)) := by
  have hsub : ({z} : Set X) ⊆ O := Set.singleton_subset_iff.2 hz
  have h0 := (hc {z} hsub isCompact_singleton 0).tendsto_at (Set.mem_singleton z)
  have h1 := (hc {z} hsub isCompact_singleton 1).tendsto_at (Set.mem_singleton z)
  constructor
  · have := (continuousMultilinearCurryFin0 ℝ X Y).continuous.tendsto _ |>.comp h0
    simpa [Function.comp_def] using this
  · have := (continuousMultilinearCurryFin1 ℝ X Y).continuous.tendsto _ |>.comp h1
    have e : ∀ F : X → Y, continuousMultilinearCurryFin1 ℝ X Y (iteratedFDeriv ℝ 1 F z) =
        fderiv ℝ F z := by
      intro F; ext v; simp [iteratedFDeriv_one_apply]
    simpa [Function.comp_def, e] using this

/-! ### Scalar multiples -/

theorem lh_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (c : ℝ) (hc : 0 < c) :
    IsFiniteEnergyCurve H J U (fun z => c • u z) ∧
      (∀ z ∈ U, proj H (c • u z) = proj H (u z)) ∧
      (∀ z ∈ U, aCoord H (c • u z) = aCoord H (u z) + Real.log c / 2) ∧
      (∀ z ∈ U, gradNorm H (fun z => c • u z) z = gradNorm H u z) ∧
      (energy H U (fun z => c • u z) = energy H U u) ∧
      dlambdaEnergy H U (fun z => c • u z) = dlambdaEnergy H U u := by
  have hres := rescale_isFiniteEnergyCurve H hH J hJ U hU u hu 0 1 one_pos c hc
  have e1 : (fun w : ℂ => (0 : ℂ) + (1 : ℝ) • w) = id := by funext w; simp
  simp only [zero_add, one_smul, Set.setOf_mem_eq] at hres
  obtain ⟨h1, h2, h3, h4⟩ := hres
  refine ⟨h1, fun z hz => (proj_aCoord_smul_aux H hH c hc _ (hu.2.1 z hz)).1, h2, ?_, ?_, ?_⟩
  · intro z hz
    have := h3 z hz
    simpa using this
  · exact (h4 U subset_rfl hU.measurableSet).1
  · exact (h4 U subset_rfl hU.measurableSet).2

/-- The loop of `c • u` is the loop of `u`. -/
theorem lh_loopInS_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (c : ℝ) (hc : 0 < c) (γ : ℝ → ℂ) (h0 : ∀ t, u (γ t) ≠ 0) :
    loopInS H (fun z => c • u z) γ = loopInS H u γ := by
  funext t
  exact (proj_aCoord_smul_aux H hH c hc _ (h0 t)).1

theorem lh_loopAction_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (c : ℝ) (hc : 0 < c) (γ : ℝ → ℂ) (h0 : ∀ t, u (γ t) ≠ 0) :
    loopAction H (fun z => c • u z) γ = loopAction H u γ := by
  simp only [loopAction, lh_loopInS_smul H hH u c hc γ h0]

/-- `C^∞_loc` convergence of `cₖ • vₖ` from convergence of `vₖ` and `cₖ`. -/
theorem lh_conv_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O : Set X}
    (hO : IsOpen O) (hf : ∀ k, ContDiffOn ℝ ∞ (f k) O) (hg : ContDiffOn ℝ ∞ g O)
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) {a : ℕ → ℝ} {a₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) :
    JHolomorphic.TendstoCInftyLocOn (fun k z => a k • f k z) (fun z => a₀ • g z) O := by
  intro K hK hKc m
  have hat : ∀ (F : X → Y), ContDiffOn ℝ ∞ F O → ∀ b : ℝ, ∀ x ∈ K,
      iteratedFDeriv ℝ m (fun z => b • F z) x = b • iteratedFDeriv ℝ m F x := by
    intro F hF b x hx
    have hFa : ContDiffAt ℝ m F x :=
      ((hF x (hK hx)).contDiffAt (hO.mem_nhds (hK hx))).of_le (by exact_mod_cast le_top)
    exact iteratedFDeriv_const_smul_apply hFa
  have hGc : ContinuousOn (iteratedFDeriv ℝ m g) K := by
    have h0 := hg.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top) hO.uniqueDiffOn
    exact (h0.congr (fun x hx => (iteratedFDerivWithin_of_isOpen m hO hx).symm)).mono hK
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hGc
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hu := Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc m)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hA : 0 < |a₀| + 1 := by positivity
  have h1 := hu (ε / (2 * (|a₀| + 1))) (by positivity)
  have h2 : ∀ᶠ k in atTop, |a k - a₀| < ε / (2 * (max B 0 + 1)) := by
    have := (Metric.tendsto_nhds.1 ha) (ε / (2 * (max B 0 + 1))) (by positivity)
    simpa [Real.dist_eq] using this
  have h3 : ∀ᶠ k in atTop, |a k - a₀| < 1 := by
    have := (Metric.tendsto_nhds.1 ha) 1 one_pos
    simpa [Real.dist_eq] using this
  filter_upwards [h1, h2, h3] with k hk1 hk2 hk3 x hx
  rw [hat _ (hf k) _ x hx, hat _ hg _ x hx, dist_eq_norm]
  have hk1' := hk1 x hx
  rw [dist_eq_norm, norm_sub_rev] at hk1'
  have hak : |a k| ≤ |a₀| + 1 := by
    have := abs_sub_abs_le_abs_sub (a k) a₀
    linarith
  have hGx : ‖iteratedFDeriv ℝ m g x‖ ≤ max B 0 + 1 := by
    have := hB x hx
    linarith [le_max_left B 0]
  have e : a₀ • iteratedFDeriv ℝ m g x - a k • iteratedFDeriv ℝ m (f k) x =
      a k • (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m (f k) x) +
        (a₀ - a k) • iteratedFDeriv ℝ m g x := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  have e1 : ‖a k • (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m (f k) x)‖ ≤ ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
    calc |a k| * ‖iteratedFDeriv ℝ m (f k) x - iteratedFDeriv ℝ m g x‖
        ≤ (|a₀| + 1) * (ε / (2 * (|a₀| + 1))) := by
          exact mul_le_mul hak hk1'.le (norm_nonneg _) hA.le
      _ = ε / 2 := by field_simp
  have e2 : ‖(a₀ - a k) • iteratedFDeriv ℝ m g x‖ < ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    have hB1 : 0 < max B 0 + 1 := by positivity
    calc |a k - a₀| * ‖iteratedFDeriv ℝ m g x‖
        ≤ |a k - a₀| * (max B 0 + 1) := mul_le_mul_of_nonneg_left hGx (abs_nonneg _)
      _ < ε / (2 * (max B 0 + 1)) * (max B 0 + 1) := mul_lt_mul_of_pos_right hk2 hB1
      _ = ε / 2 := by field_simp
  calc _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

/-- `∫_ℂ u*dλ` splits at the unit circle. -/
theorem lh_dlambda_split {n : ℕ} (H : V n → ℝ) (w : ℂ → V n) :
    dlambdaEnergy H Set.univ w =
      dlambdaEnergy H (ball 0 1) w + dlambdaEnergy H {z | 1 < ‖z‖} w := by
  have hext : MeasurableSet {z : ℂ | 1 < ‖z‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hnull : volume (sphere (0 : ℂ) 1) = 0 := Measure.addHaar_sphere _ _ _
  have hae : (Set.univ : Set ℂ) =ᵐ[volume] ((ball 0 1 ∪ {z : ℂ | 1 < ‖z‖} : Set ℂ)) := by
    have hsub : (Set.univ \ (ball (0 : ℂ) 1 ∪ {z : ℂ | 1 < ‖z‖})) ⊆ sphere (0 : ℂ) 1 := by
      intro z hz
      have h1 : ¬ ‖z‖ < 1 := fun h => hz.2 (Or.inl (mem_ball_zero_iff.2 h))
      have h2 : ¬ 1 < ‖z‖ := fun h => hz.2 (Or.inr h)
      exact mem_sphere_zero_iff_norm.2 (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
    refine (ae_eq_set.2 ⟨measure_mono_null hsub hnull, ?_⟩)
    simp
  have hdisj : Disjoint (ball (0 : ℂ) 1) {z : ℂ | 1 < ‖z‖} := by
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    have h1 := mem_ball_zero_iff.1 hz
    have h2 : 1 < ‖z‖ := hz'
    linarith
  unfold dlambdaEnergy
  rw [setLIntegral_congr hae, lintegral_union hext hdisj]

/-! ### Planes in `Θ` -/

section Theta

variable (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
  (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
  {P : ReebOrbit H} {K : Set (V 1)} {γ : ℝ} {u : ℂ → V 1}

include hH hJ in
/-- A plane in `Θ` has energy and total `dλ`-energy `P.T`. -/
theorem lh_energy (hu : u ∈ fastPlaneSet H J P K γ) :
    energy H Set.univ u = ENNReal.ofReal P.T ∧ dlambdaEnergy H Set.univ u = ENNReal.ofReal P.T := by
  obtain ⟨hf, hnd, -, -⟩ := hu
  have h1 := dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ u hf.1 P hnd
  have h2 := energy_univ_eq_dlambdaEnergy_of_plane H hH J hJ u hf.1
    (exists_ne_of_isNondegenerateEnd H u cylInf P (by norm_num) hnd)
  exact ⟨h2.trans h1, h1⟩

include hH hJ in
/-- Actions of a plane in `Θ`: at most `P.T`, at least `P.T - γ` for `ρ ≥ 1`, equal at `ρ = 1`. -/
theorem lh_action (hu : u ∈ fastPlaneSet H J P K γ) (hγ₀ : 0 < γ) (hγT : γ < P.T) :
    (∀ ρ, 0 < ρ → loopAction H u (ccwLoop ρ) ≤ P.T) ∧
      loopAction H u (ccwLoop 1) = P.T - γ ∧
      ∀ ρ, 1 ≤ ρ → P.T - γ ≤ loopAction H u (ccwLoop ρ) := by
  have htot := (lh_energy H hH J hJ hu).2
  have hfe := hu.1.1
  have hle : ∀ ρ, dlambdaEnergy H (ball 0 ρ) u ≤ ENNReal.ofReal P.T := fun ρ => by
    rw [← htot]; exact lintegral_mono_set (Set.subset_univ _)
  have hfin : ∀ ρ, dlambdaEnergy H (ball 0 ρ) u ≠ ⊤ := fun ρ =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle ρ)
  have h1 : loopAction H u (ccwLoop 1) = P.T - γ := by
    rw [loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hfe 1 one_pos]
    have hsplit := lh_dlambda_split H u
    rw [htot, hu.2.2.2] at hsplit
    have h3 : ENNReal.ofReal P.T = ENNReal.ofReal (P.T - γ) + ENNReal.ofReal γ := by
      rw [← ENNReal.ofReal_add (by linarith) hγ₀.le]
      congr 1; ring
    rw [h3] at hsplit
    have h4 := (ENNReal.add_left_inj ENNReal.ofReal_ne_top).1 hsplit
    rw [← h4, ENNReal.toReal_ofReal (by linarith)]
  refine ⟨fun ρ hρ => ?_, h1, fun ρ hρ => ?_⟩
  · rw [loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hfe ρ hρ]
    exact ENNReal.toReal_le_of_le_ofReal P.T_pos.le (hle ρ)
  · rw [← h1, loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hfe 1 one_pos,
      loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hfe ρ (by linarith)]
    exact ENNReal.toReal_mono (hfin ρ) (lintegral_mono_set (ball_subset_ball hρ))

end Theta

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A sequence of functions bounded above at a point has a subsequence whose infima converge in
`[-∞, ∞)`. -/
theorem lm_inf_subseq (a : ℕ → ℂ → ℝ) (C : ℝ) (hC : ∀ k, a k 0 ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ((∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, a (ψ k) z ≤ M) ∨
      ∃ A : ℝ, (∀ ε > 0, ∀ᶠ k in atTop, ∀ z, A - ε ≤ a (ψ k) z) ∧
        ∀ ε > 0, ∀ᶠ k in atTop, ∃ z, a (ψ k) z ≤ A + ε) := by
  obtain ⟨L, -, ψ, hψ, hL⟩ := isCompact_univ.tendsto_subseq
    (x := fun k => ⨅ z, ((a k z : ℝ) : EReal)) (fun _ => Set.mem_univ _)
  refine ⟨ψ, hψ, ?_⟩
  simp only [Function.comp_def] at hL
  induction L using EReal.rec with
  | bot =>
    left
    intro M
    filter_upwards [hL.eventually (gt_mem_nhds (EReal.bot_lt_coe M))] with k hk
    obtain ⟨z, hz⟩ := iInf_lt_iff.1 hk
    exact ⟨z, (EReal.coe_lt_coe_iff.1 hz).le⟩
  | coe A =>
    right
    refine ⟨A, fun ε hε => ?_, fun ε hε => ?_⟩
    · have h1 : ((A - ε : ℝ) : EReal) < (A : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
      filter_upwards [hL.eventually (lt_mem_nhds h1)] with k hk z
      exact (EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le hk (iInf_le _ z))).le
    · have h1 : (A : EReal) < ((A + ε : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
      filter_upwards [hL.eventually (gt_mem_nhds h1)] with k hk
      obtain ⟨z, hz⟩ := iInf_lt_iff.1 hk
      exact ⟨z, (EReal.coe_lt_coe_iff.1 hz).le⟩
  | top =>
    exfalso
    have h1 : ((C : ℝ) : EReal) < ⊤ := EReal.coe_lt_top C
    obtain ⟨k, hk⟩ := (hL.eventually (lt_mem_nhds h1)).exists
    exact absurd (lt_of_lt_of_le hk (iInf_le _ 0)) (not_lt.2 (EReal.coe_le_coe_iff.2 (hC _)))

/-- Two nondegenerate negative ends at one puncture have the same period. -/
theorem lm_end_period_unique {n : ℕ} {H : V n → ℝ} {u : ℂ → V n} {e : ℝ → ℝ → ℂ}
    {P Q : ReebOrbit H} (hP : IsNondegenerateEnd H u e P (-1))
    (hQ : IsNondegenerateEnd H u e Q (-1)) : P.T = Q.T := by
  obtain ⟨d₁, -, -, -, h₁, -⟩ := hP
  obtain ⟨d₂, -, -, -, h₂, -⟩ := hQ
  by_contra hne
  have hpos : 0 < |P.T - Q.T| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨s₁, hs₁⟩ := h₁ 1 one_pos
  obtain ⟨s₂, hs₂⟩ := h₂ 1 one_pos
  set s : ℝ := max (max s₁ s₂) ((|d₁ - d₂| + 3) / |P.T - Q.T|) with hs
  have h1 := hs₁ s (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) le_rfl) 0
  have h2 := hs₂ s (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) le_rfl) 0
  have h3 : (|d₁ - d₂| + 3) / |P.T - Q.T| ≤ s := le_max_right _ _
  rw [div_le_iff₀ hpos] at h3
  have hs0 : 0 < s := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hpos.le
    have := abs_nonneg (d₁ - d₂)
    linarith
  rw [Real.norm_eq_abs] at h1 h2
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  simp only at h1' h2'
  have hkey : |(P.T - Q.T) * s| ≤ |d₁ - d₂| + 2 := by
    have hd := le_abs_self (d₁ - d₂)
    have hd' := neg_abs_le (d₁ - d₂)
    rw [abs_le]
    constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2]
  rw [abs_mul, abs_of_pos hs0] at hkey
  linarith

/-- Positive `dλ`-energy implies positive energy. -/
theorem lm_energy_ne_zero {n : ℕ} (H : V n → ℝ) (U : Set ℂ) (u : ℂ → V n)
    (h : dlambdaEnergy H U u ≠ 0) : energy H U u ≠ 0 := by
  intro h0
  apply h
  have hadm : Admissible (fun _ : ℝ => (1 : ℝ)) :=
    ⟨contDiff_const, monotone_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩
  have hle : ∫⁻ z in U, ENNReal.ofReal (energyDensity H (fun _ => 1) u z) ≤ energy H U u :=
    le_iSup₂_of_le (fun _ : ℝ => (1 : ℝ)) hadm le_rfl
  have he : ∀ z, energyDensity H (fun _ => 1) u z = dlambdaDensity H u z := fun z => by
    simp [energyDensity, dlambdaDensity]
  simp only [he] at hle
  rw [h0] at hle
  exact le_antisymm hle bot_le

/-- The positive action near a negative puncture forces positive energy. -/
theorem lm_energy_ne_zero_of_action {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (z₁ : ℂ) (w : ℂ → V n)
    (hw : IsFiniteEnergyCurve H J {z₁}ᶜ w)
    (hneg : Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z₁) atBot) (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hact : η ≤ loopAction H w (fun t => z₁ + ccwLoop ρ t)) : energy H {z₁}ᶜ w ≠ 0 := by
  have hUo : IsOpen ({z₁}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hres := rescale_isFiniteEnergyCurve H hH J hJ {z₁}ᶜ hUo w hw z₁ 1 one_pos 1 one_pos
  simp only [one_smul] at hres
  have hset : {w : ℂ | z₁ + w ∈ ({z₁}ᶜ : Set ℂ)} = {z | z ≠ 0} := by
    ext z; simp
  rw [hset] at hres
  obtain ⟨h1, -, -, h4⟩ := hres
  have hle := ofReal_loopAction_ccwLoop_le_energy H hH J hJ (fun z => w (z₁ + z)) h1 ?_ ρ hρ
  · have hE := (h4 {z₁}ᶜ subset_rfl hUo.measurableSet).1
    rw [hset] at hE
    rw [hE] at hle
    intro h0
    rw [h0] at hle
    have : ENNReal.ofReal η ≤ 0 := le_trans (ENNReal.ofReal_le_ofReal hact) hle
    simp at this
    linarith
  · have hmap : Tendsto (fun z : ℂ => z₁ + z) (𝓝[≠] 0) (𝓝[≠] z₁) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun z : ℂ => z₁ + z) (𝓝 0) (𝓝 (z₁ + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    exact hneg.comp hmap

theorem lm_dlambda_exterior (H : V 1 → ℝ) (w : ℂ → V 1) (T γ : ℝ) (hγ : 0 < γ) (hγT : γ < T)
    (htot : dlambdaEnergy H Set.univ w = ENNReal.ofReal T)
    (hball : dlambdaEnergy H (ball 0 1) w = ENNReal.ofReal (T - γ)) :
    dlambdaEnergy H {z | 1 < ‖z‖} w = ENNReal.ofReal γ := by
  have hadd := lh_dlambda_split H w
  rw [htot, hball] at hadd
  have h3 : ENNReal.ofReal T = ENNReal.ofReal (T - γ) + ENNReal.ofReal γ := by
    rw [← ENNReal.ofReal_add (by linarith) hγ.le]
    congr 1; ring
  rw [h3] at hadd
  exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 hadd |>.symm

theorem exists_subseq_tendsto_of_fastPlaneSet_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ ∃ w : ℂ → V 1,
      IsFiniteEnergyCurve H J (↑Γ)ᶜ w ∧ energy H (↑Γ)ᶜ w ≠ 0 ∧
      energy H (↑Γ)ᶜ w ≤ ENNReal.ofReal P.T ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun k z => Real.exp (-(2 * aCoord H (u (φ k) 2))) • u (φ k) z) w (↑Γ)ᶜ ∧
      (((∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (u (φ k) z) ≤ M) ∧ Γ.card = 1 ∧
          (∀ z ∉ Γ, piDs H w z = 0) ∧ ∃ y ∈ K, proj H y ∈ Set.range P.x) ∨
        ∃ A : ℝ, (∀ ε > 0, ∀ᶠ k in atTop, ∀ z, A - ε ≤ aCoord H (u (φ k) z)) ∧
          (∀ ε > 0, ∀ᶠ k in atTop, ∃ z, aCoord H (u (φ k) z) ≤ A + ε) ∧ Γ = ∅ ∧
          ∃ c : ℝ, Tendsto (fun k => aCoord H (u (φ k) 2)) atTop (𝓝 c) ∧
            JHolomorphic.TendstoCInftyLocOn (fun k => u (φ k))
              (fun z => Real.exp (2 * c) • w z) Set.univ ∧
            (fun z => Real.exp (2 * c) • w z) ∈ fastPlaneSet H J P K γ ∧
            ∀ z, A ≤ aCoord H (Real.exp (2 * c) • w z)) := by
  classical
  have hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate := fun Q hQ => (hP Q hQ).1
  have hγT : γ < P.T := hγ₁ P le_rfl
  obtain ⟨-, hprojs, hacoord, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hacont : ContinuousOn (aCoord H) {y : V 1 | y ≠ 0} := hacoord.continuousOn
  have hpcont : ContinuousOn (proj H) {y : V 1 | y ≠ 0} := hprojs.continuousOn
  have hopen0 : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  have hKne : K ⊆ {y : V 1 | y ≠ 0} := fun y hy h0 => hK0 (h0 ▸ hy)
  -- a subsequence with `uₖ(0) → y ∈ K`
  obtain ⟨y, hyK, ψ₁, hψ₁, hy⟩ := hK.tendsto_subseq (x := fun k => u k 0) (fun k => (hu k).2.2.1)
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hacont.mono hKne)).bddAbove
  have hC' : ∀ k, aCoord H (u (ψ₁ k) 0) ≤ C := fun k =>
    hC ⟨_, (hu _).2.2.1, rfl⟩
  -- a subsequence along which the infima converge
  obtain ⟨ψ₂, hψ₂, hbranch⟩ := lm_inf_subseq (fun k z => aCoord H (u (ψ₁ k) z)) C hC'
  -- the limit
  obtain ⟨φ₃, hφ₃, Γ, hΓ, w, hw, hEw, hconv, hgrad, hblow⟩ :=
    exists_subseq_tendstoCInftyLocOn_of_mem_fastPlaneSet H hH J hJ P K γ hγ hγ₁
      (fun k => u (ψ₁ (ψ₂ k))) (fun k => hu _)
  set φ : ℕ → ℕ := fun k => ψ₁ (ψ₂ (φ₃ k)) with hφdef
  have hφ : StrictMono φ := hψ₁.comp (hψ₂.comp hφ₃)
  have hφ₃t := hφ₃.tendsto_atTop
  set v : ℕ → ℂ → V 1 := fun k => u (φ k) with hvdef
  have hv : ∀ k, v k ∈ fastPlaneSet H J P K γ := fun k => hu _
  have hv0 : Tendsto (fun k => v k 0) atTop (𝓝 y) :=
    hy.comp (hψ₂.tendsto_atTop.comp hφ₃t)
  set c : ℕ → ℝ := fun k => Real.exp (-(2 * aCoord H (v k 2))) with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  have hconv' : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • v k z) w (↑Γ)ᶜ := hconv
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  have hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (v k) := fun k => (hv k).1.1
  -- the ends
  obtain ⟨hend, hactinf⟩ := isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn H hH J hJ P hnd γ hγ
    hγ₁ hγ₂ K v hv Γ hΓ w hw hconv'
  have hneg : ∀ z ∈ Γ, ∃ Q : ReebOrbit H, Q.T ≤ P.T ∧ IsNondegenerateEnd H w (cylEndAt z) Q (-1) ∧
      Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z) atBot ∧
      ∃ r η : ℝ, 0 < r ∧ 0 < η ∧ ∀ ρ ∈ Set.Ioo 0 r,
        η ≤ loopAction H w (fun t => z + ccwLoop ρ t) := fun z hz => by
    obtain ⟨ζ, hζ, hb⟩ := hblow z hz
    exact isNondegenerateEnd_cylEndAt_of_gradNorm_tendsto H hH J hJ P.T hnd Γ w hw v hfe
      (fun k => (lh_energy H hH J hJ (hv k)).1.le) c hcpos hconv' z hz ζ hζ hb
  have hprime : P.IsPrime := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ (v 0)
    (hv 0).1 P (hv 0).2.1
  -- pointwise convergence of the shifted planes and of the shifts
  have hshift : ∀ z, z ∉ Γ → Tendsto (fun k => c k • v k z) atTop (𝓝 (w z)) := fun z hz =>
    (lh_conv_pointwise hconv' (show z ∈ ((↑Γ)ᶜ : Set ℂ) by simpa using hz)).1
  have hac : ∀ k z, aCoord H (c k • v k z) = aCoord H (v k z) - aCoord H (v k 2) := fun k z => by
    rw [(proj_aCoord_smul_aux H hH (c k) (hcpos k) _ ((hfe k).2.1 z (Set.mem_univ z))).2, hcdef,
      Real.log_exp]
    ring
  have hwne : ∀ z, z ∉ Γ → w z ≠ 0 := fun z hz => hw.2.1 z (by simpa using hz)
  have hashift : ∀ z, z ∉ Γ →
      Tendsto (fun k => aCoord H (v k z) - aCoord H (v k 2)) atTop (𝓝 (aCoord H (w z))) := by
    intro z hz
    have := (hacont.continuousAt (hopen0.mem_nhds (hwne z hz))).tendsto.comp (hshift z hz)
    simpa only [Function.comp_def, hac] using this
  have hay : Tendsto (fun k => aCoord H (v k 0)) atTop (𝓝 (aCoord H y)) :=
    (hacont.continuousAt (hopen0.mem_nhds (hKne hyK))).tendsto.comp hv0
  have ha2 : (0 : ℂ) ∉ Γ → Tendsto (fun k => aCoord H (v k 2)) atTop
      (𝓝 (aCoord H y - aCoord H (w 0))) := by
    intro h0
    have := hay.sub (hashift 0 h0)
    refine this.congr fun k => ?_
    ring
  -- the `inf` branch along `v`
  have hbranch' : (∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (v k z) ≤ M) ∨
      ∃ A : ℝ, (∀ ε > 0, ∀ᶠ k in atTop, ∀ z, A - ε ≤ aCoord H (v k z)) ∧
        ∀ ε > 0, ∀ᶠ k in atTop, ∃ z, aCoord H (v k z) ≤ A + ε := by
    rcases hbranch with hb | ⟨A, h1, h2⟩
    · exact Or.inl fun M => hφ₃t.eventually (hb M)
    · exact Or.inr ⟨A, fun ε hε => hφ₃t.eventually (h1 ε hε), fun ε hε =>
        hφ₃t.eventually (h2 ε hε)⟩
  have hact1 : (∀ t, ccwLoop 1 t ∈ ((↑Γ)ᶜ : Set ℂ)) → loopAction H w (ccwLoop 1) = P.T - γ := by
    intro hmem
    have hlim := lh_tendsto_loopAction H hH J hJ (ccwLoop 1) (lh_ccw_contDiff 1) (↑Γ)ᶜ hUo hmem
      (fun k z => c k • v k z) w
      (fun j => ⟨((lh_smul H hH J hJ Set.univ isOpen_univ (v j) (hfe j) (c j) (hcpos j)).1.1).mono
          (Set.subset_univ _), fun z _ => smul_ne_zero (hcpos j).ne' ((hfe j).2.1 z trivial)⟩)
      hw.1 hw.2.1 hconv'
    have hconst : ∀ k, loopAction H (fun z => c k • v k z) (ccwLoop 1) = P.T - γ := fun k => by
      rw [lh_loopAction_smul H hH (v k) (c k) (hcpos k) _ (fun t => (hfe k).2.1 _ trivial)]
      exact (lh_action H hH J hJ (hv k) hγ hγT).2.1
    simp only [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  refine ⟨φ, hφ, Γ, hΓ, w, hw, ?_⟩
  by_cases hd : dlambdaEnergy H (↑Γ)ᶜ w = 0
  · -- the `dλ`-energy of the limit vanishes
    obtain ⟨z₁, hΓ₁, hz, hact₁⟩ := exists_eq_singleton_of_dlambdaEnergy_eq_zero H hH J hJ Γ w hw P
      hprime hend hactinf (fun z hz => (hneg z hz).choose_spec.2.2.1) hd
    have hz₁ : z₁ ∈ Γ := by rw [hΓ₁]; exact Finset.mem_singleton_self _
    have hnorm : ‖z₁‖ ≤ 1 := hΓ z₁ hz₁
    -- the point lies on the unit circle
    have hnorm1 : ‖z₁‖ = 1 := by
      by_contra hne
      have hlt : ‖z₁‖ < 1 := lt_of_le_of_ne hnorm hne
      have h1 := hact₁ 1 hlt
      have hmem : ∀ t, ccwLoop 1 t ∈ ((↑Γ)ᶜ : Set ℂ) := fun t ht => by
        have h2 : ccwLoop 1 t = z₁ := by
          rw [hΓ₁] at ht
          simpa using ht
        have h3 := lh_ccw_norm 1 t one_pos
        rw [h2] at h3
        linarith
      have := hact1 hmem
      rw [h1] at this
      linarith
    have h0Γ : (0 : ℂ) ∉ Γ := by
      rw [hΓ₁, Finset.mem_singleton]
      rintro rfl
      simp at hnorm1
    obtain ⟨-, -, -, hnegz, r, η, hr, hη, hactz⟩ := hneg z₁ hz₁
    have hwz : IsFiniteEnergyCurve H J ({z₁}ᶜ : Set ℂ) w := by
      have : ((↑Γ)ᶜ : Set ℂ) = {z₁}ᶜ := by rw [hΓ₁]; simp
      rwa [this] at hw
    have hEne : energy H (↑Γ)ᶜ w ≠ 0 := by
      have : ((↑Γ)ᶜ : Set ℂ) = {z₁}ᶜ := by rw [hΓ₁]; simp
      rw [this]
      exact lm_energy_ne_zero_of_action H hH J hJ z₁ w hwz hnegz (r / 2) η (half_pos hr) hη
        (hactz _ ⟨half_pos hr, half_lt_self hr⟩)
    refine ⟨hEne, hEw, hconv, Or.inl ?_⟩
    rcases hbranch' with hbot | ⟨A, hA1, -⟩
    · refine ⟨hbot, by rw [hΓ₁]; simp, fun z hzΓ => (hz z hzΓ).2, y, hyK, ?_⟩
      -- the projection of `y`
      have h1 : Tendsto (fun k => proj H (v k 0)) atTop (𝓝 (proj H y)) :=
        (hpcont.continuousAt (hopen0.mem_nhds (hKne hyK))).tendsto.comp hv0
      have h2 : Tendsto (fun k => proj H (c k • v k 0)) atTop (𝓝 (proj H (w 0))) :=
        (hpcont.continuousAt (hopen0.mem_nhds (hwne 0 h0Γ))).tendsto.comp (hshift 0 h0Γ)
      have h3 : ∀ k, proj H (c k • v k 0) = proj H (v k 0) := fun k =>
        (proj_aCoord_smul_aux H hH (c k) (hcpos k) _ ((hfe k).2.1 0 trivial)).1
      simp only [h3] at h2
      rw [tendsto_nhds_unique h1 h2]
      exact (hz 0 h0Γ).1
    · -- a contradiction: near the puncture the coordinate is below `A`
      exfalso
      set c₀ : ℝ := aCoord H y - aCoord H (w 0) with hc₀
      have hev : ∀ᶠ z in 𝓝[≠] z₁, aCoord H (w z) < A - c₀ - 2 :=
        hnegz.eventually (eventually_lt_atBot _)
      obtain ⟨ζ, hζ1, hζ2⟩ := (hev.and self_mem_nhdsWithin).exists
      have hζΓ : ζ ∉ Γ := by rw [hΓ₁]; simpa using hζ2
      have hlim := (hashift ζ hζΓ).add (ha2 h0Γ)
      have hev2 : ∀ᶠ k in atTop, aCoord H (v k ζ) < A - 1 := by
        have hlt : aCoord H (w ζ) + c₀ < A - 1 := by linarith
        filter_upwards [hlim.eventually (gt_mem_nhds hlt)] with k hk
        linarith
      obtain ⟨k, hk1, hk2⟩ := (hev2.and (hA1 1 one_pos)).exists
      linarith [hk2 ζ]
  · -- the `dλ`-energy of the limit is positive
    have hwind := hasWindInfAt_one_of_tendstoCInftyLocOn H hH J hJ P K γ v hv Γ hΓ w hw hconv' hend hd
    refine ⟨lm_energy_ne_zero H _ w hd, hEw, hconv, Or.inr ?_⟩
    -- no punctures
    have hΓe : Γ = ∅ := by
      by_contra hne
      obtain ⟨z, hzΓ, Pz, -, hPz, hcz⟩ := exists_not_isCZAtLeast_three_of_windInf_le_one H hH J hJ Γ
        (Finset.nonempty_iff_ne_empty.2 hne) w hw P hend
        (fun z hz => by
          obtain ⟨Q, hQ, hQe, -⟩ := hneg z hz
          exact ⟨Q, hnd Q hQ, hQe⟩) hd 1 hwind le_rfl
      obtain ⟨Q, hQ, hQe, -⟩ := hneg z hzΓ
      have hT : Pz.T = Q.T := lm_end_period_unique hPz hQe
      exact hcz (hP Pz (hT.le.trans hQ)).2
    subst hΓe
    have hwu : IsFiniteEnergyCurve H J Set.univ w := by simpa using hw
    have h0Γ : (0 : ℂ) ∉ (∅ : Finset ℂ) := by simp
    set c₀ : ℝ := aCoord H y - aCoord H (w 0) with hc₀
    have ha2' := ha2 h0Γ
    rcases hbranch' with hbot | ⟨A, hA1, hA2⟩
    · exfalso
      exact not_forall_exists_aCoord_le_of_gradNorm_bounded H hH J hJ P γ hγ hγ₁ K hK hK0 v hv
        (fun Kc hKc => hgrad Kc (by simp) hKc) hbot
    refine ⟨A, hA1, hA2, rfl, c₀, ha2', ?_⟩
    have hconvU : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • v k z) w Set.univ := by
      simpa using hconv'
    -- the unshifted planes
    have hexp : Tendsto (fun k => Real.exp (2 * aCoord H (v k 2))) atTop (𝓝 (Real.exp (2 * c₀))) :=
      Real.continuous_exp.tendsto _ |>.comp (ha2'.const_mul 2)
    have hconvu : JHolomorphic.TendstoCInftyLocOn (fun k => v k)
        (fun z => Real.exp (2 * c₀) • w z) Set.univ := by
      have h := lh_conv_smul isOpen_univ (fun k => ((lh_smul H hH J hJ Set.univ isOpen_univ (v k) (hfe k) (c k) (hcpos k)).1.1)) hwu.1 hconvU hexp
      have e : ∀ k, (fun z => Real.exp (2 * aCoord H (v k 2)) • c k • v k z) = v k := fun k => by
        funext z
        rw [smul_smul, hcdef, ← Real.exp_add]
        simp
      rw [show (fun k z => Real.exp (2 * aCoord H (v k 2)) • c k • v k z) = v from funext e] at h
      exact h
    set ũ : ℂ → V 1 := fun z => Real.exp (2 * c₀) • w z with hũ
    obtain ⟨hũfe, hũp, hũa, -, -, hũd⟩ := lh_smul H hH J hJ Set.univ isOpen_univ w hwu
      (Real.exp (2 * c₀)) (Real.exp_pos _)
    have hlog : Real.log (Real.exp (2 * c₀)) / 2 = c₀ := by rw [Real.log_exp]; ring
    have hendW : endW H ũ cylInf = endW H w cylInf := by
      funext p; exact hũp _ trivial
    have hendA : ∀ p, endA H ũ cylInf p = endA H w cylInf p + c₀ := fun p => by
      have := hũa (cylInf p.1 p.2) trivial
      rw [hlog] at this
      exact this
    have hũend : IsNondegenerateEnd H ũ cylInf P 1 := by
      obtain ⟨d, c', b, hb, h1, h2⟩ := hend
      refine ⟨d + c₀, c', b, hb, fun ε hε => ?_, ?_⟩
      · obtain ⟨s₀, hs₀⟩ := h1 ε hε
        refine ⟨s₀, fun s hs t => ?_⟩
        have := hs₀ s hs t
        have e : endA H ũ cylInf (s, t) - 1 * P.T * s - (d + c₀) =
            endA H w cylInf (s, t) - 1 * P.T * s - d := by rw [hendA]; ring
        show ‖endA H ũ cylInf (s, t) - 1 * P.T * s - (d + c₀)‖ ≤ ε
        rw [e]
        exact this
      · rw [hendW]; exact h2
    refine ⟨hconvu, ⟨?_, hũend, ?_, ?_⟩, ?_⟩
    · -- fast
      refine (isFastPlane_iff_hasWindInfAt_one H hH J hJ ũ hũfe P hprime hũend).2 ?_
      unfold HasWindInfAt
      rw [hendW]
      exact hwind
    · -- the value at `0`
      have h1 := (lh_conv_pointwise hconvu (Set.mem_univ (0 : ℂ))).1
      rw [← tendsto_nhds_unique hv0 h1]
      exact hyK
    · -- the exterior `dλ`-energy
      have hext := (lh_smul H hH J hJ {z | 1 < ‖z‖} (isOpen_lt continuous_const continuous_norm) w
        (lh_fe_mono H J (Set.subset_univ _) w hwu) (Real.exp (2 * c₀)) (Real.exp_pos _)).2.2.2.2.2
      rw [hext]
      have htot := dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ w hwu P hend
      refine lm_dlambda_exterior H w P.T γ hγ hγT htot ?_
      have h1 := hact1 (by simp)
      rw [loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ w hwu 1 one_pos] at h1
      have hfin : dlambdaEnergy H (ball 0 1) w ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := ENNReal.ofReal P.T) ENNReal.ofReal_ne_top ?_
        rw [← htot]
        exact lintegral_mono_set (Set.subset_univ _)
      rw [← h1, ENNReal.ofReal_toReal hfin]
    · -- the lower bound on the coordinate
      intro z
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have h1 := (lh_conv_pointwise hconvu (Set.mem_univ z)).1
      have h2 := (hacont.continuousAt (hopen0.mem_nhds (hũfe.2.1 z trivial))).tendsto.comp h1
      have h3 : A - ε ≤ aCoord H (ũ z) :=
        ge_of_tendsto h2 ((hA1 ε hε).mono fun k hk => hk z)
      linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ ∃ w : ℂ → V 1,
      IsFiniteEnergyCurve H J (↑Γ)ᶜ w ∧ energy H (↑Γ)ᶜ w ≠ 0 ∧
      energy H (↑Γ)ᶜ w ≤ ENNReal.ofReal P.T ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun k z => Real.exp (-(2 * aCoord H (u (φ k) 2))) • u (φ k) z) w (↑Γ)ᶜ ∧
      (((∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (u (φ k) z) ≤ M) ∧ Γ.card = 1 ∧
          (∀ z ∉ Γ, piDs H w z = 0) ∧ ∃ y ∈ K, proj H y ∈ Set.range P.x) ∨
        ∃ A : ℝ, (∀ ε > 0, ∀ᶠ k in atTop, ∀ z, A - ε ≤ aCoord H (u (φ k) z)) ∧
          (∀ ε > 0, ∀ᶠ k in atTop, ∃ z, aCoord H (u (φ k) z) ≤ A + ε) ∧ Γ = ∅ ∧
          ∃ c : ℝ, Tendsto (fun k => aCoord H (u (φ k) 2)) atTop (𝓝 c) ∧
            JHolomorphic.TendstoCInftyLocOn (fun k => u (φ k))
              (fun z => Real.exp (2 * c) • w z) Set.univ ∧
            (fun z => Real.exp (2 * c) • w z) ∈ fastPlaneSet H J P K γ ∧
            ∀ z, A ≤ aCoord H (Real.exp (2 * c) • w z)) :=
  exists_subseq_tendsto_of_fastPlaneSet_aux H hH J hJ P hP γ hγ hγ₁ hγ₂ K hK hK0 u hu
