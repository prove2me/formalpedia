-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T21:21:03.992205+00:00
-- url     : https://prove2.me/submissions/9fb2d7ac-da0e-4089-b757-35c1b0348f6f

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
import Theorems.Thm_FiniteEnergyPlane_isAsymptoticallyCylindricalEnd_of_isNondegenerate
import Theorems.Thm_FiniteEnergyPlane_hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd
import Theorems.Thm_FiniteEnergyPlane_exists_loop_near_orbit_of_mem_fastPlaneSet
import Theorems.Thm_FiniteEnergyPlane_punctured_disk_asymptotics
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv_exterior
import Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_isRemovablePuncture
import Theorems.Thm_FiniteEnergyPlane_exists_phase_eq_of_forall_close_shift
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



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

theorem la_inv_cylEnd (s t : ℝ) : (cylEnd s t)⁻¹ = cylInf s t := by
  unfold cylEnd cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.exp_neg, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg,
    neg_mul, neg_neg]

theorem la_inv_cwLoop (R : ℝ) (hR : 0 < R) (t : ℝ) : (cwLoop 0 R⁻¹ t)⁻¹ = ccwLoop R t := by
  unfold cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.exp_neg, Complex.ofReal_inv, inv_inv, neg_mul, neg_neg]

theorem la_eventually_le (C b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, C * Real.exp (-(b * s)) ≤ ε := by
  have h : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => -(b * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hb)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp (h.eventually (ge_mem_nhds hε))
  exact ⟨s₀, hs₀⟩

theorem la_isNondegenerateEnd_of_hasExp {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε b : ℝ) (hb : 0 < b)
    (h : HasExpAsymptoticsEnd H u e P ε b) : IsNondegenerateEnd H u e P ε := by
  obtain ⟨d, c, ⟨-, ha⟩, ⟨-, hw⟩⟩ := h
  obtain ⟨Ca, sa, hCa⟩ := ha 0
  obtain ⟨Cw, sw, hCw⟩ := hw 0
  refine ⟨d, c, b / 2, by positivity, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨s₀, hs₀⟩ := la_eventually_le Ca b δ hb hδ
    refine ⟨max s₀ sa, fun s hs t => ?_⟩
    have := hCa s (le_trans (le_max_right _ _) hs) t
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (hs₀ s (le_trans (le_max_left _ _) hs))
  · intro δ hδ
    obtain ⟨s₀, hs₀⟩ := la_eventually_le Cw (b / 2) δ (by positivity) hδ
    refine ⟨max s₀ sw, fun s hs t => ?_⟩
    have := hCw s (le_trans (le_max_right _ _) hs) t
    rw [norm_iteratedFDeriv_zero] at this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (b / 2 * s) * ‖endW H u e (s, t) - P.x (ε * P.T * t + c)‖
        ≤ Real.exp (b / 2 * s) * (Cw * Real.exp (-(b * s))) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = Cw * Real.exp (-(b / 2 * s)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      _ ≤ δ := hs₀ s (le_trans (le_max_left _ _) hs)

/-- A loop limit over a nondegenerate orbit gives a nondegenerate end. -/
theorem la_isNondegenerateEnd_of_loops {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (c : ℝ) (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    IsNondegenerateEnd H u cylEnd P σ := by
  have hac := isAsymptoticallyCylindricalEnd_of_isNondegenerate H hH J hJ u hu P hP σ hσ ρ hρ hρ0 c
    hconv
  obtain ⟨b, hb, hexp⟩ := hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd H hH J hJ u hu P hP
    σ hσ hac
  exact la_isNondegenerateEnd_of_hasExp H u cylEnd P σ b hb hexp

/-- `ρ₀ • ` periodic loops: uniform convergence on `[0, 1]` is uniform on `ℝ`. -/
theorem la_loop_periodic {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (z₀ : ℂ) (ρ : ℝ) :
    Function.Periodic (loopInS H u (fun t => z₀ + ccwLoop ρ t)) 1 := by
  intro t
  simp only [loopInS, lh_ccw_periodic ρ t]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (Γ : Finset ℂ) (hΓ : ∀ z ∈ Γ, ‖z‖ ≤ 1) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (hconv : JHolomorphic.TendstoCInftyLocOn
      (fun k z => Real.exp (-(2 * aCoord H (u k 2))) • u k z) w (↑Γ)ᶜ) :
    IsNondegenerateEnd H w cylInf P 1 ∧
      Tendsto (fun ρ : ℝ => loopAction H w (ccwLoop ρ)) atTop (𝓝 P.T) := by
  classical
  have hγT : γ < P.T := hγ₁ P le_rfl
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  have hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k) := fun k => (hu k).1.1
  set c : ℕ → ℝ := fun k => Real.exp (-(2 * aCoord H (u k 2))) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  have hV : ∀ j, ContDiffOn ℝ ∞ (fun z => c j • u j z) (↑Γ)ᶜ ∧
      ∀ z ∈ ((↑Γ)ᶜ : Set ℂ), c j • u j z ≠ 0 := fun j =>
    ⟨((lh_smul H hH J hJ Set.univ isOpen_univ (u j) (hfe j) (c j) (hcpos j)).1.1).mono
        (Set.subset_univ _), fun z _ => smul_ne_zero (hcpos j).ne' ((hfe j).2.1 z trivial)⟩
  have hmem : ∀ ρ : ℝ, 1 < ρ → ∀ t, ccwLoop ρ t ∈ ((↑Γ)ᶜ : Set ℂ) := fun ρ hρ t ht => by
    have h1 := hΓ _ (Finset.mem_coe.1 ht)
    rw [lh_ccw_norm ρ t (by linarith)] at h1
    linarith
  -- actions of the limit
  have hactu : ∀ ρ : ℝ, 1 < ρ → ∀ k, loopAction H (fun z => c k • u k z) (ccwLoop ρ) =
      loopAction H (u k) (ccwLoop ρ) := fun ρ _ k =>
    lh_loopAction_smul H hH (u k) (c k) (hcpos k) _ (fun t => (hfe k).2.1 _ trivial)
  have hactlim : ∀ ρ : ℝ, 1 < ρ → Tendsto (fun k => loopAction H (u k) (ccwLoop ρ)) atTop
      (𝓝 (loopAction H w (ccwLoop ρ))) := fun ρ hρ => by
    have := lh_tendsto_loopAction H hH J hJ (ccwLoop ρ) (lh_ccw_contDiff ρ) (↑Γ)ᶜ hUo (hmem ρ hρ)
      (fun k z => c k • u k z) w hV hw.1 hw.2.1 hconv
    simpa only [hactu ρ hρ] using this
  have hactw : ∀ ρ : ℝ, 1 < ρ → P.T - γ ≤ loopAction H w (ccwLoop ρ) ∧
      loopAction H w (ccwLoop ρ) ≤ P.T := fun ρ hρ =>
    ⟨ge_of_tendsto' (hactlim ρ hρ) fun k => (lh_action H hH J hJ (hu k) hγ hγT).2.2 ρ hρ.le,
      le_of_tendsto' (hactlim ρ hρ) fun k => (lh_action H hH J hJ (hu k) hγ hγT).1 ρ (by linarith)⟩
  -- inversion
  have hsubext : {z : ℂ | 1 < ‖z‖} ⊆ ((↑Γ)ᶜ : Set ℂ) := fun z hz hzΓ => by
    have h1 := hΓ z (Finset.mem_coe.1 hzΓ)
    have h2 : 1 < ‖z‖ := hz
    linarith
  have hwext : IsFiniteEnergyCurve H J {z | 1 < ‖z‖} w := lh_fe_mono H J hsubext w hw
  obtain ⟨hwi, -⟩ := isFiniteEnergyCurve_comp_inv_exterior H hH J hJ 1 1 one_pos (by norm_num) w hwext
  set wi : ℂ → V 1 := fun z => w z⁻¹ with hwidef
  have hloopinv : ∀ R : ℝ, 0 < R → loopInS H wi (cwLoop 0 R⁻¹) = loopInS H w (ccwLoop R) := by
    intro R hR
    funext t
    simp only [loopInS, hwidef, la_inv_cwLoop R hR]
  have hactinv : ∀ ρ : ℝ, 0 < ρ → loopAction H wi (cwLoop 0 ρ) = loopAction H w (ccwLoop ρ⁻¹) := by
    intro ρ hρ
    simp only [loopAction]
    rw [← hloopinv ρ⁻¹ (inv_pos.2 hρ), inv_inv]
  have hTγ : 0 < P.T - γ := by linarith
  have hev01 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ 1 < ρ⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ρ hρ
    exact ⟨hρ.1, (one_lt_inv₀ hρ.1).2 hρ.2⟩
  have hge : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), P.T - γ ≤ loopAction H wi (cwLoop 0 ρ) ∧
      loopAction H wi (cwLoop 0 ρ) ≤ P.T := by
    filter_upwards [hev01] with ρ hρ
    rw [hactinv ρ hρ.1]
    exact hactw _ hρ.2
  rcases punctured_disk_asymptotics H hH J hJ wi hwi with hrem | ⟨Q₀, -, hQ₀, -, -, hseq⟩
  · exfalso
    have h0 := tendsto_loopAction_of_isRemovablePuncture H hH J hJ wi hrem
    have := ge_of_tendsto h0 (hge.mono fun _ h => h.1)
    linarith
  have hQ₀ge : P.T - γ ≤ Q₀ := ge_of_tendsto hQ₀ (hge.mono fun _ h => h.1)
  have hQ₀le : Q₀ ≤ P.T := le_of_tendsto hQ₀ (hge.mono fun _ h => h.2)
  have hQ₀pos : 0 < Q₀ := by linarith
  -- the radii
  set ρs : ℕ → ℝ := fun k => ((k : ℝ) + 2)⁻¹ with hρs
  have hρspos : ∀ k, 0 < ρs k := fun k => inv_pos.2 (by positivity)
  have hρslim : Tendsto ρs atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨φ, hφ, P₁, hP₁T, c₁, hc₁⟩ := hseq ρs hρspos hρslim
  have hφt := hφ.tendsto_atTop
  have hP₁T' : P₁.T = Q₀ := by rw [hP₁T, abs_of_pos hQ₀pos]
  have hP₁nd : P₁.IsNondegenerate := hnd P₁ (by linarith)
  have hρ' : ∀ k, 0 < ρs (φ k) := fun k => hρspos _
  have hρ'0 : Tendsto (fun k => ρs (φ k)) atTop (𝓝 0) := hρslim.comp hφt
  have hend₁ : IsNondegenerateEnd H wi cylEnd P₁ 1 := by
    refine la_isNondegenerateEnd_of_loops H hH J hJ wi hwi P₁ hP₁nd 1 (Or.inl rfl) _ hρ' hρ'0 c₁ ?_
    simpa only [one_mul, hP₁T'] using hc₁
  have hendAeq : endA H wi cylEnd = endA H w cylInf := by
    funext p; simp only [endA, hwidef, la_inv_cylEnd]
  have hendWeq : endW H wi cylEnd = endW H w cylInf := by
    funext p; simp only [endW, hwidef, la_inv_cylEnd]
  -- the loop limit is a loop of `P`
  set R : ℕ → ℝ := fun j => (ρs (φ j))⁻¹ with hR
  have hRlim : Tendsto R atTop atTop := by
    have h1 : Tendsto (fun j => (φ j : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hφt)
    simpa only [hR, hρs, inv_inv] using h1
  have hloopR : ∀ j, loopInS H wi (cwLoop 0 (ρs (φ j))) = loopInS H w (ccwLoop (R j)) := by
    intro j
    rw [← hloopinv (R j) (inv_pos.2 (hρ' j))]
    simp only [hR, inv_inv]
  have hf : ∀ t, Tendsto (fun j => loopInS H w (ccwLoop (R j)) t) atTop (𝓝 (P₁.x (Q₀ * t + c₁))) := by
    intro t
    have := (hc₁ 0).tendsto_at t
    simp only [iteratedDeriv_zero] at this
    simpa only [hloopR] using this
  have hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H w (ccwLoop (R j)) t - P.x (P.T * t + c')‖ ≤ ε := by
    intro ε hε
    obtain ⟨ρ₀, hρ₀, hnear⟩ := exists_loop_near_orbit_of_mem_fastPlaneSet H hH J hJ P hnd γ hγ hγ₁
      hγ₂ K (ε / 2) (half_pos hε)
    filter_upwards [hRlim.eventually (eventually_gt_atTop (max ρ₀ 1))] with j hj
    have hR1 : 1 < R j := lt_of_le_of_lt (le_max_right _ _) hj
    have hRρ : ρ₀ ≤ R j := (le_max_left _ _).trans hj.le
    obtain ⟨-, -, hun⟩ := lh_loops H hH J hJ (ccwLoop (R j)) (lh_ccw_contDiff _) (↑Γ)ᶜ hUo
      (hmem _ hR1) (fun k z => c k • u k z) w hV hw.1 hw.2.1 hconv
    have hun0 := hun 0
    simp only [iteratedDeriv_zero] at hun0
    have hper : ∀ F : ℂ → V 1, Function.Periodic (loopInS H F (ccwLoop (R j))) 1 := fun F t => by
      simp only [loopInS, lh_ccw_periodic (R j) t]
    have huni := tendstoUniformly_of_periodic_aux _ _ (fun k => hper _) (hper w) hun0
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformly_iff.1 huni (ε / 2) (half_pos hε)).exists
    obtain ⟨c', hc'⟩ := hnear (u k) (hu k) (R j) hRρ
    refine ⟨c', fun t => ?_⟩
    have h1 := hk t
    rw [dist_eq_norm] at h1
    have h2 := hc' t
    have h3 : loopInS H (fun z => c k • u k z) (ccwLoop (R j)) t = loopInS H (u k) (ccwLoop (R j)) t :=
      congrFun (lh_loopInS_smul H hH (u k) (c k) (hcpos k) _ (fun t => (hfe k).2.1 _ trivial)) t
    rw [h3] at h1
    calc ‖loopInS H w (ccwLoop (R j)) t - P.x (P.T * t + c')‖
        ≤ ‖loopInS H w (ccwLoop (R j)) t - loopInS H (u k) (ccwLoop (R j)) t‖ +
          ‖loopInS H (u k) (ccwLoop (R j)) t - P.x (P.T * t + c')‖ := by
          refine (norm_add_le _ _).trans_eq' ?_
          congr 1
          abel
      _ ≤ ε := by linarith
  have hPc : Continuous P.x := (ReebOrbit.contDiff_x H hH P).continuous
  obtain ⟨c₂, hc₂⟩ := exists_phase_eq_of_forall_close_shift P.T_pos hPc (fun τ => P.periodic τ) P.T
    (fun j => loopInS H w (ccwLoop (R j))) (fun t => P₁.x (Q₀ * t + c₁)) hf hclose
  -- equality of the periods
  have hQT : Q₀ = P.T := by
    have hP₁c : ∀ τ, HasDerivAt P₁.x (reeb H (P₁.x τ)) τ := P₁.hasDerivAt
    have hd1 : HasDerivAt (fun t : ℝ => P₁.x (Q₀ * t + c₁)) (Q₀ • reeb H (P₁.x (Q₀ * 0 + c₁))) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => Q₀ * t + c₁) Q₀ 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul Q₀).add_const c₁
      exact (P₁.hasDerivAt _).scomp 0 h1
    have hd2 : HasDerivAt (fun t : ℝ => P.x (P.T * t + c₂)) (P.T • reeb H (P.x (P.T * 0 + c₂))) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => P.T * t + c₂) P.T 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul P.T).add_const c₂
      exact (P.hasDerivAt _).scomp 0 h1
    have heq : (fun t : ℝ => P₁.x (Q₀ * t + c₁)) = fun t => P.x (P.T * t + c₂) := funext hc₂
    rw [heq] at hd1
    have hv := hd1.unique hd2
    have hpt := hc₂ 0
    rw [hpt] at hv
    have hsp := (reeb_spec H hH _ (P.mem (P.T * 0 + c₂))).2.1
    have hR0 : reeb H (P.x (P.T * 0 + c₂)) ≠ 0 := by
      intro h0
      rw [h0] at hsp
      simp [liouville, omega0, dot] at hsp
    exact smul_left_injective ℝ hR0 hv
  have hP₁TT : P₁.T = P.T := hP₁T'.trans hQT
  refine ⟨?_, ?_⟩
  · obtain ⟨d, c₃, b, hb, h1, h2⟩ := hend₁
    refine ⟨d, c₃ - c₁ + c₂, b, hb, ?_, ?_⟩
    · simpa only [hendAeq, hP₁TT] using h1
    · intro ε hε
      obtain ⟨s₀, hs₀⟩ := h2 ε hε
      refine ⟨s₀, fun s hs t => ?_⟩
      have h3 := hs₀ s hs t
      simp only [hendWeq] at h3 ⊢
      have e : P₁.x (1 * P₁.T * t + c₃) = P.x (1 * P.T * t + (c₃ - c₁ + c₂)) := by
        have := hc₂ (t + (c₃ - c₁) / P.T)
        rw [hQT] at this
        rw [hP₁TT, one_mul, show P.T * t + c₃ = P.T * (t + (c₃ - c₁) / P.T) + c₁ by
          field_simp [P.T_pos.ne']; ring, this]
        congr 1
        field_simp [P.T_pos.ne']
        ring
      rw [e] at h3
      exact h3
  · rw [← hQT]
    have hinv : Tendsto (fun ρ : ℝ => ρ⁻¹) atTop (𝓝[>] 0) := tendsto_inv_atTop_nhdsGT_zero
    have := hQ₀.comp hinv
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    simp only [Function.comp_def]
    rw [hactinv _ (inv_pos.2 hρ), inv_inv]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (Γ : Finset ℂ) (hΓ : ∀ z ∈ Γ, ‖z‖ ≤ 1) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (hconv : JHolomorphic.TendstoCInftyLocOn
      (fun k z => Real.exp (-(2 * aCoord H (u k 2))) • u k z) w (↑Γ)ᶜ) :
    IsNondegenerateEnd H w cylInf P 1 ∧
      Tendsto (fun ρ : ℝ => loopAction H w (ccwLoop ρ)) atTop (𝓝 P.T) :=
  isNondegenerateEnd_cylInf_of_tendstoCInftyLocOn_aux H hH J hJ P hnd γ hγ hγ₁ hγ₂ K u hu Γ hΓ w hw hconv
