-- Prove2me | solution 1 for FiniteEnergyPlane.exists_eq_singleton_of_dlambdaEnergy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T21:35:37.509209+00:00
-- url     : https://prove2.me/submissions/be146a43-6874-4fcc-87e3-0155e340dc4e

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
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_comp_polynomial
import Theorems.Thm_FiniteEnergyPlane_loopAction_le_and_dlambdaEnergy_annulus_eq
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos



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

/-! Stokes helpers on an annulus inside an open set: copied from fizzyinc3's accepted solution
f12a0a9a (namespace FEPA3, renamed ZCS). -/

namespace ZCS

open FiniteEnergyPlane
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


/-- The boundary term of a map `w` on the circle of radius `r`. -/
noncomputable def bdryTerm {n : ℕ} (w : ℂ → V n) (r : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
    omegaL (w (circleMap 0 r θ)) (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))

theorem continuousOn_dens {n : ℕ} (w : ℂ → V n) {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) :
    ContinuousOn (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) U := by
  have hd : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU (by simp)
  simp_rw [← omegaL_apply]
  exact ((omegaL.continuous.comp_continuousOn (hd.clm_apply continuousOn_const)).clm_apply
    (hd.clm_apply continuousOn_const))

/-- Stokes on an annulus inside an open set. -/
theorem annulus_eq {n : ℕ} (w : ℂ → V n) {U : Set ℂ} (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) :
    ∫ z in ball 0 b \ ball 0 a, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      bdryTerm w b - bdryTerm w a := by
  have hc : ContinuousOn (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I))
      (closedBall 0 b \ ball 0 a) := by
    refine (continuousOn_dens w hU hw).mono ?_
    intro z hz
    refine hsub z ?_ ?_
    · simpa using hz.2
    · simpa using hz.1
  rw [setIntegral_annulus_eq_integral_circleMap ha hab hc]
  have hS := integral_mul_integral_bilin_circleMap_eq (omegaL (n := n))
    (fun x y => by rw [omegaL_apply, omegaL_apply, omega0_antisymm]) hU
    (hw.of_le (WithTop.coe_le_coe.2 le_top)) ha hab hsub 0
  simp only [sub_zero, omegaL_apply] at hS
  simp only [smul_eq_mul, bdryTerm, omegaL_apply]
  exact hS

/-- The action of the clockwise loop is minus the boundary term. -/
theorem loopAction_cw_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ (fun z => proj H (u z)) U) (ρ : ℝ) (hρ : ∀ θ, circleMap 0 ρ θ ∈ U) :
    loopAction H u (cwLoop 0 ρ) = -bdryTerm (fun z => proj H (u z)) ρ := by
  set w := fun z => proj H (u z) with hwdef
  have hcm : ∀ t : ℝ, cwLoop 0 ρ t = circleMap 0 ρ (-(2 * π) * t) := by
    intro t; simp [cwLoop, circleMap]
  have hloop : loopInS H u (cwLoop 0 ρ) = fun t => w (circleMap 0 ρ (-(2 * π) * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hder : ∀ t : ℝ, deriv (loopInS H u (cwLoop 0 ρ)) t =
      (-(2 * π)) • fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))
        (circleMap 0 ρ (-(2 * π) * t) * Complex.I) := by
    intro t
    rw [hloop]
    have hh : HasDerivAt (fun t : ℝ => -(2 * π) * t) (-(2 * π)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(2 * π))
    have h1 := (hasDerivAt_circleMap 0 ρ (-(2 * π) * t)).scomp t hh
    have h2 : HasFDerivAt w (fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))) (circleMap 0 ρ (-(2 * π) * t)) :=
      ((hw.contDiffAt (hU.mem_nhds (hρ _))).differentiableAt (by simp)).hasFDerivAt
    have := h2.comp_hasDerivAt t h1
    rw [show (fun t => w (circleMap 0 ρ (-(2 * π) * t))) =
      w ∘ (circleMap 0 ρ ∘ fun t => -(2 * π) * t) from rfl, this.deriv, ← map_smul]
  set f : ℝ → ℝ := fun θ => omegaL (w (circleMap 0 ρ θ))
      (fderiv ℝ w (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) with hfdef
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hfdef, periodic_circleMap 0 ρ θ]
  unfold loopAction
  simp_rw [hder, hloop]
  simp only [liouville, map_smul, smul_eq_mul]
  have e : ∀ t : ℝ, omega0 (w (circleMap 0 ρ (-(2 * π) * t)))
      ((-(2 * π)) • fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))
        (circleMap 0 ρ (-(2 * π) * t) * Complex.I)) / 2 = (-π) * f (-(2 * π) * t) := by
    intro t
    simp only [hfdef, ← omegaL_apply, map_smul, smul_eq_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f (by have := Real.pi_pos; intro h; linarith : (-(2 * π) : ℝ) ≠ 0),
    mul_one, mul_zero, intervalIntegral.integral_symm]
  have hp := hper.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [mul_zero, mul_one, neg_add_cancel, zero_add] at hp
  rw [hp, bdryTerm, smul_eq_mul]
  field_simp
  ring

end ZCS

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Polynomial
open scoped ContDiff ENNReal Real

theorem ld_cyl (ρ : ℝ) (hρ : 0 < ρ) (t : ℝ) :
    cylInf (Real.log ρ / (2 * π)) t = ccwLoop ρ t := by
  simp only [cylInf]
  rw [mul_div_cancel₀ _ (by positivity), Real.exp_log hρ]

theorem ld_x_congr {n : ℕ} {H : V n → ℝ} (Q : ReebOrbit H) {θ ψ : ℝ}
    (h : (θ : Real.Angle) = ψ) : Q.x (Q.T * θ / (2 * π)) = Q.x (Q.T * ψ / (2 * π)) := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  have hper : Function.Periodic Q.x Q.T := fun τ => Q.periodic τ
  have e : Q.T * θ / (2 * π) = Q.T * ψ / (2 * π) + k * Q.T := by
    have hθ : θ = ψ + 2 * π * k := by linarith
    rw [hθ]
    field_simp
  rw [e]
  exact hper.int_mul k _

/-- The direction function of a trivial cylinder. -/
noncomputable def ldG {n : ℕ} {H : V n → ℝ} (Q : ReebOrbit H) (w : ℂ) : V n :=
  Q.x (Q.T * Complex.arg w / (2 * π))

theorem ldG_smul {n : ℕ} {H : V n → ℝ} (Q : ReebOrbit H) (r : ℝ) (hr : 0 < r) (w : ℂ) :
    ldG Q ((r : ℂ) * w) = ldG Q w := by
  unfold ldG
  rw [Complex.arg_real_mul _ hr]

theorem ldG_continuousAt {n : ℕ} {H : V n → ℝ} (Q : ReebOrbit H) (w₀ : ℂ) (h : w₀ ≠ 0) :
    ContinuousAt (ldG Q) w₀ := by
  have hcx : Continuous Q.x := continuous_iff_continuousAt.2 fun τ => (Q.hasDerivAt τ).continuousAt
  have h1 : ContinuousAt (fun w : ℂ => w / w₀) w₀ := by fun_prop
  have h2 : ContinuousAt Complex.arg (w₀ / w₀) :=
    Complex.continuousAt_arg (by rw [div_self h]; exact Complex.one_mem_slitPlane)
  have h3 : ContinuousAt (fun w : ℂ => Complex.arg (w / w₀)) w₀ :=
    ContinuousAt.comp (g := Complex.arg) h2 h1
  have h4 : ContinuousAt
      (fun w : ℂ => Q.x (Q.T * (Complex.arg (w / w₀) + Complex.arg w₀) / (2 * π))) w₀ :=
    ContinuousAt.comp (g := Q.x) hcx.continuousAt
      (((h3.add continuousAt_const).const_mul Q.T).div_const _)
  refine h4.congr ?_
  filter_upwards [isOpen_ne.mem_nhds h] with w hw
  unfold ldG
  apply ld_x_congr
  rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle (div_ne_zero hw h) h, div_mul_cancel₀ _ h]

theorem ld_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Q : ReebOrbit H) (w : ℂ)
    (hw : w ≠ 0) : proj H (trivialCylinder Q w) = ldG Q w := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hr : 0 < ‖w‖ ^ (Q.T / π) := Real.rpow_pos_of_pos hwn _
  have hS : H (Q.x (Q.T * Complex.arg w / (2 * π))) = 1 := Q.mem _
  have hx0 : Q.x (Q.T * Complex.arg w / (2 * π)) ≠ 0 := by
    intro h0
    rw [h0] at hS
    have := hH.2.2 0 hS
    simp at this
  obtain ⟨hp, -⟩ := proj_aCoord_smul_aux H hH _ hr _ hx0
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 _ hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • Q.x (Q.T * Complex.arg w / (2 * π))) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H (Q.x (Q.T * Complex.arg w / (2 * π))) = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have h2 := hru _ (Classical.choose_spec e1)
    have h3 := hru 1 ⟨one_pos, by rw [one_smul]; exact hS⟩
    rw [h2, h3]
  unfold trivialCylinder ldG
  rw [hp]
  unfold proj
  rw [h1, one_smul]

theorem ld_close {n : ℕ} (H : V n → ℝ) (w : ℂ → V n) (P : ReebOrbit H) (c b : ℝ) (hb : 0 < b)
    (hW : TendstoZeroUnif (fun p : ℝ × ℝ =>
      Real.exp (b * p.1) • (endW H w cylInf p - P.x ((1 : ℝ) * P.T * p.2 + c)))) (t : ℝ) :
    Tendsto (fun R : ℝ => proj H (w (ccwLoop R t))) atTop (𝓝 (P.x (P.T * t + c))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s₀, hs₀⟩ := hW (ε / 2) (half_pos hε)
  refine ⟨Real.exp (2 * π * max s₀ 0), fun R hR => ?_⟩
  have hRpos : 0 < R := (Real.exp_pos _).trans_le hR
  set s := Real.log R / (2 * π) with hs
  have hsge : max s₀ 0 ≤ s := by
    rw [hs, le_div_iff₀ (by positivity)]
    have := Real.log_le_log (Real.exp_pos _) hR
    rw [Real.log_exp] at this
    linarith
  have h1 : ‖Real.exp (b * s) • (endW H w cylInf (s, t) - P.x ((1 : ℝ) * P.T * t + c))‖ ≤ ε / 2 :=
    hs₀ s ((le_max_left _ _).trans hsge) t
  have e1 : endW H w cylInf (s, t) = proj H (w (ccwLoop R t)) := by
    simp only [endW, hs, ld_cyl R hRpos t]
  rw [e1, one_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  have hs0 : 0 ≤ s := (le_max_right _ _).trans hsge
  have h2 : 1 ≤ Real.exp (b * s) := Real.one_le_exp (by positivity)
  rw [dist_eq_norm]
  have h3 := norm_nonneg (proj H (w (ccwLoop R t)) - P.x (P.T * t + c))
  nlinarith

theorem ld_poly (p : ℂ[X]) (t : ℝ) (hp : p.natDegree ≠ 0 ∨ True) :
    ∃ ξ : ℝ → ℂ, Tendsto ξ atTop (𝓝 p.leadingCoeff) ∧ ∀ R : ℝ, 0 < R →
      p.eval (ccwLoop R t) = ((R ^ p.natDegree : ℝ) : ℂ) *
        (ξ R * Complex.exp (((2 * π * (p.natDegree * t) : ℝ) : ℂ) * Complex.I)) := by
  refine ⟨fun R => p.reverse.eval (ccwLoop R t)⁻¹, ?_, ?_⟩
  · have h0 : Tendsto (fun R : ℝ => (ccwLoop R t)⁻¹) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      have h1 : ∀ᶠ R : ℝ in atTop, R⁻¹ = ‖(ccwLoop R t)⁻¹‖ := by
        filter_upwards [eventually_gt_atTop 0] with R hR
        rw [norm_inv, lh_ccw_norm R t hR]
      exact tendsto_inv_atTop_zero.congr' h1
    have h2 : Tendsto (fun R : ℝ => p.reverse.eval (ccwLoop R t)⁻¹) atTop
        (𝓝 (p.reverse.eval 0)) := (p.reverse.continuous.tendsto 0).comp h0
    rwa [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse] at h2
  · intro R hR
    have hz : ccwLoop R t ≠ 0 := by
      intro h0
      have := lh_ccw_norm R t hR
      rw [h0, norm_zero] at this
      exact hR.ne this
    letI := invertibleOfNonzero hz
    have h1 := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (ccwLoop R t) p
    rw [invOf_eq_inv] at h1
    change p.reverse.eval (ccwLoop R t)⁻¹ * ccwLoop R t ^ p.natDegree = p.eval (ccwLoop R t) at h1
    rw [← h1]
    have h2 : ccwLoop R t ^ p.natDegree = ((R ^ p.natDegree : ℝ) : ℂ) *
        Complex.exp (((2 * π * (p.natDegree * t) : ℝ) : ℂ) * Complex.I) := by
      simp only [ccwLoop]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      congr 2
      ring
    rw [h2]
    ring

theorem exists_eq_singleton_of_dlambdaEnergy_eq_zero_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (P : ReebOrbit H) (hprime : P.IsPrime) (hinf : IsNondegenerateEnd H w cylInf P 1)
    (hact : Tendsto (fun ρ : ℝ => loopAction H w (ccwLoop ρ)) atTop (𝓝 P.T))
    (hneg : ∀ z₀ ∈ Γ, Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z₀) atBot)
    (hzero : dlambdaEnergy H (↑Γ)ᶜ w = 0) :
    ∃ z₁ : ℂ, Γ = {z₁} ∧ (∀ z ∉ Γ, proj H (w z) ∈ Set.range P.x ∧ piDs H w z = 0) ∧
      ∀ ρ : ℝ, ‖z₁‖ < ρ → loopAction H w (ccwLoop ρ) = P.T := by
  classical
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  obtain ⟨d, c, b, hb, hA, hW⟩ := hinf
  obtain ⟨M, hM⟩ := Γ.finite_toSet.isBounded.exists_norm_le
  have hnotin : ∀ z : ℂ, M < ‖z‖ → z ∉ Γ := fun z hz hzΓ =>
    absurd (hM z (Finset.mem_coe.2 hzΓ)) (not_le.2 hz)
  -- nonconstant
  have hnc : ∃ z₁ ∉ Γ, ∃ z₂ ∉ Γ, w z₁ ≠ w z₂ := by
    obtain ⟨s₀, hs₀⟩ := hA (1 / 2) (by norm_num)
    set s₁ : ℝ := max s₀ (Real.log (|M| + 1) / (2 * π)) with hs₁
    set s₂ : ℝ := s₁ + 2 / P.T with hs₂
    have hTp := P.T_pos
    have hs₂s₁ : s₁ ≤ s₂ := by
      rw [hs₂]
      have : 0 ≤ 2 / P.T := by positivity
      linarith
    have hnorm : ∀ s : ℝ, s₁ ≤ s → cylInf s 0 ∉ Γ := by
      intro s hs
      apply hnotin
      simp only [cylInf]
      rw [lh_ccw_norm _ _ (Real.exp_pos _)]
      have h1 : Real.log (|M| + 1) / (2 * π) ≤ s := (le_max_right _ _).trans hs
      rw [div_le_iff₀ (by positivity)] at h1
      have h2 : |M| + 1 ≤ Real.exp (2 * π * s) := by
        rw [← Real.log_le_iff_le_exp (by positivity)]
        linarith
      have := le_abs_self M
      linarith
    refine ⟨cylInf s₁ 0, hnorm s₁ le_rfl, cylInf s₂ 0, hnorm s₂ hs₂s₁, fun heq => ?_⟩
    have h1 : ‖endA H w cylInf (s₁, 0) - (1 : ℝ) * P.T * s₁ - d‖ ≤ 1 / 2 :=
      hs₀ s₁ (le_max_left _ _) 0
    have h2 : ‖endA H w cylInf (s₂, 0) - (1 : ℝ) * P.T * s₂ - d‖ ≤ 1 / 2 :=
      hs₀ s₂ ((le_max_left _ _).trans hs₂s₁) 0
    have h3 : endA H w cylInf (s₁, 0) = endA H w cylInf (s₂, 0) := by
      simp only [endA, heq]
    rw [Real.norm_eq_abs, abs_le] at h1 h2
    have h4 : P.T * s₂ = P.T * s₁ + 2 := by
      rw [hs₂, mul_add, mul_div_cancel₀ _ hTp.ne']
    rw [h3] at h1
    linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨p, hpdeg, hpzero, Q, hQ⟩ := eq_trivialCylinder_comp_polynomial H hH J hJ Γ w hw hnc hneg
    hzero
  have hpne : ∀ z ∉ Γ, p.eval z ≠ 0 := fun z hz h0 => by
    have : z ∈ ((↑Γ) : Set ℂ) := by
      rw [← hpzero]
      exact h0
    exact hz (Finset.mem_coe.1 this)
  have hprojw : ∀ z ∉ Γ, proj H (w z) = ldG Q (p.eval z) := fun z hz => by
    rw [hQ z hz, ld_proj H hH Q _ (hpne z hz)]
  set a : ℂ := p.leadingCoeff with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Polynomial.leadingCoeff_ne_zero]
    rintro rfl
    simp at hpdeg
  set e : ℝ → ℂ := fun τ => Complex.exp (((2 * π * τ : ℝ) : ℂ) * Complex.I) with he
  have he0 : ∀ τ, e τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  -- the key identity
  have hid : ∀ t : ℝ, P.x (P.T * t + c) = ldG Q (a * e (p.natDegree * t)) := by
    intro t
    obtain ⟨ξ, hξ, hval⟩ := ld_poly p t (Or.inr trivial)
    have hc1 : Tendsto (fun R : ℝ => ldG Q (ξ R * e (p.natDegree * t))) atTop
        (𝓝 (ldG Q (a * e (p.natDegree * t)))) :=
      (ldG_continuousAt Q _ (mul_ne_zero ha0 (he0 _))).tendsto.comp (hξ.mul_const _)
    have hc2 := ld_close H w P c b hb hW t
    refine tendsto_nhds_unique hc2 (hc1.congr' ?_)
    filter_upwards [eventually_gt_atTop (max M 0)] with R hR
    have hR0 : 0 < R := lt_of_le_of_lt (le_max_right _ _) hR
    have hnot : ccwLoop R t ∉ Γ := hnotin _ (by
      rw [lh_ccw_norm R t hR0]
      exact lt_of_le_of_lt (le_max_left _ _) hR)
    rw [hprojw _ hnot, hval R hR0, ldG_smul Q _ (pow_pos hR0 _)]
  -- degree one
  have hk1 : p.natDegree = 1 := by
    by_contra hk
    have hk2 : 2 ≤ p.natDegree := by omega
    have hTp := P.T_pos
    have hkr : (2 : ℝ) ≤ p.natDegree := by exact_mod_cast hk2
    set t₀ : ℝ := -c / P.T with ht₀
    set t₁ : ℝ := t₀ + 1 / p.natDegree with ht₁
    have e0 : P.T * t₀ + c = 0 := by
      rw [ht₀]
      field_simp
      ring
    have e1 : P.T * t₁ + c = P.T / p.natDegree := by
      rw [ht₁, mul_add, add_right_comm, e0]
      ring
    have hee : e (p.natDegree * t₁) = e (p.natDegree * t₀) := by
      have : (p.natDegree : ℝ) * t₁ = p.natDegree * t₀ + 1 := by
        rw [ht₁, mul_add, mul_one_div_cancel (by positivity)]
      simp only [he, this]
      have e2 : (((2 * π * ((p.natDegree : ℝ) * t₀ + 1) : ℝ) : ℂ) * Complex.I) =
          ((2 * π * ((p.natDegree : ℝ) * t₀) : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
        push_cast
        ring
      rw [e2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have h1 := hid t₀
    have h2 := hid t₁
    rw [e0] at h1
    rw [e1, hee, ← h1] at h2
    refine hprime (P.T / p.natDegree) (by positivity) ?_ h2
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨a₁, ha₁, b₁, hp⟩ := Polynomial.natDegree_eq_one.1 hk1
  set z₁ : ℂ := -b₁ / a₁ with hz₁
  have hΓ : Γ = {z₁} := by
    apply Finset.coe_injective
    rw [← hpzero, Finset.coe_singleton]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, ← hp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hz₁]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      rw [h]
      field_simp
      ring
  -- range
  have hrange : ∀ z ∉ Γ, proj H (w z) ∈ Set.range P.x := by
    intro z hz
    set v := p.eval z with hv
    have hv0 : v ≠ 0 := hpne z hz
    set t : ℝ := Complex.arg (v / a) / (2 * π) with ht
    refine ⟨P.T * t + c, ?_⟩
    rw [hid t, hprojw z hz, hk1]
    have hn : 0 < ‖v / a‖ := norm_pos_iff.2 (div_ne_zero hv0 ha0)
    have e1 : ((1 : ℕ) : ℝ) * t = t := by simp
    rw [e1]
    have e2 : e t = Complex.exp ((Complex.arg (v / a) : ℂ) * Complex.I) := by
      simp only [he, ht]
      congr 2
      rw [mul_div_cancel₀ _ (by positivity)]
    have e3 : ((‖v / a‖ : ℝ) : ℂ) * (a * e t) = v := by
      have := Complex.norm_mul_exp_arg_mul_I (v / a)
      rw [e2]
      calc ((‖v / a‖ : ℝ) : ℂ) * (a * Complex.exp ((Complex.arg (v / a) : ℂ) * Complex.I))
          = a * (((‖v / a‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (v / a) : ℂ) * Complex.I)) := by
            ring
        _ = a * (v / a) := by rw [this]
        _ = v := mul_div_cancel₀ _ ha0
    have h5 := ldG_smul Q _ hn (a * e t)
    rw [e3] at h5
    exact h5.symm
  -- density vanishes
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hprojc : ContDiffOn ℝ ∞ (fun z => proj H (w z)) ((↑Γ)ᶜ : Set ℂ) :=
    hprojs.comp hw.1 (fun z hz => hw.2.1 z hz)
  have hdc : ContinuousOn (fun z => dlambdaDensity H w z) ((↑Γ)ᶜ : Set ℂ) :=
    ZCS.continuousOn_dens (fun z => proj H (w z)) hUo hprojc
  have hofc : ContinuousOn (fun z => ENNReal.ofReal (dlambdaDensity H w z)) ((↑Γ)ᶜ : Set ℂ) :=
    ENNReal.continuous_ofReal.comp_continuousOn hdc
  have hae : (fun z => ENNReal.ofReal (dlambdaDensity H w z)) =ᵐ[volume.restrict ((↑Γ)ᶜ : Set ℂ)]
      fun _ => 0 :=
    (lintegral_eq_zero_iff' (hofc.aemeasurable hUo.measurableSet)).1 hzero
  have hd0 := Measure.eqOn_open_of_ae_eq hae hUo hofc continuousOn_const
  have hpi : ∀ z ∉ Γ, piDs H w z = 0 := by
    intro z hz
    have hzU : z ∈ ((↑Γ)ᶜ : Set ℂ) := fun h => hz (Finset.mem_coe.1 h)
    by_contra hne
    have hpos := (piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ _ hUo w hw.2.1 hw.2.2.1 hzU).1 hne
    have := hd0 hzU
    simp only [ENNReal.ofReal_eq_zero] at this
    linarith
  refine ⟨z₁, hΓ, fun z hz => ⟨hrange z hz, hpi z hz⟩, ?_⟩
  -- actions
  intro ρ hρ
  have hρ0 : 0 < ρ := (norm_nonneg _).trans_lt hρ
  have hconst : ∀ b' : ℝ, ρ ≤ b' → loopAction H w (ccwLoop b') = loopAction H w (ccwLoop ρ) := by
    intro b' hb'
    have hmemU : ∀ z : ℂ, ρ ≤ ‖z‖ → z ∈ ((↑Γ)ᶜ : Set ℂ) := by
      intro z hz hzΓ
      rw [hΓ, Finset.coe_singleton, Set.mem_singleton_iff] at hzΓ
      rw [hzΓ] at hz
      linarith
    obtain ⟨hle, heq⟩ := loopAction_le_and_dlambdaEnergy_annulus_eq H hH J hJ _ hUo w hw ρ b' hρ0 hb'
      (fun z hz _ => hmemU z hz)
    have hsubann : ball (0 : ℂ) b' \ ball 0 ρ ⊆ ((↑Γ)ᶜ : Set ℂ) := fun z hz =>
      hmemU z (by simpa using hz.2)
    have h0 : dlambdaEnergy H (ball 0 b' \ ball 0 ρ) w = 0 :=
      le_antisymm ((lintegral_mono_set hsubann).trans_eq hzero) bot_le
    rw [h0] at heq
    have := ENNReal.ofReal_eq_zero.1 heq.symm
    linarith
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hact
  filter_upwards [eventually_ge_atTop ρ] with b' hb'
  exact (hconst b' hb').symm

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (P : ReebOrbit H) (hprime : P.IsPrime) (hinf : IsNondegenerateEnd H w cylInf P 1)
    (hact : Tendsto (fun ρ : ℝ => loopAction H w (ccwLoop ρ)) atTop (𝓝 P.T))
    (hneg : ∀ z₀ ∈ Γ, Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z₀) atBot)
    (hzero : dlambdaEnergy H (↑Γ)ᶜ w = 0) :
    ∃ z₁ : ℂ, Γ = {z₁} ∧ (∀ z ∉ Γ, proj H (w z) ∈ Set.range P.x ∧ piDs H w z = 0) ∧
      ∀ ρ : ℝ, ‖z₁‖ < ρ → loopAction H w (ccwLoop ρ) = P.T :=
  exists_eq_singleton_of_dlambdaEnergy_eq_zero_aux H hH J hJ Γ w hw P hprime hinf hact hneg hzero
