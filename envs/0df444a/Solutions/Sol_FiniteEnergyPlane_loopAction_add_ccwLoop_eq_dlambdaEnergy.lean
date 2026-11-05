-- Prove2me | solution 1 for FiniteEnergyPlane.loopAction_add_ccwLoop_eq_dlambdaEnergy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T22:29:25.089968+00:00
-- url     : https://prove2.me/submissions/4cda8ead-74f7-44c3-9284-e064f7bf3d75

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_FiniteEnergyPlane_Compactness
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
import Theorems.Thm_FiniteEnergyPlane_exists_bubble
import Theorems.Thm_FiniteEnergyPlane_punctured_disk_asymptotics
import Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_isRemovablePuncture
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_affine
import Theorems.Thm_FiniteEnergyPlane_loopAction_cwLoop_eq_neg_ccwLoop
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg



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

/-- A nondegenerate end transported by a shift of the cylinder coordinate. -/
theorem ln_shift {n : ℕ} (H : V n → ℝ) (w w' : ℂ → V n) (e e' : ℝ → ℝ → ℂ) (ℓ : ℝ)
    (he : ∀ s t, w' (e s t) = w (e' (s + ℓ) t)) (P : ReebOrbit H) (ε : ℝ)
    (h : IsNondegenerateEnd H w' e P ε) : IsNondegenerateEnd H w e' P ε := by
  obtain ⟨d, c, b, hb, hA, hW⟩ := h
  refine ⟨d - ε * P.T * ℓ, c, b, hb, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨s₀, hs₀⟩ := hA δ hδ
    refine ⟨s₀ + ℓ, fun s hs t => ?_⟩
    have h1 : ‖endA H w' e (s - ℓ, t) - ε * P.T * (s - ℓ) - d‖ ≤ δ := hs₀ (s - ℓ) (by linarith) t
    have e1 : endA H w' e (s - ℓ, t) = endA H w e' (s, t) := by
      simp only [endA, he, sub_add_cancel]
    rw [e1] at h1
    show ‖endA H w e' (s, t) - ε * P.T * s - (d - ε * P.T * ℓ)‖ ≤ δ
    convert h1 using 2
    ring
  · intro δ hδ
    have hexp := Real.exp_pos (b * ℓ)
    obtain ⟨s₀, hs₀⟩ := hW (δ / Real.exp (b * ℓ)) (div_pos hδ hexp)
    refine ⟨s₀ + ℓ, fun s hs t => ?_⟩
    have h1 : ‖Real.exp (b * (s - ℓ)) • (endW H w' e (s - ℓ, t) - P.x (ε * P.T * t + c))‖ ≤
        δ / Real.exp (b * ℓ) := hs₀ (s - ℓ) (by linarith) t
    have e1 : endW H w' e (s - ℓ, t) = endW H w e' (s, t) := by
      simp only [endW, he, sub_add_cancel]
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_div_iff₀ hexp] at h1
    show ‖Real.exp (b * s) • (endW H w e' (s, t) - P.x (ε * P.T * t + c))‖ ≤ δ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have e2 : Real.exp (b * s) = Real.exp (b * (s - ℓ)) * Real.exp (b * ℓ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    calc _ = Real.exp (b * (s - ℓ)) * ‖endW H w e' (s, t) - P.x (ε * P.T * t + c)‖ *
          Real.exp (b * ℓ) := by ring
      _ ≤ δ := h1

/-- The action of a plane around a disk about any center is its `dλ`-energy there. -/
theorem ln_action {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    loopAction H u (fun t => z₀ + ccwLoop ρ t) = (dlambdaEnergy H (ball z₀ ρ) u).toReal := by
  obtain ⟨hfe, -, -, hen⟩ := rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hu z₀ 1
    one_pos 1 one_pos
  have hfe' : IsFiniteEnergyCurve H J Set.univ (fun w => (1 : ℝ) • u (z₀ + (1 : ℝ) • w)) := by
    simpa using hfe
  have h1 := loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ _ hfe' ρ hρ
  have h2 := (hen (ball z₀ ρ) (Set.subset_univ _) isOpen_ball.measurableSet).2
  have hset : {w : ℂ | z₀ + (1 : ℝ) • w ∈ ball z₀ ρ} = ball 0 ρ := by
    ext w
    simp [mem_ball, dist_eq_norm]
  rw [hset] at h2
  rw [h2] at h1
  rw [← h1]
  have h3 : loopInS H (fun w => (1 : ℝ) • u (z₀ + (1 : ℝ) • w)) (ccwLoop ρ) =
      loopInS H u (fun t => z₀ + ccwLoop ρ t) := by
    funext t
    simp only [loopInS, one_smul]
  simp only [loopAction, h3]

theorem isNondegenerateEnd_cylEndAt_of_gradNorm_tendsto_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (C : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate)
    (Γ : Finset ℂ) (w : ℂ → V n) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (u : ℕ → ℂ → V n) (hu : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k))
    (hE : ∀ k, energy H Set.univ (u k) ≤ ENNReal.ofReal C)
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (hconv : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • u k z) w (↑Γ)ᶜ)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Γ) (ζ : ℕ → ℂ) (hζ : Tendsto ζ atTop (𝓝 z₀))
    (hblow : Tendsto (fun k => gradNorm H (u k) (ζ k)) atTop atTop) :
    ∃ Q : ReebOrbit H, Q.T ≤ C ∧ IsNondegenerateEnd H w (cylEndAt z₀) Q (-1) ∧
      Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z₀) atBot ∧
      ∃ r η : ℝ, 0 < r ∧ 0 < η ∧ ∀ ρ ∈ Set.Ioo 0 r,
        η ≤ loopAction H w (fun t => z₀ + ccwLoop ρ t) := by
  classical
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  -- the punctured neighbourhood
  obtain ⟨ρ₀, hρ₀, hball⟩ : ∃ ρ₀ > 0, ball z₀ ρ₀ ⊆ ((↑(Γ.erase z₀)) : Set ℂ)ᶜ := by
    have ho : IsOpen (((↑(Γ.erase z₀)) : Set ℂ)ᶜ) := (Γ.erase z₀).finite_toSet.isClosed.isOpen_compl
    exact Metric.isOpen_iff.1 ho z₀ (by simp)
  have hsub : ball z₀ ρ₀ \ {z₀} ⊆ ((↑Γ)ᶜ : Set ℂ) := by
    intro z hz hzΓ
    exact hball hz.1 (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hz.2, Finset.mem_coe.1 hzΓ⟩))
  have hmem : ∀ ρ ∈ Set.Ioo 0 ρ₀, ∀ t, z₀ + ccwLoop ρ t ∈ ((↑Γ)ᶜ : Set ℂ) := by
    intro ρ hρ t
    apply hsub
    have hn := lh_ccw_norm ρ t hρ.1
    refine ⟨by simp [mem_ball, dist_eq_norm, hn, hρ.2], ?_⟩
    intro h0
    have h1 : ccwLoop ρ t = 0 := by simpa using h0
    rw [h1, norm_zero] at hn
    exact hρ.1.ne hn
  set A : ℝ → ℝ := fun ρ => loopAction H w (fun t => z₀ + ccwLoop ρ t) with hA
  have hV : ∀ j, ContDiffOn ℝ ∞ (fun z => c j • u j z) (↑Γ)ᶜ ∧
      ∀ z ∈ ((↑Γ)ᶜ : Set ℂ), c j • u j z ≠ 0 := fun j =>
    ⟨((lh_smul H hH J hJ Set.univ isOpen_univ (u j) (hu j) (c j) (hc j)).1.1).mono
        (Set.subset_univ _), fun z _ => smul_ne_zero (hc j).ne' ((hu j).2.1 z trivial)⟩
  have hsm : ∀ ρ : ℝ, ContDiff ℝ ∞ (fun t => z₀ + ccwLoop ρ t) := fun ρ =>
    contDiff_const.add (lh_ccw_contDiff ρ)
  have hlim : ∀ ρ ∈ Set.Ioo 0 ρ₀, Tendsto (fun k => loopAction H (u k) (fun t => z₀ + ccwLoop ρ t))
      atTop (𝓝 (A ρ)) := by
    intro ρ hρ
    have := lh_tendsto_loopAction H hH J hJ (fun t => z₀ + ccwLoop ρ t) (hsm ρ) (↑Γ)ᶜ hUo (hmem ρ hρ)
      (fun k z => c k • u k z) w hV hw.1 hw.2.1 hconv
    have heq : ∀ k, loopAction H (fun z => c k • u k z) (fun t => z₀ + ccwLoop ρ t) =
        loopAction H (u k) (fun t => z₀ + ccwLoop ρ t) := fun k =>
      lh_loopAction_smul H hH (u k) (c k) (hc k) _ (fun t => (hu k).2.1 _ trivial)
    simpa only [heq] using this
  have hdle : ∀ k (S : Set ℂ), dlambdaEnergy H S (u k) ≤ ENNReal.ofReal C := by
    intro k S
    refine le_trans (lintegral_mono_set (Set.subset_univ S)) ?_
    exact ((energyDensity_nonneg H hH J hJ Set.univ isOpen_univ (u k) (hu k)).2.2.1).trans (hE k)
  -- the bubble
  obtain ⟨φ, hφ, z', r, Q₁, hzz', hrpos, hr0, -, hQ₁C, hQ₁⟩ := exists_bubble H hH J hJ ∅
    (fun _ => Set.univ) (fun _ => isOpen_univ) monotone_const (fun _ => by simp)
    (by rw [Finset.coe_empty, Set.compl_empty]; exact Set.iUnion_const _) u hu C
    hE ζ (fun _ => trivial) hblow ⟨1, one_pos, by simp⟩ (Or.inr ⟨0, 0, fun _ _ => trivial⟩)
  have hC : 0 < C := Q₁.T_pos.trans_le hQ₁C
  have hz'lim : Tendsto z' atTop (𝓝 z₀) := by
    have h1 : Tendsto (fun j => ζ (φ j)) atTop (𝓝 z₀) := hζ.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun j => ζ (φ j) - z' j) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.2 hzz'
    simpa using h1.sub h2
  have hAlow : ∀ ρ ∈ Set.Ioo 0 ρ₀, Q₁.T ≤ A ρ := by
    intro ρ hρ
    have hle : ∀ᶠ j in atTop, dlambdaEnergy H (ball (z' j) (r j)) (u (φ j)) ≤
        dlambdaEnergy H (ball z₀ ρ) (u (φ j)) := by
      have h1 : ∀ᶠ j in atTop, dist (z' j) z₀ < ρ / 2 :=
        (Metric.tendsto_nhds.1 hz'lim) _ (half_pos hρ.1)
      have h2 : ∀ᶠ j in atTop, r j < ρ / 2 := hr0.eventually (gt_mem_nhds (half_pos hρ.1))
      filter_upwards [h1, h2] with j h1 h2
      refine lintegral_mono_set (ball_subset_ball' ?_)
      linarith
    have hval : ∀ j, dlambdaEnergy H (ball z₀ ρ) (u (φ j)) =
        ENNReal.ofReal (loopAction H (u (φ j)) (fun t => z₀ + ccwLoop ρ t)) := by
      intro j
      rw [ln_action H hH J hJ _ (hu _) z₀ ρ hρ.1, ENNReal.ofReal_toReal]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdle _ _)
    have hlim' : Tendsto (fun j => dlambdaEnergy H (ball z₀ ρ) (u (φ j))) atTop
        (𝓝 (ENNReal.ofReal (A ρ))) := by
      simp only [hval]
      exact ENNReal.tendsto_ofReal ((hlim ρ hρ).comp hφ.tendsto_atTop)
    have h3 : ENNReal.ofReal Q₁.T ≤ ENNReal.ofReal (A ρ) := by
      refine hQ₁.trans ?_
      rw [← hlim'.limsup_eq]
      exact limsup_le_limsup hle
    rcases (ENNReal.ofReal_le_ofReal_iff').1 h3 with h | h
    · exact h
    · exact absurd h (not_le.2 Q₁.T_pos)
  have hAup : ∀ ρ ∈ Set.Ioo 0 ρ₀, A ρ ≤ C := by
    intro ρ hρ
    refine le_of_tendsto' (hlim ρ hρ) fun k => ?_
    rw [ln_action H hH J hJ _ (hu _) z₀ ρ hρ.1]
    exact ENNReal.toReal_le_of_le_ofReal hC.le (hdle _ _)
  -- the rescaled curve on the unit disk
  have hw₁ : IsFiniteEnergyCurve H J (ball z₀ ρ₀ \ {z₀}) w := lh_fe_mono H J hsub w hw
  set w₂ : ℂ → V n := fun z => w (z₀ + (ρ₀ : ℂ) * z) with hw₂def
  have hw₂ : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) w₂ :=
    (isFiniteEnergyCurve_comp_affine H J z₀ ρ₀ hρ₀ w hw₁).1
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hUo₂ : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hprojw₂ : ContDiffOn ℝ ∞ (fun z => proj H (w₂ z)) (ball 0 1 \ {0}) :=
    hprojs.comp hw₂.1 (fun z hz => hw₂.2.1 z hz)
  have hact₂ : ∀ ρ ∈ Set.Ioo (0 : ℝ) 1, loopAction H w₂ (cwLoop 0 ρ) = -A (ρ₀ * ρ) := by
    intro ρ hρ
    rw [loopAction_cwLoop_eq_neg_ccwLoop H w₂ hUo₂ hprojw₂ ρ ?_]
    · congr 1
      simp only [hA, loopAction]
      have : loopInS H w₂ (ccwLoop ρ) = loopInS H w (fun t => z₀ + ccwLoop (ρ₀ * ρ) t) := by
        funext t
        simp only [loopInS, hw₂def, ccwLoop]
        congr 3
        push_cast
        ring
      rw [this]
    · intro θ
      have hn : ‖circleMap 0 ρ θ‖ = ρ := by
        simp [circleMap, abs_of_pos hρ.1]
      refine ⟨by simp [mem_ball, hn, hρ.2], ?_⟩
      intro h0
      have h0' : circleMap 0 ρ θ = 0 := h0
      rw [h0', norm_zero] at hn
      exact hρ.1.ne hn
  have hmemρ : ∀ ρ ∈ Set.Ioo (0 : ℝ) 1, ρ₀ * ρ ∈ Set.Ioo 0 ρ₀ := fun ρ hρ =>
    ⟨mul_pos hρ₀ hρ.1, by nlinarith [hρ.2]⟩
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), -C ≤ loopAction H w₂ (cwLoop 0 ρ) ∧
      loopAction H w₂ (cwLoop 0 ρ) ≤ -Q₁.T := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ρ hρ
    rw [hact₂ ρ hρ]
    have h1 := hAlow _ (hmemρ ρ hρ)
    have h2 := hAup _ (hmemρ ρ hρ)
    constructor <;> linarith
  rcases punctured_disk_asymptotics H hH J hJ w₂ hw₂ with hrem | ⟨Q₀, -, hQ₀, -, hneg, hseq⟩
  · exfalso
    have h0 := tendsto_loopAction_of_isRemovablePuncture H hH J hJ w₂ hrem
    have := le_of_tendsto h0 (hev.mono fun _ h => h.2)
    linarith [Q₁.T_pos]
  have hQ₀le : Q₀ ≤ -Q₁.T := le_of_tendsto hQ₀ (hev.mono fun _ h => h.2)
  have hQ₀ge : -C ≤ Q₀ := ge_of_tendsto hQ₀ (hev.mono fun _ h => h.1)
  have hQ₀neg : Q₀ < 0 := by linarith [Q₁.T_pos]
  -- radii
  set ρs : ℕ → ℝ := fun k => ((k : ℝ) + 2)⁻¹ with hρs
  have hρspos : ∀ k, 0 < ρs k := fun k => inv_pos.2 (by positivity)
  have hρslim : Tendsto ρs atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨ψ, hψ, Q, hQT, c₁, hc₁⟩ := hseq ρs hρspos hρslim
  have hQT' : Q.T = -Q₀ := by rw [hQT, abs_of_neg hQ₀neg]
  have hQC : Q.T ≤ C := by linarith
  have hend₂ : IsNondegenerateEnd H w₂ cylEnd Q (-1) := by
    refine la_isNondegenerateEnd_of_loops H hH J hJ w₂ hw₂ Q (hnd Q hQC) (-1) (Or.inr rfl) _
      (fun k => hρspos (ψ k)) (hρslim.comp hψ.tendsto_atTop) c₁ ?_
    have he : (fun t : ℝ => Q.x (-1 * Q.T * t + c₁)) = fun t : ℝ => Q.x (Q₀ * t + c₁) := by
      funext t
      rw [hQT']
      congr 2
      ring
    rw [he]
    exact hc₁
  refine ⟨Q, hQC, ?_, ?_, ρ₀, Q₁.T, hρ₀, Q₁.T_pos, hAlow⟩
  · refine ln_shift H w w₂ cylEnd (cylEndAt z₀) (-(Real.log ρ₀) / (2 * π)) ?_ Q (-1) hend₂
    intro s t
    simp only [hw₂def, cylEnd, cylEndAt, cwLoop]
    congr 1
    have hexp : Real.exp (-(2 * π * (s + -(Real.log ρ₀) / (2 * π)))) =
        ρ₀ * Real.exp (-(2 * π * s)) := by
      have hpi : (2 * π : ℝ) ≠ 0 := by positivity
      have e3 : -(2 * π * (s + -(Real.log ρ₀) / (2 * π))) = Real.log ρ₀ + -(2 * π * s) := by
        field_simp
        ring
      rw [e3, Real.exp_add, Real.exp_log hρ₀]
    rw [hexp]
    push_cast
    ring
  · have hg : Tendsto (fun z : ℂ => (z - z₀) / (ρ₀ : ℂ)) (𝓝[≠] z₀) (𝓝[≠] 0) := by
      have hρc : (ρ₀ : ℂ) ≠ 0 := by exact_mod_cast hρ₀.ne'
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc0 : Continuous fun z : ℂ => (z - z₀) / (ρ₀ : ℂ) := by fun_prop
        have := hc0.tendsto z₀
        simp only [sub_self, zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact div_ne_zero (sub_ne_zero.2 hz) hρc
    have := (hneg hQ₀neg).comp hg
    refine this.congr fun z => ?_
    have hρc : (ρ₀ : ℂ) ≠ 0 := by exact_mod_cast hρ₀.ne'
    simp only [Function.comp, hw₂def]
    rw [mul_div_cancel₀ _ hρc, add_sub_cancel]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    loopAction H u (fun t => z₀ + ccwLoop ρ t) = (dlambdaEnergy H (ball z₀ ρ) u).toReal :=
  ln_action H hH J hJ u hu z₀ ρ hρ
