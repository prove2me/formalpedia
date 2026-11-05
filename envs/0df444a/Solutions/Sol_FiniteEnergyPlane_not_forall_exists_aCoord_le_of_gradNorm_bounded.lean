-- Prove2me | solution 1 for FiniteEnergyPlane.not_forall_exists_aCoord_le_of_gradNorm_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T21:08:28.355059+00:00
-- url     : https://prove2.me/submissions/5a633a0b-4656-4efd-ab73-e06268c03abc

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
import Theorems.Thm_FiniteEnergyPlane_tendsto_aCoord_atTop_of_small_area



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

/-- The coordinate `a` of a plane with a positive nondegenerate puncture at `∞` is bounded below. -/
theorem lz_bddBelow (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (hnd : IsNondegenerateEnd H u cylInf P 1) : ∃ m : ℝ, ∀ z, m ≤ aCoord H (u z) := by
  obtain ⟨-, -, hacoord, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨d, -, -, -, h1, -⟩ := hnd
  obtain ⟨s₀, hs₀⟩ := h1 1 one_pos
  set s₁ : ℝ := max s₀ 0 with hs₁
  set R : ℝ := Real.exp (2 * π * s₁) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hcont : Continuous (fun z => aCoord H (u z)) :=
    (hacoord.comp_contDiff (contDiffOn_univ.1 hu.1) (fun z => hu.2.1 z trivial)).continuous
  obtain ⟨m₀, hm₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨min (-m₀) (d - 1), fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ R
  · have := hm₀ z (mem_closedBall_zero_iff.2 hz)
    rw [Real.norm_eq_abs] at this
    exact (min_le_left _ _).trans (neg_le_of_abs_le this)
  · push_neg at hz
    have hzpos : 0 < ‖z‖ := hRpos.trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    set s : ℝ := Real.log ‖z‖ / (2 * π) with hs
    set t : ℝ := Complex.arg z / (2 * π) with ht
    have hexp : Real.exp (2 * π * s) = ‖z‖ := by
      rw [hs, mul_div_cancel₀ _ (by positivity), Real.exp_log hzpos]
    have hcyl : cylInf s t = z := by
      simp only [cylInf, ccwLoop, hexp, ht]
      rw [show (((2 * π * (Complex.arg z / (2 * π)) : ℝ)) : ℂ) = (Complex.arg z : ℂ) by
        rw [mul_div_cancel₀ _ (by positivity)]]
      exact Complex.norm_mul_exp_arg_mul_I z
    have hss : s₁ ≤ s := by
      have h2 : Real.exp (2 * π * s₁) < Real.exp (2 * π * s) := by rw [hexp]; exact hz
      have h3 := Real.exp_lt_exp.1 h2
      have := Real.pi_pos
      nlinarith
    have h2 := hs₀ s ((le_max_left _ _).trans hss) t
    simp only [endA, hcyl, Real.norm_eq_abs] at h2
    have h3 := (abs_le.1 h2).1
    have hs0 : 0 ≤ s := (le_max_right _ _).trans hss
    have := mul_nonneg P.T_pos.le hs0
    refine (min_le_right _ _).trans ?_
    nlinarith

theorem not_forall_exists_aCoord_le_of_gradNorm_bounded_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (hgrad : ∀ Kc : Set ℂ, IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u k) z ≤ M) :
    ¬ ∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (u k z) ≤ M := by
  classical
  intro hbot
  have hγT : γ < P.T := hγ₁ P le_rfl
  obtain ⟨-, -, hacoord, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k) := fun k => (hu k).1.1
  -- near-minimizers
  have hmin : ∀ k, ∃ z, ∀ z', aCoord H (u k z) - 1 ≤ aCoord H (u k z') := by
    intro k
    obtain ⟨m, hm⟩ := lz_bddBelow H hH J hJ (u k) (hfe k) P (hu k).2.1
    have hbdd : BddBelow (Set.range fun z => aCoord H (u k z)) := ⟨m, by rintro _ ⟨z, rfl⟩; exact hm z⟩
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _)
      (show sInf (Set.range fun z => aCoord H (u k z)) <
        sInf (Set.range fun z => aCoord H (u k z)) + 1 by linarith)
    refine ⟨z, fun z' => ?_⟩
    have := csInf_le hbdd ⟨z', rfl⟩
    simp only at hz this
    linarith
  choose ζ hζ using hmin
  have hζbot : ∀ M : ℝ, ∀ᶠ k in atTop, aCoord H (u k (ζ k)) ≤ M := by
    intro M
    filter_upwards [hbot (M - 1)] with k ⟨z, hz⟩
    linarith [hζ k z]
  -- the coordinate at `0` is bounded below
  have hKne : K ⊆ {y : V 1 | y ≠ 0} := fun y hy h0 => hK0 (h0 ▸ hy)
  obtain ⟨a₀, ha₀⟩ := (hK.image_of_continuousOn (hacoord.continuousOn.mono hKne)).bddBelow
  have ha₀' : ∀ k, a₀ ≤ aCoord H (u k 0) := fun k => ha₀ ⟨_, (hu k).2.2.1, rfl⟩
  have hsmooth : ∀ k, ContDiff ℝ ∞ (fun z => aCoord H (u k z)) := fun k =>
    hacoord.comp_contDiff (contDiffOn_univ.1 (hfe k).1) (fun z => (hfe k).2.1 z trivial)
  -- the near-minimizers go to `∞`
  have hζinf : Tendsto (fun k => ‖ζ k‖) atTop atTop := by
    refine tendsto_atTop.2 fun R => ?_
    obtain ⟨M, hM⟩ := hgrad (closedBall 0 (max R 0)) (isCompact_closedBall _ _)
    filter_upwards [hζbot (a₀ - (max M 0) * (max R 0) - 1)] with k hk
    by_contra hlt
    push_neg at hlt
    have hmem : ζ k ∈ closedBall (0 : ℂ) (max R 0) :=
      mem_closedBall_zero_iff.2 (hlt.le.trans (le_max_left _ _))
    have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) (max R 0) :=
      mem_closedBall_self (le_max_right _ _)
    have hmv := (convex_closedBall (0 : ℂ) (max R 0)).norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => aCoord H (u k z)) (C := max M 0)
      (fun z _ => ((hsmooth k).differentiable (by simp)) z)
      (fun z hz => by
        have h1 := hM k z hz
        have h2 : ‖fderiv ℝ (fun z => aCoord H (u k z)) z‖ ≤ gradNorm H (u k) z := by
          unfold gradNorm
          linarith [norm_nonneg (fderiv ℝ (fun z => proj H (u k z)) z)]
        exact h2.trans (h1.trans (le_max_left _ _))) (x := ζ k) (y := 0) hmem h0mem
    simp only [sub_zero, zero_sub, norm_neg, Real.norm_eq_abs] at hmv
    have h3 := (abs_le.1 hmv).2
    have h4 : ‖ζ k‖ * max M 0 ≤ max R 0 * max M 0 := by
      refine mul_le_mul_of_nonneg_right (hlt.le.trans (le_max_left _ _)) (le_max_right _ _)
    have h5 := ha₀' k
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hζinf.eventually (eventually_gt_atTop 2))
  -- the rescalings
  set s : ℕ → ℝ := fun j => ‖ζ (j + N)‖ with hs
  have hs2 : ∀ j, 2 < s j := fun j => hN _ (Nat.le_add_left _ _)
  have hspos : ∀ j, 0 < s j := fun j => by linarith [hs2 j]
  set c : ℕ → ℝ := fun j => Real.exp (-(2 * aCoord H (u (j + N) (ζ (j + N))))) with hc
  have hcpos : ∀ j, 0 < c j := fun j => Real.exp_pos _
  set v : ℕ → ℂ → V 1 := fun j z => c j • u (j + N) (0 + s j • z) with hv
  have hres := fun j => rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ (u (j + N))
    (hfe _) 0 (s j) (hspos j) (c j) (hcpos j)
  have hset : ∀ (j : ℕ) (A : Set ℂ), {w : ℂ | (0 : ℂ) + s j • w ∈ A} =
      (fun w : ℂ => (0 : ℂ) + s j • w) ⁻¹' A := fun _ _ => rfl
  have hnorm : ∀ j (z : ℂ), ‖(0 : ℂ) + s j • z‖ = s j * ‖z‖ := fun j z => by
    rw [zero_add, norm_smul, Real.norm_of_nonneg (hspos j).le]
  have hunivset : ∀ j, {w : ℂ | (0 : ℂ) + s j • w ∈ (Set.univ : Set ℂ)} = Set.univ := fun j => by
    ext; simp
  have hvfe : ∀ j, IsFiniteEnergyCurve H J Set.univ (v j) := fun j => by
    have := (hres j).1
    rwa [hunivset j] at this
  have hvE : ∀ j, energy H Set.univ (v j) ≤ ENNReal.ofReal P.T := fun j => by
    have := ((hres j).2.2.2 Set.univ subset_rfl MeasurableSet.univ).1
    rw [hunivset j] at this
    rw [show energy H Set.univ (v j) = _ from this]
    exact (lh_energy H hH J hJ (hu _)).1.le
  set r : ℕ → ℝ := fun j => 2 / s j with hr
  have hrpos : ∀ j, 0 < r j := fun j => div_pos two_pos (hspos j)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    refine Tendsto.const_div_atTop ?_ 2
    exact hζinf.comp (tendsto_add_atTop_nat N)
  have hextset : ∀ j, {z : ℂ | r j < ‖z‖} = {w : ℂ | (0 : ℂ) + s j • w ∈ {z : ℂ | 2 < ‖z‖}} := by
    intro j
    ext z
    simp only [Set.mem_setOf_eq, hnorm, hr]
    rw [div_lt_iff₀ (hspos j), mul_comm]
  have hvd : ∀ j, dlambdaEnergy H {z | r j < ‖z‖} (v j) ≤ ENNReal.ofReal γ := fun j => by
    rw [hextset j]
    have := ((hres j).2.2.2 {z : ℂ | 2 < ‖z‖} (Set.subset_univ _)
      (isOpen_lt continuous_const continuous_norm).measurableSet).2
    rw [show dlambdaEnergy H {w : ℂ | (0 : ℂ) + s j • w ∈ {z : ℂ | 2 < ‖z‖}} (v j) = _ from this]
    rw [← (hu (j + N)).2.2.2]
    refine lintegral_mono_set fun z hz => ?_
    show 1 < ‖z‖
    have : 2 < ‖z‖ := hz
    linarith
  have hloop : ∀ j (ρ : ℝ), loopInS H (v j) (ccwLoop ρ) =
      loopInS H (u (j + N)) (ccwLoop (s j * ρ)) := by
    intro j ρ
    funext t
    have hne := (hfe (j + N)).2.1 (0 + s j • ccwLoop ρ t) trivial
    simp only [loopInS, hv]
    rw [(proj_aCoord_smul_aux H hH (c j) (hcpos j) _ hne).1]
    congr 2
    simp only [ccwLoop, zero_add, Complex.real_smul]
    push_cast
    ring
  have hact : ∀ j, ∀ ρ : ℝ, r j < ρ → P.T - γ ≤ loopAction H (v j) (ccwLoop ρ) := by
    intro j ρ hρ
    have h1 : 2 < s j * ρ := by
      have := (div_lt_iff₀ (hspos j)).1 hρ
      linarith
    simp only [loopAction, hloop]
    exact (lh_action H hH J hJ (hu (j + N)) hγ hγT).2.2 _ (by linarith)
  have hN1 : ∀ j z, -1 ≤ aCoord H (v j z) := by
    intro j z
    have h1 := (hres j).2.1 z trivial
    simp only [hv]
    rw [h1, hc, Real.log_exp]
    have := hζ (j + N) (0 + s j • z)
    linarith
  have hfin := tendsto_aCoord_atTop_of_small_area H hH J hJ P.T γ (P.T - γ) 1 hγ hγ₁
    (by linarith) r hrpos hrlim v hvfe hvE hvd hact hN1 (sphere 0 1) (isCompact_sphere _ _) (by simp)
    1
  obtain ⟨j, hj⟩ := hfin.exists
  have hz1 : (s j)⁻¹ • ζ (j + N) ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_pos.2 (hspos j)).le]
    exact inv_mul_cancel₀ (hspos j).ne'
  have h2 := hj _ hz1
  have h3 := (hres j).2.1 ((s j)⁻¹ • ζ (j + N)) trivial
  simp only [hv] at h2
  rw [h3, hc, Real.log_exp, zero_add, smul_smul, mul_inv_cancel₀ (hspos j).ne', one_smul] at h2
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (hgrad : ∀ Kc : Set ℂ, IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u k) z ≤ M) :
    ¬ ∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (u k z) ≤ M :=
  not_forall_exists_aCoord_le_of_gradNorm_bounded_aux H hH J hJ P γ hγ hγ₁ K hK hK0 u hu hgrad
