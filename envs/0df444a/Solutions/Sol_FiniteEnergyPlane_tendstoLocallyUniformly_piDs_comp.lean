-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoLocallyUniformly_piDs_comp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T22:37:57.832776+00:00
-- url     : https://prove2.me/submissions/6deee1e2-3587-4dd7-a290-589c6f0494b1

import Definitions.Def_FiniteEnergyPlane_Winding
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
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_eq_zero_or_isolated
import Theorems.Thm_FiniteEnergyPlane_exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_continuousOn_piDs
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_cylInf_of_hasLoopWind_circle
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_annulus_eq_add_sum
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_eq_sum
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos
import Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_cylInf_of_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Theorems.Thm_FiniteEnergyPlane_continuousAt_xiCoordC_prod
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb



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

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma wcm_energy_mono (H : V 1 → ℝ) {U W : Set ℂ} (h : W ⊆ U) (u : ℂ → V 1) :
    energy H W u ≤ energy H U u := by
  unfold energy
  exact iSup₂_mono fun φ _ => lintegral_mono_set h

lemma wcm_restrict {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {U W : Set ℂ} {u : ℂ → V 1}
    (hu : IsFiniteEnergyCurve H J U u) (h : W ⊆ U) : IsFiniteEnergyCurve H J W u :=
  ⟨hu.1.mono h, fun z hz => hu.2.1 z (h hz), fun z hz => hu.2.2.1 z (h hz),
    lt_of_le_of_lt (wcm_energy_mono H h u) hu.2.2.2⟩

lemma wcm_exists_ne (z : ℂ) {r : ℝ} (hr : 0 < r) : ∃ w ∈ ball z r, w ≠ z := by
  refine ⟨z + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  · intro h
    have h2 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination h
    rw [Complex.ofReal_eq_zero] at h2
    linarith

lemma wcm_ball_sub {z w : ℂ} {r : ℝ} (hw : w ∈ ball z r) (hwz : w ≠ z) :
    0 < min (r - dist w z) (dist w z) ∧
      ∀ v ∈ ball w (min (r - dist w z) (dist w z)), v ∈ ball z r ∧ v ≠ z := by
  have hd : 0 < dist w z := dist_pos.2 hwz
  have hwr := mem_ball.1 hw
  refine ⟨lt_min (by linarith) hd, fun v hv => ⟨?_, ?_⟩⟩
  · have := mem_ball.1 hv
    rw [mem_ball]
    linarith [dist_triangle v w z, min_le_left (r - dist w z) (dist w z)]
  · intro hvz
    rw [hvz] at hv
    have := mem_ball.1 hv
    rw [dist_comm] at this
    linarith [min_le_right (r - dist w z) (dist w z)]

/-- The zeros of `piDs` beyond a radius enclosing `Γ` are finite, with local indices, and bounded. -/
lemma wcm_zeros (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1) (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) (R₀ : ℝ)
    (hΓ : ∀ z ∈ Γ, ‖z‖ < R₀) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ R₀ < ‖z‖ ∧ piDs H u z = 0) ∧
      ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) := by
  classical
  set U : Set ℂ := (↑Γ)ᶜ with hUdef
  have hUo : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  have hR₀U : ∀ z : ℂ, R₀ ≤ ‖z‖ → z ∈ U := fun z hz hzΓ => by
    have := hΓ z (Finset.mem_coe.1 hzΓ)
    linarith
  have hloc : ∀ z₀ ∈ U, ∃ r > (0 : ℝ), ball z₀ r ⊆ U ∧
      ((∀ z ∈ ball z₀ r, piDs H u z = 0) ∨
        ((∀ z ∈ ball z₀ r, z ≠ z₀ → piDs H u z ≠ 0) ∧
          (piDs H u z₀ = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z₀ m))) :=
    fun z₀ hz => exists_ball_piDs_eq_zero_or_isolated H hH J hJ U hUo u hu.1 hu.2.1 hu.2.2.1 z₀ hz
  set A : Set ℂ := {z | z ∈ U ∧ ∃ r > (0 : ℝ), ∀ w ∈ ball z r, piDs H u w = 0} with hAdef
  set B : Set ℂ := {z | z ∈ U ∧ ∃ r > (0 : ℝ), ball z r ⊆ U ∧
    ∀ w ∈ ball z r, w ≠ z → piDs H u w ≠ 0} with hBdef
  have hAo : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, r, hr, hz⟩
    obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hUo z hzU
    refine ⟨min r r', lt_min hr hr', fun w hw => ⟨hr'U (ball_subset_ball (min_le_right _ _) hw), ?_⟩⟩
    have hw' := mem_ball.1 hw
    refine ⟨r - dist w z, sub_pos.2 (lt_of_lt_of_le hw' (min_le_left _ _)), fun v hv => hz v ?_⟩
    have := mem_ball.1 hv
    rw [mem_ball]
    linarith [dist_triangle v w z]
  have hBo : IsOpen B := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, r, hr, hrU, hz⟩
    refine ⟨r, hr, fun w hw => ?_⟩
    by_cases hwz : w = z
    · rw [hwz]; exact ⟨hzU, r, hr, hrU, hz⟩
    obtain ⟨hpos, hsub⟩ := wcm_ball_sub hw hwz
    exact ⟨hrU hw, _, hpos, fun v hv => hrU (hsub v hv).1,
      fun v hv _ => hz v (hsub v hv).1 (hsub v hv).2⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨_, r₁, hr₁, h₁⟩ ⟨_, r₂, hr₂, _, h₂⟩
    obtain ⟨w, hw, hwz⟩ := wcm_exists_ne z (lt_min hr₁ hr₂)
    exact h₂ w (ball_subset_ball (min_le_right _ _) hw) hwz
      (h₁ w (ball_subset_ball (min_le_left _ _) hw))
  have hUAB : U ⊆ A ∪ B := by
    intro z hz
    obtain ⟨r, hr, hrU, h | ⟨h, _⟩⟩ := hloc z hz
    · exact Or.inl ⟨hz, r, hr, h⟩
    · exact Or.inr ⟨hz, r, hr, hrU, h⟩
  have hpre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (Γ.countable_toSet)).isPreconnected
  have hUB : U ⊆ B := by
    rcases hpre.subset_or_subset hAo hBo hdisj hUAB with h | h
    · exfalso
      obtain ⟨z, hzΓ, hz⟩ := hne
      obtain ⟨_, r, hr, h0⟩ := h (show z ∈ U from hzΓ)
      exact hz (h0 z (mem_ball_self hr))
    · exact h
  have hnotA : ∀ z ∈ U, ∀ r > (0 : ℝ), ∃ w ∈ ball z r, piDs H u w ≠ 0 := by
    intro z hz r hr
    obtain ⟨_, r₀, hr₀, _, h₀⟩ := hUB hz
    obtain ⟨w, hw, hwz⟩ := wcm_exists_ne z (lt_min hr hr₀)
    exact ⟨w, ball_subset_ball (min_le_left _ _) hw,
      h₀ w (ball_subset_ball (min_le_right _ _) hw) hwz⟩
  have part1 : ∀ z ∈ U, piDs H u z = 0 → ∃ m : ℤ, HasZeroIndex (piDs H u) z m := by
    intro z hzΓ hz0
    obtain ⟨r, hr, _, h | ⟨_, h⟩⟩ := hloc z hzΓ
    · obtain ⟨w, hw, hw0⟩ := hnotA z hzΓ r hr
      exact absurd (h w hw) hw0
    · obtain ⟨m, -, hm⟩ := h hz0
      exact ⟨m, hm⟩
  have hfarU : {z : ℂ | R₀ < ‖z‖} ⊆ U := fun z hz => hR₀U z (le_of_lt hz)
  obtain ⟨R₁, hR₁⟩ := exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf H hH J hJ R₀ u
    (wcm_restrict hu hfarU) Pinf 1 (Or.inl rfl) hinf (by
      intro R'
      set p : ℂ := ((max R' R₀ + 2 + |R₀| : ℝ) : ℂ)
      have hmax : 0 ≤ max R' R₀ + |R₀| := by
        linarith [le_max_right R' R₀, neg_abs_le R₀]
      have hpn : ‖p‖ = max R' R₀ + 2 + |R₀| := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
        linarith
      have hpU : p ∈ U := hfarU (by
        show R₀ < ‖p‖
        rw [hpn]; linarith [le_max_right R' R₀, abs_nonneg R₀])
      obtain ⟨w, hw, hw0⟩ := hnotA p hpU 1 one_pos
      refine ⟨w, ?_, hw0⟩
      have h1 := mem_ball.1 hw
      rw [dist_eq_norm] at h1
      have h2 := norm_sub_norm_le p w
      rw [norm_sub_rev] at h1
      linarith [le_max_left R' R₀, abs_nonneg R₀])
  set K : Set ℂ := closedBall 0 (max R₁ R₀) \ ball 0 R₀ with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKU : K ⊆ U := by
    rintro x ⟨_, hx⟩
    refine hR₀U x ?_
    simpa using hx
  set Zs : Set ℂ := {z | R₀ < ‖z‖ ∧ piDs H u z = 0} with hZs
  have hZK : Zs ⊆ K := by
    rintro z ⟨hzR, hz0⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      by_contra hlt
      exact hR₁ z (lt_of_le_of_lt (le_max_left _ _) (not_le.1 hlt)) hz0
    · simpa using hzR.le
  have hBx : ∀ x ∈ U, ∃ r > (0 : ℝ), ∀ w ∈ ball x r, w ≠ x → piDs H u w ≠ 0 := by
    intro x hx
    obtain ⟨_, r, hr, _, h⟩ := hUB hx
    exact ⟨r, hr, h⟩
  choose! rr hrrpos hrr using hBx
  obtain ⟨t, ht, hcover⟩ := hKc.elim_nhds_subcover (fun x => ball x (rr x))
    (fun x hx => ball_mem_nhds x (hrrpos x (hKU hx)))
  have hZt : Zs ⊆ ↑t := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hcover (hZK hz))
    by_cases h : z = x
    · rw [h]; exact hx
    · exact absurd hz.2 (hrr x (hKU (ht x hx)) z hzx h)
  have hfin : Zs.Finite := t.finite_toSet.subset hZt
  choose! idx hidx using part1
  refine ⟨hfin.toFinset, fun z => ?_, idx, fun z hz => ?_⟩
  · rw [Set.Finite.mem_toFinset]
    rfl
  · rw [Set.Finite.mem_toFinset] at hz
    exact hidx z (hfarU hz.1) hz.2

theorem hasLoopWind_cylInf_eq_windInf_sub_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1) (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) (k : ℤ)
    (hk : HasWindInfAt H u cylInf 1 k) (s₀ : ℝ)
    (hΓ : ∀ z ∈ Γ, ‖z‖ < Real.exp (2 * π * s₀))
    (hcirc : ∀ z : ℂ, ‖z‖ = Real.exp (2 * π * s₀) → piDs H u z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ Real.exp (2 * π * s₀) < ‖z‖ ∧ piDs H u z = 0) ∧
      ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) ∧
        HasLoopWind (fun t => xiCoordC H (endW H u cylInf (s₀, t))
      (piXi H (endW H u cylInf (s₀, t)) (fderiv ℝ (endW H u cylInf) (s₀, t) (1, 0)))) (k - ∑ z ∈ Z, idx z) := by
  classical
  have hpi := Real.pi_pos
  set R₀ : ℝ := Real.exp (2 * π * s₀) with hR₀
  have hR₀0 : 0 < R₀ := Real.exp_pos _
  obtain ⟨Z, hZ, idx, hidx⟩ := wcm_zeros H hH J hJ Γ u hu Pinf hinf hne R₀ hΓ
  refine ⟨Z, hZ, idx, hidx, ?_⟩
  obtain ⟨huc, hu0, hhol, -⟩ := hu
  set U : Set ℂ := (↑Γ)ᶜ with hUdef
  have hU : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  have hR₀U : ∀ z : ℂ, R₀ ≤ ‖z‖ → z ∈ U := fun z hz hzΓ => by
    have := hΓ z (Finset.mem_coe.1 hzΓ)
    linarith
  have hpc : ContinuousOn (piDs H u) U := continuousOn_piDs H hH U hU u huc hu0
  -- a big radius above all zeros, at which `hk` applies
  obtain ⟨s₁, hs₁⟩ := hk
  set s₂ : ℝ := max (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π)) with hs₂
  set R₂ : ℝ := Real.exp (2 * π * s₂) with hR₂
  have hR₂0 : 0 < R₂ := Real.exp_pos _
  have hs₂s₁ : s₁ ≤ s₂ := by
    linarith [le_max_left s₁ s₀, le_max_left (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π))]
  have hs₂s₀ : s₀ < s₂ := by
    linarith [le_max_right s₁ s₀, le_max_left (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π))]
  have hR₀₂ : R₀ < R₂ := Real.exp_lt_exp.2 (by nlinarith)
  have hZnn : 0 ≤ ∑ z ∈ Z, ‖z‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZR₂ : ∀ z ∈ Z, ‖z‖ < R₂ := by
    intro z hz
    have h1 := Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _) hz
    have h2 : Real.log (∑ z ∈ Z, ‖z‖ + 1) ≤ 2 * π * s₂ := by
      have := le_max_right (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π))
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h3 : ∑ z ∈ Z, ‖z‖ + 1 ≤ R₂ := by
      rw [hR₂, ← Real.exp_log (by positivity : (0 : ℝ) < ∑ z ∈ Z, ‖z‖ + 1)]
      exact Real.exp_le_exp.2 h2
    linarith
  -- the annulus minus `Z`
  set S : Set ℂ := {z : ℂ | R₀ ≤ ‖z‖ ∧ ‖z‖ ≤ R₂} \ ↑Z with hS
  have hSU : S ⊆ U := fun z hz => hR₀U z hz.1.1
  have hS0 : ∀ z ∈ S, piDs H u z ≠ 0 := by
    rintro z ⟨⟨h1, _⟩, hzZ⟩ h0
    rcases h1.lt_or_eq with h | h
    · exact hzZ ((hZ z).2 ⟨h, h0⟩)
    · exact hcirc z h.symm h0
  have hloop : ∀ ρ, 0 < ρ → (∀ t, ccwLoop ρ t ∈ U) → (∀ t, piDs H u (ccwLoop ρ t) ≠ 0) →
      ∃ m : ℤ, HasLoopWind (fun t => piDs H u (ccwLoop ρ t)) m := by
    intro ρ _ hmem hnz
    exact exists_hasLoopWind _ (hpc.comp_continuous (by unfold ccwLoop; fun_prop) hmem)
      (fun t => by
        have : ccwLoop ρ (t + 1) = ccwLoop ρ t := by
          unfold ccwLoop
          have h : ((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I =
              ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
            push_cast; ring
          rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        simp only [this]) hnz
  have hnorm : ∀ ρ t, 0 < ρ → ‖ccwLoop ρ t‖ = ρ := by
    intro ρ t hρ
    unfold ccwLoop
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- windings on the two boundary circles
  obtain ⟨m₀, hm₀⟩ := hloop R₀ hR₀0 (fun t => hR₀U _ (hnorm R₀ t hR₀0).ge)
    (fun t => hcirc _ (hnorm R₀ t hR₀0))
  have hgt : ∀ t, piDs H u (ccwLoop R₂ t) ≠ 0 := fun t => by
    refine hS0 _ ⟨⟨?_, ?_⟩, fun hz => ?_⟩
    · rw [hnorm R₂ t hR₂0]; exact hR₀₂.le
    · rw [hnorm R₂ t hR₂0]
    · have := hZR₂ _ hz
      rw [hnorm R₂ t hR₂0] at this
      exact lt_irrefl _ this
  have hann := hasLoopWind_ccwLoop_annulus_eq_add_sum (piDs H u) Z R₀ R₂ hR₀0 hR₀₂
    (fun p hp => ⟨((hZ p).1 hp).1, hZR₂ p hp⟩) (hpc.mono hSU) hS0 m₀ hm₀ idx
    (fun p hp => by
      obtain ⟨-, r, hr, -, hw⟩ := hidx p hp
      exact ⟨r, hr, hw⟩)
  have hbig := hasLoopWind_cylInf_of_hasLoopWind_circle H hH J hJ U hU u huc hu0 hhol s₂
    (fun t => hR₀U _ (by rw [hnorm R₂ t hR₂0]; exact hR₀₂.le)) _ hann
  have hkbig := hs₁ s₂ hs₂s₁
  simp only [one_mul] at hkbig
  have hkeq := hasLoopWind_unique hbig hkbig
  have hsmall := hasLoopWind_cylInf_of_hasLoopWind_circle H hH J hJ U hU u huc hu0 hhol s₀
    (fun t => hR₀U _ (hnorm R₀ t hR₀0).ge) m₀ hm₀
  have harith : m₀ + 1 = k - ∑ z ∈ Z, idx z := by linarith
  rwa [harith] at hsmall

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real Uniformity

theorem lw_proj_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : H (proj H y) = 1 := by
  obtain ⟨r, ⟨hr0, hr1⟩, -⟩ := hH.2.1 y hy
  have e : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  unfold proj scaleToS
  rw [dif_pos e]
  exact (Classical.choose_spec e).2

theorem lw_joint {Y : Type*} [NormedAddCommGroup Y] (F : ℕ → ℂ → Y) (f : ℂ → Y) (S : Set ℂ)
    (hS : TendstoUniformlyOn F f atTop S) (γ : ℝ → ℂ) (hγ : ∀ t, γ t ∈ S)
    (hfc : Continuous fun t => f (γ t)) (x : ℝ) :
    Tendsto (fun y : ℕ × ℝ => F y.1 (γ y.2)) (atTop ×ˢ 𝓝 x) (𝓝 (f (γ x))) := by
  have h1 : TendstoUniformly (fun k t => F k (γ t)) (fun t => f (γ t)) atTop := by
    rw [← tendstoUniformlyOn_univ]
    have := hS.comp γ
    have e : γ ⁻¹' S = Set.univ := Set.eq_univ_of_forall hγ
    rw [e] at this
    exact this
  have h2 := tendstoLocallyUniformly_iff_forall_tendsto.1 h1.tendstoLocallyUniformly x
  have h3 : Tendsto (fun y : ℕ × ℝ => f (γ y.2)) (atTop ×ˢ 𝓝 x) (𝓝 (f (γ x))) :=
    (hfc.tendsto x).comp tendsto_snd
  exact h3.congr_uniformity h2

theorem lw_re_pos (a g : ℂ) (m : ℝ) (ha : m ≤ ‖a‖) (hd : ‖g - a‖ < m) :
    0 < (starRingEnd ℂ g * a).re := by
  set d := g - a with hd'
  have hg : g = a + d := by rw [hd']; ring
  have hm : 0 < m := (norm_nonneg _).trans_lt hd
  have e : starRingEnd ℂ a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : (starRingEnd ℂ g * a).re = ‖a‖ ^ 2 + (starRingEnd ℂ d * a).re := by
    rw [hg, map_add, add_mul, e, Complex.add_re, Complex.ofReal_re]
  have h3 : |(starRingEnd ℂ d * a).re| ≤ ‖d‖ * ‖a‖ := by
    have := Complex.abs_re_le_norm (starRingEnd ℂ d * a)
    rwa [norm_mul, RCLike.norm_conj] at this
  rw [e2]
  have h4 := (abs_le.1 h3).1
  nlinarith [norm_nonneg a, norm_nonneg d]

theorem lw_liouville_continuous : Continuous fun q : V 1 × V 1 => liouville q.1 q.2 := by
  have e : (fun q : V 1 × V 1 => liouville q.1 q.2) =
      fun q => ZCS.omegaL q.1 q.2 / 2 := by
    funext q
    rw [ZCS.omegaL_apply]
    rfl
  rw [e]
  exact ((ZCS.omegaL.continuous.comp continuous_fst).clm_apply continuous_snd).div_const _

theorem lw_xi_tendsto (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {ι : Type*} (l : Filter ι)
    (X Y : V 1) (x y : ι → V 1) (hx : Tendsto x l (𝓝 X)) (hy : Tendsto y l (𝓝 Y)) (hX : H X = 1) :
    Tendsto (fun i => xiCoordC H (x i) (y i)) l (𝓝 (xiCoordC H X Y)) := by
  have hc : ContinuousAt (fun q : V 1 × V 1 => xiCoordC H q.1 q.2) (X, Y) :=
    continuousAt_xiCoordC_prod H hH hX
  exact Tendsto.comp (f := fun i => (x i, y i)) hc (hx.prodMk_nhds hy)

theorem lw_piXi_tendsto (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {ι : Type*} (l : Filter ι)
    (X D : V 1) (x d : ι → V 1) (hx : Tendsto x l (𝓝 X)) (hd : Tendsto d l (𝓝 D))
    (hS : ∀ i, x i ∈ energySurface H) (hX : H X = 1) :
    Tendsto (fun i => piXi H (x i) (d i)) l (𝓝 (piXi H X D)) := by
  obtain ⟨Lip, hLip⟩ := exists_lipschitzOnWith_reeb H hH
  have hcw : ContinuousWithinAt (reeb H) (energySurface H) X := hLip.continuousOn X hX
  have hin : Tendsto x l (𝓝[energySurface H] X) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hS⟩
  have hreeb : Tendsto (fun i => reeb H (x i)) l (𝓝 (reeb H X)) := hcw.tendsto.comp hin
  have hLv : Tendsto (fun i => liouville (x i) (d i)) l (𝓝 (liouville X D)) :=
    Tendsto.comp (f := fun i => (x i, d i)) (lw_liouville_continuous.tendsto (X, D))
      (hx.prodMk_nhds hd)
  have hsmul : Tendsto (fun i => liouville (x i) (d i) • reeb H (x i)) l
      (𝓝 (liouville X D • reeb H X)) := hLv.smul hreeb
  exact hd.sub hsmul

/-- `piDs` converges locally uniformly along a loop. -/
theorem lw_tendsto_piDs (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hUo : IsOpen U)
    (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J U w) (u : ℕ → ℂ → V 1)
    (hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k)) (c : ℕ → ℝ) (hcpos : ∀ k, 0 < c k)
    (hconv : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • u k z) w U)
    (L : ℝ → ℂ) (hLc : Continuous L) (S : Set ℂ) (hSc : IsCompact S) (hSU : S ⊆ U)
    (hLS : ∀ t, L t ∈ S) :
    TendstoLocallyUniformly (fun k t => piDs H (u k) (L t)) (fun t => piDs H w (L t)) atTop := by
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hLU : ∀ t, L t ∈ U := fun t => hSU (hLS t)
  have hV : ∀ j, ContDiffOn ℝ ∞ (fun z => c j • u j z) U ∧ ∀ z ∈ U, c j • u j z ≠ 0 := fun j =>
    ⟨((lh_smul H hH J hJ Set.univ isOpen_univ (u j) (hfe j) (c j) (hcpos j)).1.1).mono
        (Set.subset_univ _), fun z _ => smul_ne_zero (hcpos j).ne' ((hfe j).2.1 z trivial)⟩
  have hPk' : ∀ k, (fun z => proj H (c k • u k z)) = fun z => proj H (u k z) := fun k =>
    funext fun z => (proj_aCoord_smul_aux H hH _ (hcpos k) _ ((hfe k).2.1 z trivial)).1
  have hcv : JHolomorphic.TendstoCInftyLocOn (fun k z => proj H (u k z)) (fun z => proj H (w z)) U := by
    have h := tendstoCInftyLocOn_comp (X := ℂ) (Y := V 1) (Z := V 1) hUo
      (isOpen_ne : IsOpen {y : V 1 | y ≠ 0}) (fun k z => c k • u k z) w (fun _ => proj H) (proj H)
      (fun j => (hV j).1) hw.1 (fun _ => hprojs) hprojs (fun j z hz => (hV j).2 z hz)
      (fun z hz => hw.2.1 z hz) hconv (lh_const _ _)
    have e : (fun k => proj H ∘ fun z => c k • u k z) = fun k z => proj H (u k z) :=
      funext fun k => hPk' k
    rw [e] at h
    exact h
  have A₀ : TendstoUniformlyOn (fun k z => proj H (u k z)) (fun z => proj H (w z)) atTop S := by
    have h0 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℂ) (V 1)
      (fun _ => 0)).uniformContinuous.comp_tendstoUniformlyOn (hcv S hSU hSc 0)
    have h1 : TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ 0 (fun z => proj H (u k z)) z (fun _ => 0))
        (fun z => iteratedFDeriv ℝ 0 (fun z => proj H (w z)) z (fun _ => 0)) atTop S := h0
    simpa only [iteratedFDeriv_zero_apply] using h1
  have A₁ : TendstoUniformlyOn (fun k z => fderiv ℝ (fun z => proj H (u k z)) z 1)
      (fun z => fderiv ℝ (fun z => proj H (w z)) z 1) atTop S := by
    have h0 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℂ) (V 1)
      (fun _ => 1)).uniformContinuous.comp_tendstoUniformlyOn (hcv S hSU hSc 1)
    have h1 : TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ 1 (fun z => proj H (u k z)) z (fun _ => 1))
        (fun z => iteratedFDeriv ℝ 1 (fun z => proj H (w z)) z (fun _ => 1)) atTop S := h0
    simpa only [iteratedFDeriv_one_apply] using h1
  have hpc : ContDiffOn ℝ ∞ (fun z => proj H (w z)) U :=
    hprojs.comp hw.1 (fun z hz => hw.2.1 z hz)
  have hpLc : Continuous fun t => proj H (w (L t)) := hpc.continuousOn.comp_continuous hLc hLU
  have hdLc : Continuous fun t => fderiv ℝ (fun z => proj H (w z)) (L t) 1 :=
    ((hpc.continuousOn_fderiv_of_isOpen hUo (by simp)).clm_apply
      continuousOn_const).comp_continuous hLc hLU
  have hfc : Continuous fun t => piDs H w (L t) :=
    (continuousOn_piDs H hH _ hUo w hw.1 hw.2.1).comp_continuous hLc hLU
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have hx := lw_joint (fun k z => proj H (u k z)) (fun z => proj H (w z)) S A₀ L hLS hpLc x
  have hd := lw_joint (fun k z => fderiv ℝ (fun z => proj H (u k z)) z 1)
    (fun z => fderiv ℝ (fun z => proj H (w z)) z 1) S A₁ L hLS hdLc x
  have hXS : H (proj H (w (L x))) = 1 := lw_proj_mem H hH _ (hw.2.1 _ (hLU x))
  have hpi := lw_piXi_tendsto H hH _ _ _ _ _ hx hd
    (fun y => lw_proj_mem H hH _ ((hfe y.1).2.1 _ trivial)) hXS
  have hG := lw_xi_tendsto H hH _ _ _ _ _ hx hpi hXS
  have hG' : Tendsto (fun y : ℕ × ℝ => piDs H (u y.1) (L y.2)) (atTop ×ˢ 𝓝 x)
      (𝓝 (piDs H w (L x))) := hG
  have hF : Tendsto (fun y : ℕ × ℝ => piDs H w (L y.2)) (atTop ×ˢ 𝓝 x) (𝓝 (piDs H w (L x))) :=
    (hfc.tendsto x).comp tendsto_snd
  exact (hF.prodMk_nhds hG').mono_right (nhds_le_uniformity _)

theorem hasWindInfAt_one_of_tendstoCInftyLocOn_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (K : Set (V 1)) (γ : ℝ)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (Γ : Finset ℂ) (hΓ : ∀ z ∈ Γ, ‖z‖ ≤ 1) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (hconv : JHolomorphic.TendstoCInftyLocOn
      (fun k z => Real.exp (-(2 * aCoord H (u k 2))) • u k z) w (↑Γ)ᶜ)
    (hinf : IsNondegenerateEnd H w cylInf P 1) (hpos : dlambdaEnergy H (↑Γ)ᶜ w ≠ 0) :
    HasWindInfAt H w cylInf 1 1 := by
  classical
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  set c : ℕ → ℝ := fun k => Real.exp (-(2 * aCoord H (u k 2))) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  have hfast : ∀ k, IsFastPlane H J (u k) := fun k => (hu k).1
  have hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k) := fun k => (hu k).1.1
  -- `piDs` of the limit is not identically zero
  have hne : ∃ z ∉ Γ, piDs H w z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hpos
    unfold dlambdaEnergy
    rw [setLIntegral_congr_fun (g := fun _ => 0) hUo.measurableSet ?_]
    · simp
    · intro z hz
      have hzΓ : z ∉ Γ := fun h => hz (Finset.mem_coe.2 h)
      refine ENNReal.ofReal_eq_zero.2 (not_lt.1 fun h => ?_)
      exact (piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ _ hUo w hw.2.1 hw.2.2.1 hz).2 h
        (hcon z hzΓ)
  obtain ⟨Z, hZ, -, -⟩ := wcm_zeros H hH J hJ Γ w hw P hinf hne 2
    (fun z hz => (hΓ z hz).trans_lt (by norm_num))
  set R₁ : ℝ := max 2 (∑ z ∈ Z, ‖z‖) with hR₁
  have hR₁2 : 2 ≤ R₁ := le_max_left _ _
  have hzf : ∀ z : ℂ, R₁ < ‖z‖ → piDs H w z ≠ 0 := by
    intro z hz h0
    have hzZ := (hZ z).2 ⟨(hR₁2.trans_lt hz), h0⟩
    have h1 := Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _) hzZ
    have h2 : ∑ z ∈ Z, ‖z‖ ≤ R₁ := le_max_right _ _
    linarith
  have hmem : ∀ z : ℂ, R₁ < ‖z‖ → z ∈ ((↑Γ)ᶜ : Set ℂ) := by
    intro z hz hzΓ
    have := hΓ z (Finset.mem_coe.1 hzΓ)
    linarith
  have hk : ∀ ρ > R₁, HasLoopWind (fun t => piDs H w (ccwLoop ρ t)) 0 := by
    intro ρ hρ
    have hρ0 : 0 < ρ := by linarith
    set L : ℝ → ℂ := ccwLoop ρ with hL
    have hLc : Continuous L := (lh_ccw_contDiff ρ).continuous
    have hLn : ∀ t, ‖L t‖ = ρ := fun t => lh_ccw_norm ρ t hρ0
    have hLU : ∀ t, L t ∈ ((↑Γ)ᶜ : Set ℂ) := fun t => hmem _ (by rw [hLn t]; exact hρ)
    set f : ℝ → ℂ := fun t => piDs H w (L t) with hf
    set g : ℕ → ℝ → ℂ := fun k t => piDs H (u k) (L t) with hg
    have hfc : Continuous f :=
      (continuousOn_piDs H hH _ hUo w hw.1 hw.2.1).comp_continuous hLc hLU
    have hfper : Function.Periodic f 1 := fun t => by
      simp only [hf, hL, lh_ccw_periodic ρ t]
    have hgper : ∀ k, Function.Periodic (g k) 1 := fun k t => by
      simp only [hg, hL, lh_ccw_periodic ρ t]
    have hf0 : ∀ t, f t ≠ 0 := fun t => hzf _ (by rw [hLn t]; exact hρ)
    have ghas : ∀ k, HasLoopWind (g k) 0 := by
      intro k
      have h := hasLoopWind_ccwLoop_eq_sum (piDs H (u k)) ∅ 0 ρ hρ0 (by simp)
        ((continuousOn_piDs H hH Set.univ isOpen_univ (u k) (hfe k).1
          (fun z hz => (hfe k).2.1 z hz)).mono (Set.subset_univ _))
        (fun z _ => piDs_ne_zero_of_isFastPlane H hH J hJ _ (hfast k) z) (fun _ => 0) (by simp)
      simpa only [zero_add, Finset.sum_empty] using h
    have hloc : TendstoLocallyUniformly g f atTop :=
      lw_tendsto_piDs H hH J hJ _ hUo w hw u hfe c hcpos hconv L hLc (sphere 0 ρ)
        (isCompact_sphere 0 ρ)
        (fun z hz => hmem z (by rw [mem_sphere_zero_iff_norm.1 hz]; exact hρ))
        (fun t => mem_sphere_zero_iff_norm.2 (hLn t))
    have hunO : TendstoUniformlyOn g f atTop (Set.Icc 0 1) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).1
        hloc.tendstoLocallyUniformlyOn
    have hun : TendstoUniformly g f atTop :=
      tendstoUniformly_of_periodic_aux g f hgper hfper hunO
    -- a lower bound
    obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
      ⟨0, by simp⟩ hfc.norm.continuousOn
    have hm : 0 < ‖f t₀‖ := norm_pos_iff.2 (hf0 t₀)
    have hmin : ∀ t, ‖f t₀‖ ≤ ‖f t‖ := by
      intro t
      obtain ⟨y, hy, hyt⟩ := hfper.exists_mem_Ico₀ one_pos t
      rw [hyt]
      refine ht₀ ⟨hy.1, ?_⟩
      exact hy.2.le
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformly_iff.1 hun _ hm).exists
    refine hasLoopWind_of_re_conj_mul_pos (ghas k) hfc hfper fun t => ?_
    refine lw_re_pos _ _ _ (hmin t) ?_
    have := hk t
    rwa [dist_comm, dist_eq_norm] at this
  have := hasWindInfAt_cylInf_of_hasLoopWind H hH J hJ _ hUo w hw.1 hw.2.1 hw.2.2.1 R₁ hmem 0 hk
  simpa using this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hUo : IsOpen U)
    (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J U w) (u : ℕ → ℂ → V 1)
    (hfe : ∀ k, IsFiniteEnergyCurve H J Set.univ (u k)) (c : ℕ → ℝ) (hcpos : ∀ k, 0 < c k)
    (hconv : JHolomorphic.TendstoCInftyLocOn (fun k z => c k • u k z) w U)
    (L : ℝ → ℂ) (hLc : Continuous L) (S : Set ℂ) (hSc : IsCompact S) (hSU : S ⊆ U)
    (hLS : ∀ t, L t ∈ S) :
    TendstoLocallyUniformly (fun k t => piDs H (u k) (L t)) (fun t => piDs H w (L t)) atTop :=
  lw_tendsto_piDs H hH J hJ U hUo w hw u hfe c hcpos hconv L hLc S hSc hSU hLS
