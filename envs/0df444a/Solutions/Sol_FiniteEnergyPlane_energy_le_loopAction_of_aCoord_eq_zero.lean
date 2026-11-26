-- Prove2me | solution 1 for FiniteEnergyPlane.energy_le_loopAction_of_aCoord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T20:14:37.811067+00:00
-- url     : https://prove2.me/submissions/6349f0dc-7ea2-4578-b7f4-4db21f803995

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_loopAction_ccwLoop_eq_dlambdaEnergy
import Theorems.Thm_FiniteEnergyPlane_plane_asymptotics
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg_of_isJHolomorphicOn

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology

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

/-- The boundary term of a smooth map `w` on the circle of radius `r`. -/
noncomputable def buBdry {n : ℕ} (w : ℂ → V n) (r : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
    omegaL (w (circleMap 0 r θ)) (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))

theorem bu_continuous_dens {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) :
    Continuous (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  simp_rw [← omegaL_apply]
  exact (omegaL.continuous₂).comp₂ (hd.clm_apply continuous_const)
    (hd.clm_apply continuous_const)

theorem bu_continuous_bdry {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (r : ℝ) :
    Continuous (fun θ => omegaL (w (circleMap 0 r θ))
      (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  have hc : Continuous (circleMap 0 r) := continuous_circleMap 0 r
  exact (omegaL.continuous₂).comp₂ (hw.continuous.comp hc)
    ((hd.comp hc).clm_apply (hc.mul continuous_const))

theorem bu_annulus_eq {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ z in ball 0 b \ ball 0 a, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      buBdry w b - buBdry w a := by
  have hc := bu_continuous_dens w hw
  rw [setIntegral_annulus_eq_integral_circleMap ha hab hc.continuousOn]
  have hS := integral_mul_integral_bilin_circleMap_eq (omegaL (n := n))
    (fun x y => by rw [omegaL_apply, omegaL_apply, omega0_antisymm]) isOpen_univ
    (hw.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top)) ha hab (fun _ _ _ => Set.mem_univ _) 0
  simp only [sub_zero, omegaL_apply] at hS
  simp only [smul_eq_mul, buBdry, omegaL_apply]
  exact hS

/-- Stokes on a disc for `ω₀(∂ₛW, ∂ₜW)`, `W` smooth. -/
theorem bu_ball_eq {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (R : ℝ) (hR : 0 < R) :
    ∫ z in ball 0 R, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) = buBdry w R := by
  set dens : ℂ → ℝ := fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) with hdensdef
  have hc : Continuous dens := bu_continuous_dens w hw
  have hint : ∀ r, IntegrableOn dens (ball 0 r) :=
    fun r => (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      ball_subset_closedBall
  have key : ∀ a, 0 < a → a ≤ R →
      (∫ z in ball 0 R, dens z) - buBdry w R = (∫ z in ball 0 a, dens z) - buBdry w a := by
    intro a ha haR
    have h1 := setIntegral_sdiff (μ := volume) measurableSet_ball (hint R) (ball_subset_ball haR)
    have h2 := bu_annulus_eq w hw ha haR
    rw [h2] at h1
    linarith
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hw.continuous_fderiv (by simp)).continuousOn
  have hM2n : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 (mem_closedBall_self zero_le_one))
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (mem_closedBall_self zero_le_one))
  set K := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hK
  have hKn : 0 ≤ K := norm_nonneg (omegaL (n := n))
  have hbd : ∀ a, 0 < a → a ≤ 1 → a ≤ R →
      |(∫ z in ball 0 R, dens z) - buBdry w R| ≤
        K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a := by
    intro a ha ha1 haR
    rw [key a ha haR]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · have hvol : (volume : Measure ℂ).real (ball 0 a) = a ^ 2 * π := by
        simp [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal ha.le]
      rw [← hvol, ← Real.norm_eq_abs]
      refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top ?_
      intro z hz
      have hz1 : z ∈ closedBall (0 : ℂ) 1 :=
        ball_subset_closedBall (ball_subset_ball ha1 hz)
      have hb := hM2 z hz1
      simp only [hdensdef, ← omegaL_apply]
      refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
      have e1 : ‖fderiv ℝ w z 1‖ ≤ M2 :=
        ((fderiv ℝ w z).le_opNorm 1).trans (by simpa using hb)
      have e2 : ‖fderiv ℝ w z Complex.I‖ ≤ M2 :=
        ((fderiv ℝ w z).le_opNorm _).trans (by simpa using hb)
      exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hKn) e2 (norm_nonneg _) (mul_nonneg hKn hM2n)
    · rw [buBdry, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
      have hθ : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖omegaL (w (circleMap 0 a θ))
          (fderiv ℝ w (circleMap 0 a θ) (circleMap 0 a θ * Complex.I))‖ ≤ K * M1 * (M2 * a) := by
        intro θ _
        have hz1 : circleMap 0 a θ ∈ closedBall (0 : ℂ) 1 := by
          rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos ha]; exact ha1
        refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
        have e1 := hM1 _ hz1
        have e2 : ‖fderiv ℝ w (circleMap 0 a θ) (circleMap 0 a θ * Complex.I)‖ ≤ M2 * a := by
          refine ((fderiv ℝ w _).le_opNorm _).trans ?_
          rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos ha]
          exact mul_le_mul_of_nonneg_right (hM2 _ hz1) ha.le
        gcongr
      have := intervalIntegral.norm_integral_le_of_norm_le_const hθ
      rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
      nlinarith [this]
  have hlim : Tendsto (fun a : ℝ => K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a)
      (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (fun a : ℝ => K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a) := by
      fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      |(∫ z in ball 0 R, dens z) - buBdry w R| ≤
        K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hR)] with a ha
    exact hbd a ha.1 (ha.2.le.trans (min_le_left _ _)) (ha.2.le.trans (min_le_right _ _))
  have h0 := ge_of_tendsto hlim hev
  have := abs_nonneg ((∫ z in ball 0 R, dens z) - buBdry w R)
  have hz : (∫ z in ball 0 R, dens z) - buBdry w R = 0 := abs_eq_zero.1 (le_antisymm h0 this)
  linarith

theorem setIntegral_ball_omega0_fderiv_eq_aux {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (R : ℝ)
    (hR : 0 < R) :
    ∫ z in ball 0 R, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, omega0 (w (circleMap 0 R θ))
        (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) := by
  have h := bu_ball_eq w hw R hR
  simpa only [buBdry, omegaL_apply] using h

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Along the loops of a `C^∞`-converging family, the action integrand is eventually nonnegative. -/
theorem bu_eventually_nonneg {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (l : ℕ → ℝ → V n) (Q : ReebOrbit H) (hT : 0 < Q.T) (c : ℝ)
    (hconv : TendstoCInfty l (fun t => Q.x (Q.T * t + c))) :
    ∀ᶠ k in atTop, ∀ t, 0 ≤ liouville (l k t) (deriv (l k) t) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have hcpt := isCompact_energySurface H hH
  obtain ⟨A, hA⟩ := hcpt.exists_bound_of_continuousOn (f := fun x : V n => x) continuousOn_id
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn hK.continuousOn
  set Λ := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hΛ
  have hΛn : 0 ≤ Λ := norm_nonneg (omegaL (n := n))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (Q.mem 0))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (Q.mem 0))
  have hder : ∀ t, deriv (fun t => Q.x (Q.T * t + c)) t = Q.T • reeb H (Q.x (Q.T * t + c)) := by
    intro t
    have hin : HasDerivAt (fun t : ℝ => Q.T * t + c) Q.T t := by
      simpa using ((hasDerivAt_id t).const_mul Q.T).add_const c
    exact ((Q.hasDerivAt (Q.T * t + c)).scomp t hin).deriv
  -- `L` is the constant `‖T • reeb‖` bound
  set L := Q.T * B with hL
  have hL0 : 0 ≤ L := mul_nonneg hT.le hB0
  -- choose the tolerance
  obtain ⟨ε, hε, hεs⟩ : ∃ ε > 0, Λ * ε * (L + ε) + Λ * A * ε < 2 * Q.T := by
    have hc : Continuous (fun ε : ℝ => Λ * ε * (L + ε) + Λ * A * ε) := by fun_prop
    have h0 : (fun ε : ℝ => Λ * ε * (L + ε) + Λ * A * ε) 0 < 2 * Q.T := by simpa using hT
    have hev := hc.continuousAt.eventually (gt_mem_nhds h0)
    obtain ⟨ε, hε1, hε2⟩ := (hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))) |>.exists
    exact ⟨ε, hε2, hε1⟩
  have h0 := Metric.tendstoUniformly_iff.1 (hconv 0) ε hε
  have h1 := Metric.tendstoUniformly_iff.1 (hconv 1) ε hε
  filter_upwards [h0, h1] with k hk0 hk1 t
  have ht0 := hk0 t
  have ht1 := hk1 t
  simp only [iteratedDeriv_zero, iteratedDeriv_one, hder] at ht0 ht1
  rw [dist_comm, dist_eq_norm] at ht0 ht1
  set x := Q.x (Q.T * t + c) with hx
  have hxS : x ∈ energySurface H := Q.mem _
  have hR := (reeb_spec H hH x hxS).2.1
  have hR2 : omegaL x (Q.T • reeb H x) = 2 * Q.T := by
    have h := hR
    rw [liouville, ← omegaL_apply] at h
    rw [map_smul, smul_eq_mul]
    have : omegaL x (reeb H x) = 2 := by linarith
    rw [this]; ring
  set a := l k t with ha
  set b := deriv (l k) t with hb
  set y := Q.T • reeb H x with hy
  have hby : ‖y‖ ≤ L := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos hT, hL]
    exact mul_le_mul_of_nonneg_left (hB _ hxS) hT.le
  have hbb : ‖b‖ ≤ L + ε := by
    have : b = y + (b - y) := by abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add hby ht1.le)
  have hsplit : omegaL a b = omegaL x y + (omegaL (a - x) b + omegaL x (b - y)) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    ring
  have he1 : |omegaL (a - x) b| ≤ Λ * ε * (L + ε) := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht0.le hΛn) hbb (norm_nonneg _)
      (mul_nonneg hΛn hε.le)
  have he2 : |omegaL x (b - y)| ≤ Λ * A * ε := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA _ hxS) hΛn) ht1.le (norm_nonneg _)
      (mul_nonneg hΛn hA0)
  have hfin : 0 ≤ omegaL a b := by
    rw [hsplit, hR2]
    have := neg_abs_le (omegaL (a - x) b)
    have := neg_abs_le (omegaL x (b - y))
    linarith
  rw [liouville, ← omegaL_apply]
  linarith

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The loop action integrand in terms of the `ω₀`-form on the circle. -/
theorem bu_liouville_loop {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hw : ContDiff ℝ ∞ (fun z => proj H (u z))) (R t : ℝ) :
    liouville (loopInS H u (ccwLoop R) t) (deriv (loopInS H u (ccwLoop R)) t) =
      π * omegaL (proj H (u (circleMap 0 R (2 * π * t))))
        (fderiv ℝ (fun z => proj H (u z)) (circleMap 0 R (2 * π * t))
          (circleMap 0 R (2 * π * t) * Complex.I)) := by
  set w := fun z => proj H (u z) with hwdef
  have hcm : ∀ t : ℝ, ccwLoop R t = circleMap 0 R (2 * π * t) := by
    intro t; simp [ccwLoop, circleMap]
  have hloop : loopInS H u (ccwLoop R) = fun t => w (circleMap 0 R (2 * π * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hh : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have h1 := (hasDerivAt_circleMap 0 R (2 * π * t)).scomp t hh
  have h2 := ((hw.differentiable (by simp)) (circleMap 0 R (2 * π * t))).hasFDerivAt
  have h3 := h2.comp_hasDerivAt t h1
  have hder : deriv (loopInS H u (ccwLoop R)) t =
      (2 * π) • fderiv ℝ w (circleMap 0 R (2 * π * t)) (circleMap 0 R (2 * π * t) * Complex.I) := by
    rw [hloop]
    rw [show (fun t => w (circleMap 0 R (2 * π * t))) =
      w ∘ (circleMap 0 R ∘ fun t => 2 * π * t) from rfl, h3.deriv, ← map_smul]
  rw [hder, hloop]
  simp only [liouville, ← omegaL_apply, map_smul, smul_eq_mul]
  ring

theorem bu_loopAction_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hw : ContDiff ℝ ∞ (fun z => proj H (u z))) (R : ℝ) :
    loopAction H u (ccwLoop R) = buBdry (fun z => proj H (u z)) R := by
  unfold loopAction
  simp_rw [bu_liouville_loop H u hw R]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun θ => omegaL (proj H (u (circleMap 0 R θ)))
      (fderiv ℝ (fun z => proj H (u z)) (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)))
      (by positivity)]
  simp only [mul_zero, mul_one, smul_eq_mul, buBdry]
  rw [← mul_assoc]
  congr 1
  field_simp

/-- The energy density for `χ²` is the `ω₀`-density of `χ(a) • w`. -/
theorem bu_density_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (z : ℂ) (ha : DifferentiableAt ℝ (fun z => aCoord H (u z)) z)
    (hw : DifferentiableAt ℝ (fun z => proj H (u z)) z) :
    omega0 (fderiv ℝ (fun z => χ (aCoord H (u z)) • proj H (u z)) z 1)
        (fderiv ℝ (fun z => χ (aCoord H (u z)) • proj H (u z)) z Complex.I) =
      energyDensity H (fun s => χ s ^ 2) u z := by
  have hca : HasFDerivAt (fun y => χ (aCoord H (u y)))
      (deriv χ (aCoord H (u z)) • fderiv ℝ (fun y => aCoord H (u y)) z) z :=
    (hχ (aCoord H (u z))).hasDerivAt.comp_hasFDerivAt z ha.hasFDerivAt
  have hW : HasFDerivAt (fun z => χ (aCoord H (u z)) • proj H (u z)) _ z :=
    hca.smul hw.hasFDerivAt
  rw [hW.fderiv]
  have hφ : deriv (fun s => χ s ^ 2) (aCoord H (u z)) =
      2 * χ (aCoord H (u z)) * deriv χ (aCoord H (u z)) := by
    have h2 : HasDerivAt (fun s => χ s ^ 2)
        ((2 : ℕ) * χ (aCoord H (u z)) ^ (2 - 1) * deriv χ (aCoord H (u z))) (aCoord H (u z)) :=
      (hχ (aCoord H (u z))).hasDerivAt.pow 2
    rw [h2.deriv]; push_cast; ring
  simp only [energyDensity, ds, dt, liouville]
  rw [hφ]
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  simp only [← omegaL_apply, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  have hanti : ∀ v : V n, omegaL v (w z) = -omegaL (w z) v := by
    intro v; rw [omegaL_apply, omegaL_apply, omega0_antisymm]
  rw [h0]
  simp only [hwdef] at hanti ⊢
  rw [hanti]
  ring

/-- On the circle, the boundary form of `χ(a) • w` is `χ(a)²` times that of `w`. -/
theorem bu_bdry_form {n : ℕ} (a : ℂ → ℝ) (w : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (z v : ℂ) (ha : DifferentiableAt ℝ a z) (hw : DifferentiableAt ℝ w z) :
    omegaL (χ (a z) • w z) (fderiv ℝ (fun z => χ (a z) • w z) z v) =
      χ (a z) ^ 2 * omegaL (w z) (fderiv ℝ w z v) := by
  have hca : HasFDerivAt (fun y => χ (a y)) (deriv χ (a z) • fderiv ℝ a z) z :=
    (hχ (a z)).hasDerivAt.comp_hasFDerivAt z ha.hasFDerivAt
  have hW : HasFDerivAt (fun z => χ (a z) • w z) _ z := hca.smul hw.hasFDerivAt
  rw [hW.fderiv]
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, map_add, map_smul, h0]
  ring

/-- The Hofer energy of a nonconstant finite-energy plane equals its `dλ`-energy. -/
theorem energy_univ_eq_dlambdaEnergy_of_plane_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    energy H Set.univ u = dlambdaEnergy H Set.univ u := by
  obtain ⟨hnnφ, hnnd, hdle, -⟩ := energyDensity_nonneg H hH J hJ Set.univ isOpen_univ u hu
  refine le_antisymm ?_ hdle
  obtain ⟨hpos, -, -, hseq⟩ := plane_asymptotics H hH J hJ u hu hnc
  have htop : dlambdaEnergy H Set.univ u ≠ ⊤ := by
    intro h; rw [h] at hpos; simp at hpos
  set T := (dlambdaEnergy H Set.univ u).toReal with hTdef
  have hTe : dlambdaEnergy H Set.univ u = ENNReal.ofReal T := (ENNReal.ofReal_toReal htop).symm
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hw : ContDiff ℝ ∞ w :=
    contDiffOn_univ.1 (hprojs.comp hu.1 (fun z _ => hu.2.1 z (Set.mem_univ _)))
  have ha : ContDiff ℝ ∞ a :=
    contDiffOn_univ.1 (haCs.comp hu.1 (fun z _ => hu.2.1 z (Set.mem_univ _)))
  -- radii along which the action integrand is nonnegative
  obtain ⟨φ₀, hφ₀, Q, hQT, c, hconv⟩ := hseq (fun k => (k : ℝ)) tendsto_natCast_atTop_atTop
  have hQpos : 0 < Q.T := Q.T_pos
  have hevpos := bu_eventually_nonneg H hH _ Q hQpos c hconv
  have hφt : Tendsto (fun k => ((φ₀ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ₀.tendsto_atTop
  refine iSup₂_le fun φ hφ => ?_
  -- it suffices to bound all `(1 + ε)`-multiples
  have main : ∀ ε : ℝ, 0 < ε → ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H φ u z) ≤
      ENNReal.ofReal ((1 + ε) * T) := by
    intro ε hε
    set χ : ℝ → ℝ := fun s => Real.sqrt (φ s + ε) with hχdef
    have hφε : ∀ s, 0 < φ s + ε := fun s => by linarith [(hφ.2.2 s).1]
    have hχ : ContDiff ℝ ∞ χ :=
      (hφ.1.add contDiff_const).sqrt fun s => (hφε s).ne'
    have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
    have hχ2 : ∀ s, χ s ^ 2 = φ s + ε := fun s => Real.sq_sqrt (hφε s).le
    set W : ℂ → V n := fun z => χ (a z) • w z with hWdef
    have hW : ContDiff ℝ ∞ W := (hχ.comp ha).smul hw
    have had : ∀ z, DifferentiableAt ℝ a z := fun z => (ha.differentiable (by simp)) z
    have hwd : ∀ z, DifferentiableAt ℝ w z := fun z => (hw.differentiable (by simp)) z
    have hfun : (fun s => χ s ^ 2) = fun s => φ s + ε := funext hχ2
    have hden : ∀ z, omega0 (fderiv ℝ W z 1) (fderiv ℝ W z Complex.I) =
        energyDensity H (fun s => φ s + ε) u z := fun z => by
      rw [← hfun]
      exact bu_density_eq H u χ hχd z (had z) (hwd z)
    -- comparison with the density of `φ + ε`
    have hcmp : ∀ z, energyDensity H φ u z ≤ energyDensity H (fun s => φ s + ε) u z := by
      intro z
      have hd : deriv (fun s => φ s + ε) (a z) = deriv φ (a z) := by simp
      have hnn := hnnd z (Set.mem_univ _)
      simp only [dlambdaDensity] at hnn
      simp only [energyDensity]
      rw [show deriv (fun s => φ s + ε) (aCoord H (u z)) = deriv φ (aCoord H (u z)) from hd]
      nlinarith [mul_nonneg hε.le hnn]
    -- the disc bound
    have hball : ∀ᶠ k in atTop, ∫⁻ z in ball 0 ((φ₀ k : ℕ) : ℝ),
        ENNReal.ofReal (energyDensity H φ u z) ≤ ENNReal.ofReal ((1 + ε) * T) := by
      filter_upwards [hevpos, hφt.eventually (eventually_gt_atTop (0 : ℝ))] with k hk hR0
      set R : ℝ := ((φ₀ k : ℕ) : ℝ) with hRdef
      have hposθ : ∀ θ, 0 ≤ omegaL (w (circleMap 0 R θ))
          (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) := by
        intro θ
        have h := hk (θ / (2 * π))
        rw [bu_liouville_loop H u hw R (θ / (2 * π))] at h
        have e : 2 * π * (θ / (2 * π)) = θ := by field_simp
        rw [e] at h
        exact nonneg_of_mul_nonneg_right h Real.pi_pos
      have hbdry : buBdry W R ≤ (1 + ε) * buBdry w R := by
        unfold buBdry
        rw [show (1 + ε) * ((1 / 2) * ∫ θ in (0 : ℝ)..2 * π, omegaL (w (circleMap 0 R θ))
            (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I))) =
            (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, (1 + ε) * omegaL (w (circleMap 0 R θ))
            (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) by
          rw [intervalIntegral.integral_const_mul]; ring]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine intervalIntegral.integral_mono_on (by positivity)
          ((bu_continuous_bdry W hW R).intervalIntegrable _ _)
          (((bu_continuous_bdry w hw R).const_mul _).intervalIntegrable _ _) fun θ _ => ?_
        have hform := bu_bdry_form a w χ hχd (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)
          (had _) (hwd _)
        rw [show W (circleMap 0 R θ) = χ (a (circleMap 0 R θ)) • w (circleMap 0 R θ) from rfl,
          show fderiv ℝ W (circleMap 0 R θ) = fderiv ℝ (fun z => χ (a z) • w z) (circleMap 0 R θ)
            from rfl, hform, hχ2]
        refine mul_le_mul_of_nonneg_right ?_ (hposθ θ)
        linarith [(hφ.2.2 (a (circleMap 0 R θ))).2]
      -- `buBdry w R` is the action of the circle
      have hact : buBdry w R ≤ T := by
        rw [← bu_loopAction_eq H u hw R, loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hu R hR0]
        exact ENNReal.toReal_mono htop (lintegral_mono_set (Set.subset_univ _))
      have hint : IntegrableOn (fun z => energyDensity H (fun s => φ s + ε) u z) (ball 0 R) := by
        have hc : Continuous (fun z => energyDensity H (fun s => φ s + ε) u z) := by
          simp_rw [← hden]
          exact bu_continuous_dens W hW
        exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
          ball_subset_closedBall
      have hφεadm : ∀ z, 0 ≤ energyDensity H (fun s => φ s + ε) u z := fun z =>
        (hnnφ φ hφ z (Set.mem_univ _)).trans (hcmp z)
      calc ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H φ u z)
          ≤ ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H (fun s => φ s + ε) u z) :=
            lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hcmp z)
        _ = ENNReal.ofReal (∫ z in ball 0 R, energyDensity H (fun s => φ s + ε) u z) :=
            (ofReal_integral_eq_lintegral_ofReal hint
              (Eventually.of_forall hφεadm)).symm
        _ ≤ ENNReal.ofReal ((1 + ε) * T) := by
            refine ENNReal.ofReal_le_ofReal ?_
            simp_rw [← hden]
            rw [bu_ball_eq W hW R hR0]
            exact hbdry.trans (mul_le_mul_of_nonneg_left hact (by linarith))
    -- exhaust by balls
    set μ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (energyDensity H φ u z))
      with hμdef
    have hμ : ∀ s : Set ℂ, MeasurableSet s →
        ∫⁻ z in s, ENNReal.ofReal (energyDensity H φ u z) = μ s := fun s hs =>
      (withDensity_apply _ hs).symm
    have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) (N : ℝ)) := fun i j hij =>
      ball_subset_ball (by exact_mod_cast hij)
    have hunion : ⋃ N : ℕ, ball (0 : ℂ) (N : ℝ) = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
    have hN : ∀ N : ℕ, (μ ∘ fun N : ℕ => ball (0 : ℂ) (N : ℝ)) N ≤ ENNReal.ofReal ((1 + ε) * T) := by
      intro N
      rw [Function.comp_apply, ← hμ _ measurableSet_ball]
      obtain ⟨k, hk1, hk2⟩ := (hball.and (hφt.eventually (eventually_ge_atTop (N : ℝ)))).exists
      exact (lintegral_mono_set (ball_subset_ball hk2)).trans hk1
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, ← hμ _ MeasurableSet.univ] at h
    exact le_of_tendsto' h hN
  -- let `ε → 0`
  rw [hTe]
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * T)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal T)) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * T)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun ε hε => main ε hε)

end FiniteEnergyPlane

/-! Basic identities for the symplectization of a star-shaped level (copied, renamed, from the
`ka_*` helpers of accepted solution a386257a). -/


set_option linter.unusedSimpArgs false

def ka_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def ka_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem ka_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((ka_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold ka_sig; split_ifs <;> rfl

theorem ka_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sig (ka_sig k) = k := by
  ext
  rw [ka_sig_val, ka_sig_val]
  split_ifs <;> omega

theorem ka_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn (ka_sig k) = - ka_sgn k := by
  unfold ka_sgn
  rw [ka_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem ka_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn k * ka_sgn k = 1 := by
  unfold ka_sgn; split_ifs <;> norm_num

def ka_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm ka_sig ka_sig_sig

theorem ka_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sigE n k = ka_sig k := rfl

theorem ka_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = ka_sgn k * v (ka_sig k) := by
  unfold j0 ka_sgn ka_sig
  split_ifs <;> simp

theorem ka_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [ka_j0_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  simp only [Pi.neg_apply]
  have := ka_sgn_sq k
  linear_combination (-(v k)) * this

theorem ka_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [ka_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ka_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [ka_j0_apply, Pi.add_apply]; ring

theorem ka_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [ka_j0_apply, Pi.sub_apply]; ring

theorem ka_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [ka_dot_comm, ka_dot_smul_right, ka_dot_comm]

theorem ka_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [ka_dot_comm, ka_dot_add_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [ka_dot_comm, ka_dot_sub_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem ka_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [ka_dot_comm, ka_dot_neg_right, ka_dot_comm]

theorem ka_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (ka_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [ka_sigE_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  ring

theorem ka_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [ka_dot_j0_left, ka_j0_j0, ka_dot_neg_right, neg_neg]

theorem ka_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := ka_dot_j0_left u u
  rw [ka_dot_comm] at this
  linarith

theorem ka_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem ka_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [ka_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [ka_dot_j0_j0, ka_fderiv_eq_dot, ka_dot_comm]

theorem ka_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [ka_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [ka_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, ka_fderiv_eq_dot, ka_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [ka_j0_smul, ka_j0_j0, ka_dot_smul_left, ka_dot_neg_left,
      ← ka_fderiv_eq_dot, hw]; ring

theorem ka_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [ka_j0_add, ka_dot_add_left]
theorem ka_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [ka_dot_add_right]
theorem ka_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [ka_j0_sub, ka_dot_sub_left]
theorem ka_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [ka_dot_sub_right]
theorem ka_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [ka_j0_smul, ka_dot_smul_left]
theorem ka_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [ka_dot_smul_right]
theorem ka_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [ka_dot_j0_left, ka_dot_comm]
theorem ka_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := ka_om_anti u u; linarith

theorem ka_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem ka_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem ka_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (ka_scale_spec H hH y hy)
  rw [h1, h2]

theorem ka_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y₀ hy₀
  set r := scaleToS H y₀
  set f : V n × ℝ → ℝ := fun p => H (p.2 • p.1) with hf
  have hfc : ContDiff ℝ ∞ f := hH.1.comp (ContDiff.smul contDiff_snd contDiff_fst)
  set u : V n × ℝ := (y₀, r)
  have cdf : ContDiffAt ℝ ∞ f u := hfc.contDiffAt
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- derivative
  have hg : HasFDerivAt (fun p : V n × ℝ => p.2 • p.1)
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀) u := by
    have h1 : HasFDerivAt (fun p : V n × ℝ => p.2) (ContinuousLinearMap.snd ℝ (V n) ℝ) u :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : V n × ℝ => p.1) (ContinuousLinearMap.fst ℝ (V n) ℝ) u :=
      hasFDerivAt_fst
    exact h1.smul h2
  have hHd : HasFDerivAt H (fderiv ℝ H (r • y₀)) (r • y₀) :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hfd : HasFDerivAt f ((fderiv ℝ H (r • y₀)).comp
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀)) u :=
    hHd.comp u hg
  have hpos : 0 < fderiv ℝ H (r • y₀) y₀ := by
    have := hH.2.2 (r • y₀) hHx
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr.le
  set c := fderiv ℝ H (r • y₀) y₀
  have hL1 : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ) 1 = c := by
    rw [hfd.fderiv]; simp [c]
  have if₂ : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
      rw [show c⁻¹ = c⁻¹ • (1:ℝ) by simp, map_smul, hL1, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, hL1]
      simp [inv_mul_cancel₀ hpos.ne']
  set ψ := ContDiffAt.implicitFunction cdf pn if₂
  have hψc : ContDiffAt ℝ ∞ ψ y₀ := ContDiffAt.contDiffAt_implicitFunction cdf pn if₂
  have hψ0 : ψ y₀ = r := ContDiffAt.implicitFunction_apply_self cdf pn if₂
  have hψeq := ContDiffAt.eventually_apply_implicitFunction cdf pn if₂
  have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y := by
    have := hψc.continuousAt.eventually (lt_mem_nhds (show (0:ℝ) < ψ y₀ by rw [hψ0]; exact hr))
    exact this
  have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  have hev : ψ =ᶠ[𝓝 y₀] scaleToS H := by
    filter_upwards [hψeq, hψpos, hne] with y h1 h2 h3
    have h1' : H (ψ y • y) = 1 := by
      have : f (y, ψ y) = f u := h1
      simp only [hf, u] at this
      rw [this, hHx]
    exact (ka_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm


theorem ka_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => ka_sgn k * v (ka_sig k) := by
    funext v; exact ka_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (ka_sig k))

theorem ka_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem ka_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (ka_dH_contDiff H hH).clm_apply contDiff_const

theorem ka_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := ka_j0_contDiff.comp (ka_grad_contDiff H hH)

theorem ka_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp ka_j0_contDiff).smul contDiff_const

theorem ka_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (ka_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (ka_hamVF_contDiff H hH.1).contDiffAt

theorem ka_scale_hasFDerivAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) :
    HasFDerivAt (scaleToS H)
      ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)) y := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hy
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  set r := scaleToS H y
  set x := proj H y
  have hxr : x = r • y := rfl
  set L := fderiv ℝ (scaleToS H) y
  have hm : HasFDerivAt (fun y' => scaleToS H y' • y') (r • ContinuousLinearMap.id ℝ (V n) +
      L.smulRight y) y := hd.hasFDerivAt.smul (hasFDerivAt_id y)
  have hHd : HasFDerivAt H (fderiv ℝ H x) x :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg := hHd.comp y hm
  have hev : (H ∘ fun y' => scaleToS H y' • y') =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hy] with y' hy'
    exact (ka_scale_spec H hH y' hy').2
  have h0 := hg.fderiv
  rw [hev.fderiv_eq, fderiv_fun_const] at h0
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hHx
  have hL : ∀ v, L v = -(r ^ 2 / fderiv ℝ H x x) * fderiv ℝ H x v := by
    intro v
    have := congrArg (fun T => T v) h0
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul] at this
    have hxy : fderiv ℝ H x y = fderiv ℝ H x x / r := by
      rw [hxr, map_smul, smul_eq_mul]; field_simp
    rw [hxy] at this
    field_simp
    field_simp at this
    linarith
  have : L = (-(r ^ 2 / fderiv ℝ H x x)) • fderiv ℝ H x := by
    ext1 v; rw [hL v]; rfl
  rw [← this]; exact hd.hasFDerivAt

theorem ka_hol_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
    (α β : V n →L[ℝ] ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B)) (hJP : ∀ w, P w → P (J' w))
    (hαA : α A = 1) (hαB : α B = 0) (hβA : β A = 0) (hβB : β B = 1)
    (hαP : ∀ w, P w → α w = 0) (hβP : ∀ w, P w → β w = 0)
    (hB : ∀ w, P w → omega0 B w = 0) (us ut : V n)
    (hhol : us + (α ut • B - β ut • A + J' (ut - α ut • A - β ut • B)) = 0) :
    α us = β ut ∧ α ut = - β us ∧
      omega0 (us - α us • A) (ut - α ut • A) =
        omega0 (ut - α ut • A - β ut • B) (J' (ut - α ut • A - β ut • B)) ∧
      (β us = 0 → β ut = 0 → ut - α ut • A - β ut • B = 0 → us = 0 ∧ ut = 0) := by
  set w := ut - α ut • A - β ut • B with hwdef
  have hPw : P w := hW ut
  have hPJw := hJP _ hPw
  have hs : us = -(α ut • B - β ut • A + J' w) := eq_neg_of_add_eq_zero_left hhol
  have e1 : α us = β ut := by
    rw [hs, map_neg, map_add, hαP _ hPJw]
    simp only [map_sub, map_smul, hαA, hαB, smul_eq_mul]; ring
  have e2 : β us = - α ut := by
    rw [hs, map_neg, map_add, hβP _ hPJw]
    simp only [map_sub, map_smul, hβA, hβB, smul_eq_mul]; ring
  have hus : us - α us • A = β us • B - J' w := by
    rw [e1, e2]; rw [hs]; module
  have hut : ut - α ut • A = β ut • B + w := by rw [hwdef]; module
  have hBB : omega0 B B = 0 := ka_om_self B
  have hJwB : omega0 (J' w) B = 0 := by rw [ka_om_anti, hB _ hPJw, neg_zero]
  refine ⟨e1, by linarith, ?_, ?_⟩
  · rw [hus, hut]
    simp only [ka_om_add_right, ka_om_sub_left, ka_om_smul_left, ka_om_smul_right,
      hBB, hB _ hPw, hJwB]
    rw [ka_om_anti (J' w) w]; ring
  · intro h1 h2 h3
    have hw0 : w = 0 := h3
    have hα : α ut = 0 := by linarith
    have hJ0 : J' w = 0 := by rw [hw0, map_zero]
    constructor
    · rw [hs, hJ0, h2, hα]; simp
    · have : ut = α ut • A + β ut • B + w := by rw [hwdef]; module
      rw [this, hα, h2, hw0]; simp

theorem ka_clm_complex_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (h1 : L 1 = 0) (hI : L Complex.I = 0) : L = 0 := by
  ext1 z
  have : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [this, map_add, map_smul, map_smul, h1, hI]; simp

theorem ka_cr {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
    dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := ka_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, ka_liouvilleCLM_apply]
    unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring
  -- derivatives
  have hS' := ka_scale_hasFDerivAt H hH y hz
  have ha' : HasFDerivAt (aCoord H) α y := by
    have h1 := (hS'.log hr.ne').const_mul (-1/2 : ℝ)
    have : (fun y => (-1/2 : ℝ) * Real.log (scaleToS H y)) = aCoord H := by
      funext y; unfold aCoord; ring
    rw [this] at h1
    have heq : α = ((-1 / 2 : ℝ) • (scaleToS H y)⁻¹ • -(scaleToS H y ^ 2 /
        (fderiv ℝ H (proj H y)) (proj H y)) • fderiv ℝ H (proj H y)) := by
      ext1 v
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hrdef, ← hxdef]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      field_simp
      exact mul_comm _ _
    rw [heq]; exact h1
  have hp' : HasFDerivAt (proj H) (r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A)) y := by
    have h1 := hS'.smul (hasFDerivAt_id y)
    have heq : r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A) =
        scaleToS H y • ContinuousLinearMap.id ℝ (V n) +
        ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight y := by
      ext1 v
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, ← hrdef, ← hxdef, smul_sub, smul_smul]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      field_simp
      ring
    rw [heq]; exact h1
  set us := fderiv ℝ u z 1
  set ut := fderiv ℝ u z Complex.I
  have hdsa : ds (fun z => aCoord H (u z)) z = α us := by
    unfold ds; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdta : dt (fun z => aCoord H (u z)) z = α ut := by
    unfold dt; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdsw : ds (fun z => proj H (u z)) z = r • (us - α us • A) := by
    unfold ds; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdtw : dt (fun z => proj H (u z)) z = r • (ut - α ut • A) := by
    unfold dt; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hWgen : ∀ v, IsInXi H x (v - α v • A - β v • B) := by
    intro v
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, ka_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [ka_om_sub_right, ka_om_sub_right]
      simp only [A, B, hyx, ka_om_smul_right]
      have h1 : omega0 x x = 0 := ka_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := ka_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply]
      unfold liouville; simp only [ka_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [ka_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, ka_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨?_, ?_⟩
  · rw [hdsa, hdtw, hLt, e1]
  · rw [hdta, hdsw, hLs, e2]



namespace KAo
open FiniteEnergyPlane
variable {n : ℕ}

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := ka_j0_add, map_smul' := ka_j0_smul }

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply, j0L]

end KAo

/-! Child A of `energy_le_diskArea`, layer 1: the cutoff `χ`, the extended map `W = χ(a) • w`,
its regularity, and the pointwise comparison of energy densities. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

noncomputable section

variable {n : ℕ}

/-- The cutoff `χ(s) = √(φ s + ε) · β(s + K)` with `β` the smooth transition. -/
def elaChi (φ : ℝ → ℝ) (ε K : ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (φ s + ε) * Real.smoothTransition (s + K)

theorem ela_chi_contDiff {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ContDiff ℝ ∞ (elaChi φ ε K) := by
  have hφε : ∀ s, 0 < φ s + ε := fun s => by linarith [(hφ.2.2 s).1]
  exact ((hφ.1.add contDiff_const).sqrt fun s => (hφε s).ne').mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.add contDiff_const))

theorem ela_chi_sq {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε) (K s : ℝ) :
    elaChi φ ε K s ^ 2 = (φ s + ε) * Real.smoothTransition (s + K) ^ 2 := by
  have hφε : 0 ≤ φ s + ε := by linarith [(hφ.2.2 s).1]
  rw [elaChi, mul_pow, Real.sq_sqrt hφε]

theorem ela_deriv_chi_sq {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε) (K s : ℝ) :
    deriv (fun s => elaChi φ ε K s ^ 2) s =
      deriv φ s * Real.smoothTransition (s + K) ^ 2 +
        (φ s + ε) * (2 * Real.smoothTransition (s + K) *
          deriv Real.smoothTransition (s + K)) := by
  have hfun : (fun s => elaChi φ ε K s ^ 2) =
      fun s => (φ s + ε) * Real.smoothTransition (s + K) ^ 2 :=
    funext fun s => ela_chi_sq hφ hε K s
  rw [hfun]
  have hφd : HasDerivAt (fun s => φ s + ε) (deriv φ s) s :=
    ((hφ.1.differentiable (by simp)) s).hasDerivAt.add_const ε
  have hβ : HasDerivAt (fun s => Real.smoothTransition (s + K))
      (deriv Real.smoothTransition (s + K)) s := by
    have h1 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (s + K)) (s + K) :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (s + K)).hasDerivAt
    simpa using h1.comp_add_const s K
  have hβ2 := hβ.pow 2
  have := hφd.mul hβ2
  exact this.deriv.trans (by simp only [Pi.pow_apply]; push_cast; ring)

/-- The `da ∧ λ` part of the energy integrand. -/
def elaX (H : V n → ℝ) (u : ℂ → V n) (z : ℂ) : ℝ :=
  ds (fun z => aCoord H (u z)) z * liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) -
    dt (fun z => aCoord H (u z)) z * liouville (proj H (u z)) (ds (fun z => proj H (u z)) z)

theorem ela_X_nonneg (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) : 0 ≤ elaX H u z := by
  obtain ⟨h1, h2⟩ := ka_cr H hH J hJ u z hdu hz hhol
  unfold elaX
  rw [← h1]
  have : liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) =
      -dt (fun z => aCoord H (u z)) z := by rw [h2]; ring
  rw [this]
  nlinarith [sq_nonneg (ds (fun z => aCoord H (u z)) z),
    sq_nonneg (dt (fun z => aCoord H (u z)) z)]

theorem ela_density_cmp {H : V n → ℝ} {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε)
    (K : ℝ) (u : ℂ → V n) (z : ℂ) (hX : 0 ≤ elaX H u z) (hY : 0 ≤ dlambdaDensity H u z) :
    Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z ≤
      energyDensity H (fun s => elaChi φ ε K s ^ 2) u z := by
  unfold energyDensity
  simp only
  rw [ela_deriv_chi_sq hφ hε K, ela_chi_sq hφ hε K]
  set s := aCoord H (u z)
  set X := ds (fun z => aCoord H (u z)) z *
      liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) -
    dt (fun z => aCoord H (u z)) z * liouville (proj H (u z)) (ds (fun z => proj H (u z)) z)
  have hXX : X = elaX H u z := rfl
  set Y := omega0 (ds (fun z => proj H (u z)) z) (dt (fun z => proj H (u z)) z)
  have hYY : Y = dlambdaDensity H u z := rfl
  rw [← hXX] at hX
  rw [← hYY] at hY
  have hb0 := Real.smoothTransition.nonneg (s + K)
  have hb' : 0 ≤ deriv Real.smoothTransition (s + K) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hφε : 0 < φ s + ε := by linarith [(hφ.2.2 s).1]
  have key : 0 ≤ (φ s + ε) * (2 * Real.smoothTransition (s + K) *
      deriv Real.smoothTransition (s + K)) * X + ε * Real.smoothTransition (s + K) ^ 2 * Y := by
    have := mul_nonneg (mul_nonneg hφε.le (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb0) hb')) hX
    have := mul_nonneg (mul_nonneg hε.le (sq_nonneg (Real.smoothTransition (s + K)))) hY
    linarith
  nlinarith [key]

/-- The extension of `χ(a) • w` by `0` on `Γ`. -/
def elaW (H : V n → ℝ) (Γ : Finset ℂ) (u : ℂ → V n) (φ : ℝ → ℝ) (ε K : ℝ) : ℂ → V n :=
  fun z => if z ∈ Γ then 0 else elaChi φ ε K (aCoord H (u z)) • proj H (u z)

theorem ela_isClosed (Γ : Finset ℂ) : IsClosed (Γ : Set ℂ) := Γ.finite_toSet.isClosed

theorem ela_W_eq_near (H : V n → ℝ) (Γ : Finset ℂ) (u : ℂ → V n) (φ : ℝ → ℝ) (ε K : ℝ)
    {z : ℂ} (hz : z ∉ Γ) :
    elaW H Γ u φ ε K =ᶠ[𝓝 z] fun z => elaChi φ ε K (aCoord H (u z)) • proj H (u z) := by
  have : (Γ : Set ℂ)ᶜ ∈ 𝓝 z := (ela_isClosed Γ).isOpen_compl.mem_nhds (by simpa using hz)
  filter_upwards [this] with y hy
  have hy' : y ∉ Γ := by simpa using hy
  simp [elaW, hy']

theorem ela_W_eventually_zero (H : V n → ℝ) (Γ : Finset ℂ) (u : ℂ → V n) (φ : ℝ → ℝ)
    (ε K : ℝ) {p : ℂ} (hp : p ∈ Γ)
    (hΓ : Tendsto (fun w => aCoord H (u w)) (𝓝[≠] p) atBot) :
    elaW H Γ u φ ε K =ᶠ[𝓝 p] fun _ => 0 := by
  have h1 : ∀ᶠ w in 𝓝[≠] p, aCoord H (u w) < -K := hΓ.eventually (eventually_lt_atBot (-K))
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with y hy
  by_cases hyp : y = p
  · subst hyp; simp [elaW, hp]
  · have hlt := hy hyp
    by_cases hyΓ : y ∈ Γ
    · simp [elaW, hyΓ]
    · have : Real.smoothTransition (aCoord H (u y) + K) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [elaW, hyΓ, elaChi, this]

theorem ela_aw_contDiffOn (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) {T : Set ℂ} (u : ℂ → V n)
    (hu : ContDiffOn ℝ ∞ u T) (hu0 : ∀ z ∈ T, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) T ∧ ContDiffOn ℝ ∞ (fun z => proj H (u z)) T := by
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  exact ⟨haCs.comp hu (fun z hz => hu0 z hz), hprojs.comp hu (fun z hz => hu0 z hz)⟩

theorem ela_W_contDiffOn (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot)
    {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ContDiffOn ℝ ∞ (elaW H Γ u φ ε K) (closedBall 0 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ ∞ (elaW H Γ u φ ε K) z := by
  obtain ⟨ha, hw⟩ := ela_aw_contDiffOn H hH J hJ u hu hu0
  have hV : ContDiffOn ℝ ∞ (fun z => elaChi φ ε K (aCoord H (u z)) • proj H (u z))
      (closedBall 0 1 \ Γ) :=
    ((ela_chi_contDiff hφ hε K).comp_contDiffOn ha).smul hw
  have hzero : ∀ p ∈ Γ, ContDiffAt ℝ ∞ (elaW H Γ u φ ε K) p := fun p hp =>
    (contDiffAt_const (c := (0 : V n))).congr_of_eventuallyEq
      (ela_W_eventually_zero H Γ u φ ε K hp (hΓ p hp))
  constructor
  · intro z hz
    by_cases hzΓ : z ∈ Γ
    · exact (hzero z hzΓ).contDiffWithinAt
    · have hmem : closedBall (0 : ℂ) 1 \ Γ ∈ 𝓝[closedBall 0 1] z := by
        have : (Γ : Set ℂ)ᶜ ∈ 𝓝 z := (ela_isClosed Γ).isOpen_compl.mem_nhds (by simpa using hzΓ)
        exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds this)
      exact ((hV z ⟨hz, hzΓ⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
        (nhdsWithin_le_nhds (ela_W_eq_near H Γ u φ ε K hzΓ)) (by simp [elaW, hzΓ])
  · intro z hz
    by_cases hzΓ : z ∈ Γ
    · exact hzero z hzΓ
    · have hmem : closedBall (0 : ℂ) 1 \ Γ ∈ 𝓝 z := by
        have : ball (0 : ℂ) 1 \ Γ ∈ 𝓝 z :=
          (isOpen_ball.sdiff (ela_isClosed Γ)).mem_nhds ⟨hz, hzΓ⟩
        exact mem_of_superset this (Set.diff_subset_diff_left ball_subset_closedBall)
      exact (hV.contDiffAt hmem).congr_of_eventuallyEq (ela_W_eq_near H Γ u φ ε K hzΓ)

end

end FiniteEnergyPlane

/-! Child A of `energy_le_diskArea`, layer 2: the bound on the disk of radius `R < 1`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

noncomputable section

variable {n : ℕ}

/-- A smooth map on `ℂ` that agrees with `W` near the closed disk of radius `R`, for `W` smooth on
the open unit disk. -/
theorem ela_exists_global (W : ℂ → V n) (hW : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ ∞ W z)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    ∃ W' : ℂ → V n, ContDiff ℝ ∞ W' ∧ ∀ z ∈ ball (0 : ℂ) ((R + 1) / 2), W' =ᶠ[𝓝 z] W := by
  let ψ : ContDiffBump (0 : ℂ) :=
    ⟨(R + 1) / 2, (R + 3) / 4, by linarith, by linarith⟩
  refine ⟨fun z => ψ z • W z, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · exact (ψ.contDiff.contDiffAt).smul (hW z hz)
    · have hz' : z ∉ closedBall (0 : ℂ) ((R + 3) / 4) := by
        intro h
        apply hz
        rw [mem_ball]; rw [mem_closedBall] at h; linarith
      have hev : ∀ᶠ y in 𝓝 z, ψ y • W y = (0 : V n) := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz'] with y hy
        have : ψ y = 0 := by
          have hy' : y ∉ ball (0 : ℂ) ((R + 3) / 4) := fun h => hy (ball_subset_closedBall h)
          have : y ∉ Function.support ψ := by
            change y ∉ Function.support (ψ : ℂ → ℝ)
            rw [ψ.support_eq]; exact hy'
          simpa using this
        simp [this]
      exact (contDiffAt_const (c := (0 : V n))).congr_of_eventuallyEq hev
  · intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    have : ψ y = 1 := ψ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [this]

theorem ela_buBdry_congr {W W' : ℂ → V n} {R : ℝ} (hR : 0 ≤ R) {R' : ℝ} (hRR' : R < R')
    (h : ∀ z ∈ ball (0 : ℂ) R', W' =ᶠ[𝓝 z] W) : buBdry W' R = buBdry W R := by
  unfold buBdry
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : circleMap 0 R θ ∈ ball (0 : ℂ) R' := by
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hR]; exact hRR'
  rw [(h _ hz).eq_of_nhds, (h _ hz).fderiv_eq]

/-- The energy bound on the disk of radius `R < 1`, with the cutoff `β(a + K)²`. -/
theorem ela_ball_bound (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ Γ) u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot)
    {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε) (K : ℝ) {R : ℝ} (hR0 : 0 < R)
    (hR1 : R < 1) :
    ∫⁻ z in ball 0 R \ Γ, ENNReal.ofReal
        (Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z) ≤
      ENNReal.ofReal (buBdry (elaW H Γ u φ ε K) R) := by
  set W := elaW H Γ u φ ε K with hWdef
  obtain ⟨-, hWat⟩ := ela_W_contDiffOn H hH J hJ Γ u hu hu0 hΓ hφ hε K
  obtain ⟨W', hW', hW'eq⟩ := ela_exists_global W hWat hR0 hR1
  have hRR : R < (R + 1) / 2 := by linarith
  rw [← ela_buBdry_congr hR0.le hRR hW'eq, ← bu_ball_eq W' hW' R hR0]
  set dens := fun z => omega0 (fderiv ℝ W' z 1) (fderiv ℝ W' z Complex.I) with hdens
  have hc : Continuous dens := bu_continuous_dens W' hW'
  have hint : IntegrableOn dens (ball 0 R) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall
  obtain ⟨ha, hw⟩ := ela_aw_contDiffOn H hH J hJ u hu hu0
  have hχd : Differentiable ℝ (elaChi φ ε K) := (ela_chi_contDiff hφ hε K).differentiable (by simp)
  -- the pointwise comparison on `ball R \ Γ`
  have hpt : ∀ z ∈ ball (0 : ℂ) R \ Γ,
      Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z ≤ dens z := by
    intro z ⟨hzR, hzΓ⟩
    have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball hR1.le hzR
    have hzU : z ∈ ball (0 : ℂ) 1 \ Γ := ⟨hz1, hzΓ⟩
    have hnhds : closedBall (0 : ℂ) 1 \ Γ ∈ 𝓝 z := by
      have : ball (0 : ℂ) 1 \ Γ ∈ 𝓝 z := (isOpen_ball.sdiff (ela_isClosed Γ)).mem_nhds hzU
      exact mem_of_superset this (Set.diff_subset_diff_left ball_subset_closedBall)
    have had : DifferentiableAt ℝ (fun z => aCoord H (u z)) z :=
      ((ha.contDiffAt hnhds).differentiableAt (by simp))
    have hwd : DifferentiableAt ℝ (fun z => proj H (u z)) z :=
      ((hw.contDiffAt hnhds).differentiableAt (by simp))
    have hfd : fderiv ℝ W' z = fderiv ℝ (fun z => elaChi φ ε K (aCoord H (u z)) • proj H (u z)) z := by
      rw [(hW'eq z (ball_subset_ball hRR.le hzR)).fderiv_eq,
        (ela_W_eq_near H Γ u φ ε K hzΓ).fderiv_eq]
    have hd : dens z = energyDensity H (fun s => elaChi φ ε K s ^ 2) u z := by
      simp only [hdens, hfd]
      exact bu_density_eq H u (elaChi φ ε K) hχd z had hwd
    rw [hd]
    obtain ⟨hdu, hdb⟩ := hhol z hzU
    have hX := ela_X_nonneg H hH J hJ u z hdu (hu0 z ⟨ball_subset_closedBall hz1, hzΓ⟩) hdb
    have hY := (energyDensity_nonneg_of_isJHolomorphicOn H hH J hJ (ball 0 1 \ Γ) u
      (fun y hy => hu0 y ⟨ball_subset_closedBall hy.1, hy.2⟩) hhol φ hφ hzU).2
    exact ela_density_cmp hφ hε K u z hX hY
  have hΓnull : volume (Γ : Set ℂ) = 0 := Γ.finite_toSet.measure_zero _
  have hnn : 0 ≤ᵐ[volume.restrict (ball (0 : ℂ) R)] dens := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_ball]
    have : ∀ᵐ z ∂volume, z ∉ (Γ : Set ℂ) := compl_mem_ae_iff.2 hΓnull
    filter_upwards [this] with z hz hzR
    have h1 := hpt z ⟨hzR, hz⟩
    have h2 : 0 ≤ Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z := by
      have hz1 : z ∈ ball (0 : ℂ) 1 \ Γ := ⟨ball_subset_ball hR1.le hzR, hz⟩
      exact mul_nonneg (sq_nonneg _) (energyDensity_nonneg_of_isJHolomorphicOn H hH J hJ
        (ball 0 1 \ Γ) u (fun y hy => hu0 y ⟨ball_subset_closedBall hy.1, hy.2⟩) hhol φ hφ hz1).1
    exact h2.trans h1
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  calc ∫⁻ z in ball 0 R \ Γ, ENNReal.ofReal
          (Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z)
      ≤ ∫⁻ z in ball 0 R \ Γ, ENNReal.ofReal (dens z) :=
        setLIntegral_mono' (measurableSet_ball.diff (ela_isClosed Γ).measurableSet)
          fun z hz => ENNReal.ofReal_le_ofReal (hpt z hz)
    _ ≤ ∫⁻ z in ball 0 R, ENNReal.ofReal (dens z) := lintegral_mono_set Set.diff_subset

end

end FiniteEnergyPlane

/-! Child A of `energy_le_diskArea`, layer 3: the boundary term `buBdry W R` as `R → 1⁻`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

noncomputable section

variable {n : ℕ}

theorem ela_uniqueDiffOn : UniqueDiffOn ℝ (closedBall (0 : ℂ) 1) :=
  uniqueDiffOn_convex (convex_closedBall 0 1) (by
    rw [interior_closedBall (0 : ℂ) one_ne_zero]; exact ⟨0, mem_ball_self one_pos⟩)

theorem ela_norm_circleMap {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : ‖circleMap (0 : ℂ) R θ‖ = R := by
  rw [norm_circleMap_zero, abs_of_nonneg hR]

/-- The boundary integrand, with derivatives within the closed disk. -/
def elaG (W : ℂ → V n) (z : ℂ) : ℝ :=
  omegaL (W z) (fderivWithin ℝ W (closedBall 0 1) z (z * Complex.I))

theorem ela_G_continuousOn (W : ℂ → V n) (hW : ContDiffOn ℝ ∞ W (closedBall 0 1)) :
    ContinuousOn (elaG W) (closedBall 0 1) := by
  have hd : ContinuousOn (fderivWithin ℝ W (closedBall 0 1)) (closedBall 0 1) :=
    hW.continuousOn_fderivWithin ela_uniqueDiffOn (by simp)
  have h2 : ContinuousOn (fun z => fderivWithin ℝ W (closedBall 0 1) z (z * Complex.I))
      (closedBall 0 1) :=
    hd.clm_apply (continuous_id.mul continuous_const).continuousOn
  exact (omegaL.continuous.comp_continuousOn hW.continuousOn).clm_apply h2

theorem ela_buBdry_eq_G (W : ℂ → V n) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    buBdry W R = (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, elaG W (circleMap 0 R θ) := by
  unfold buBdry
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : closedBall (0 : ℂ) 1 ∈ 𝓝 (circleMap 0 R θ) := by
    apply closedBall_mem_nhds_of_mem
    rw [mem_ball, dist_zero_right, ela_norm_circleMap hR0]; exact hR1
  simp only [elaG, fderivWithin_of_mem_nhds hz]

theorem ela_tendsto_buBdry (W : ℂ → V n) (hW : ContDiffOn ℝ ∞ W (closedBall 0 1)) :
    Tendsto (fun R => buBdry W R) (𝓝[<] 1)
      (𝓝 ((1 / 2) * ∫ θ in (0 : ℝ)..2 * π, elaG W (circleMap 0 1 θ))) := by
  set c : ℝ → ℝ := fun R => max 0 (min R 1) with hc
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hc0 : ∀ R, 0 ≤ c R := fun R => le_max_left _ _
  have hc1 : ∀ R, c R ≤ 1 := fun R => max_le zero_le_one (min_le_right _ _)
  have hF : Continuous (Function.uncurry fun R θ => elaG W (circleMap 0 (c R) θ)) := by
    have hm : Continuous fun p : ℝ × ℝ => circleMap (0 : ℂ) (c p.1) p.2 := by
      simp only [circleMap]
      fun_prop
    refine (ela_G_continuousOn W hW).comp_continuous hm fun p => ?_
    rw [mem_closedBall, dist_zero_right, ela_norm_circleMap (hc0 _)]; exact hc1 _
  have hI : Continuous fun R => ∫ θ in (0 : ℝ)..2 * π, elaG W (circleMap 0 (c R) θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _
  have h1 : c 1 = 1 := by simp [hc]
  have ht : Tendsto (fun R => (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, elaG W (circleMap 0 (c R) θ))
      (𝓝[<] 1) (𝓝 ((1 / 2) * ∫ θ in (0 : ℝ)..2 * π, elaG W (circleMap 0 (c 1) θ))) :=
    ((continuous_const.mul hI).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [h1] at ht
  refine ht.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with R hR
  have : c R = R := by simp [hc, hR.1.le, hR.2.le]
  rw [this, ela_buBdry_eq_G W hR.1.le hR.2]

/-- On the unit circle, where `a = 0`, the boundary integrand is `χ(0)²` times that of `w`. -/
theorem ela_G_sphere (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ)
    (hΓ₁ : (Γ : Set ℂ) ⊆ ball 0 1)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0)
    (hbd : ∀ z ∈ sphere (0 : ℂ) 1, aCoord H (u z) = 0)
    {φ : ℝ → ℝ} (hφ : Admissible φ) {ε : ℝ} (hε : 0 < ε) (K : ℝ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) :
    elaG (elaW H Γ u φ ε K) z = elaChi φ ε K 0 ^ 2 *
      omegaL (proj H (u z))
        (fderivWithin ℝ (fun z => proj H (u z)) (closedBall 0 1) z (z * Complex.I)) := by
  have hzΓ : z ∉ Γ := fun h => by
    have := hΓ₁ h
    rw [mem_ball, dist_zero_right] at this
    rw [mem_sphere, dist_zero_right] at hz
    linarith
  have hzB : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
  obtain ⟨ha, hw⟩ := ela_aw_contDiffOn H hH J hJ u hu hu0
  have hmem : closedBall (0 : ℂ) 1 \ Γ ∈ 𝓝[closedBall 0 1] z := by
    have : (Γ : Set ℂ)ᶜ ∈ 𝓝 z := (ela_isClosed Γ).isOpen_compl.mem_nhds (by simpa using hzΓ)
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds this)
  have had : DifferentiableWithinAt ℝ (fun z => aCoord H (u z)) (closedBall 0 1) z :=
    ((ha z ⟨hzB, hzΓ⟩).mono_of_mem_nhdsWithin hmem).differentiableWithinAt (by simp)
  have hwd : DifferentiableWithinAt ℝ (fun z => proj H (u z)) (closedBall 0 1) z :=
    ((hw z ⟨hzB, hzΓ⟩).mono_of_mem_nhdsWithin hmem).differentiableWithinAt (by simp)
  have hχd : Differentiable ℝ (elaChi φ ε K) := (ela_chi_contDiff hφ hε K).differentiable (by simp)
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hca : HasFDerivWithinAt (fun y => elaChi φ ε K (a y))
      (deriv (elaChi φ ε K) (a z) • fderivWithin ℝ a (closedBall 0 1) z) (closedBall 0 1) z :=
    (hχd (a z)).hasDerivAt.comp_hasFDerivWithinAt z had.hasFDerivWithinAt
  have hV := hca.smul hwd.hasFDerivWithinAt
  have hEq : fderivWithin ℝ (elaW H Γ u φ ε K) (closedBall 0 1) z =
      fderivWithin ℝ (fun y => elaChi φ ε K (a y) • w y) (closedBall 0 1) z :=
    ((ela_W_eq_near H Γ u φ ε K hzΓ).filter_mono nhdsWithin_le_nhds).fderivWithin_eq (by simp [elaW, hzΓ])
  have hWz : elaW H Γ u φ ε K z = elaChi φ ε K (a z) • w z := by simp [elaW, hzΓ, hadef, hwdef]
  unfold elaG
  rw [hEq, show fderivWithin ℝ (fun y => elaChi φ ε K (a y) • w y) (closedBall 0 1) z = _ from
    hV.fderivWithin (ela_uniqueDiffOn z hzB), hWz]
  have ha0 : a z = 0 := hbd z hz
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, map_add, map_smul, h0, ha0]
  ring

/-- The loop action of `u` on the unit circle in terms of within-derivatives. -/
theorem ela_loopAction_eq (H : V n → ℝ) (u : ℂ → V n)
    (hw : ∀ z ∈ sphere (0 : ℂ) 1,
      DifferentiableWithinAt ℝ (fun z => proj H (u z)) (closedBall 0 1) z) :
    loopAction H u (ccwLoop 1) = (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
      omegaL (proj H (u (circleMap 0 1 θ)))
        (fderivWithin ℝ (fun z => proj H (u z)) (closedBall 0 1) (circleMap 0 1 θ)
          (circleMap 0 1 θ * Complex.I)) := by
  set w := fun z => proj H (u z) with hwdef
  set D := fun z => fderivWithin ℝ w (closedBall 0 1) z with hD
  have hcm : ∀ t : ℝ, ccwLoop 1 t = circleMap 0 1 (2 * π * t) := by
    intro t; simp [ccwLoop, circleMap]
  have hloop : loopInS H u (ccwLoop 1) = fun t => w (circleMap 0 1 (2 * π * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hpt : ∀ t : ℝ, liouville (loopInS H u (ccwLoop 1) t) (deriv (loopInS H u (ccwLoop 1)) t) =
      π * omegaL (w (circleMap 0 1 (2 * π * t)))
        (D (circleMap 0 1 (2 * π * t)) (circleMap 0 1 (2 * π * t) * Complex.I)) := by
    intro t
    have hh : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * π)
    have h1 := (hasDerivAt_circleMap 0 1 (2 * π * t)).scomp t hh
    have hmem : circleMap (0 : ℂ) 1 (2 * π * t) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere, dist_zero_right, ela_norm_circleMap zero_le_one]
    have h2 := (hw _ hmem).hasFDerivWithinAt
    have h3 := h2.comp_hasDerivWithinAt (s := Set.univ) t h1.hasDerivWithinAt (fun s _ => by
      rw [mem_closedBall, dist_zero_right]; simp only [Function.comp]
      rw [ela_norm_circleMap zero_le_one])
    have h4 : HasDerivAt (fun t => w (circleMap 0 1 (2 * π * t)))
        ((2 * π) • D (circleMap 0 1 (2 * π * t)) (circleMap 0 1 (2 * π * t) * Complex.I)) t := by
      have := h3.hasDerivAt Filter.univ_mem
      rw [map_smul] at this
      exact this
    rw [hloop, h4.deriv]
    simp only [liouville, ← omegaL_apply, map_smul, smul_eq_mul]
    ring
  unfold loopAction
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun θ => omegaL (w (circleMap 0 1 θ))
      (D (circleMap 0 1 θ) (circleMap 0 1 θ * Complex.I))) (by positivity)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  field_simp

end

end FiniteEnergyPlane

/-! Child A of `energy_le_diskArea`: `energy_le_loopAction_of_aCoord_eq_zero`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

noncomputable section

variable {n : ℕ}

/-- The exhausting open sets `S k = {z ∈ B(0, 1 - 1/(k+2)) \ Γ | a z > 1 - k}`. -/
def elaS (H : V n → ℝ) (Γ : Finset ℂ) (u : ℂ → V n) (k : ℕ) : Set ℂ :=
  (ball (0 : ℂ) (1 - 1 / ((k : ℝ) + 2)) \ Γ) ∩ (fun z => aCoord H (u z)) ⁻¹' Set.Ioi (1 - (k : ℝ))

theorem ela_S_mono (H : V n → ℝ) (Γ : Finset ℂ) (u : ℂ → V n) : Monotone (elaS H Γ u) := by
  intro k m hkm z ⟨⟨hz, hzΓ⟩, ha⟩
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  refine ⟨⟨?_, hzΓ⟩, ?_⟩
  · refine ball_subset_ball ?_ hz
    have : 1 / ((m : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · simp only [Set.mem_preimage, Set.mem_Ioi] at ha ⊢; linarith

theorem ela_iUnion_S (H : V n → ℝ) (Γ : Finset ℂ) (u : ℂ → V n) :
    ⋃ k, elaS H Γ u k = ball (0 : ℂ) 1 \ Γ := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, ⟨hz, hzΓ⟩, -⟩
    refine ⟨ball_subset_ball ?_ hz, hzΓ⟩
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    linarith
  · rintro ⟨hz, hzΓ⟩
    rw [mem_ball, dist_zero_right] at hz
    have hpos : 0 < 1 - ‖z‖ := by linarith
    obtain ⟨k1, hk1⟩ := exists_nat_gt (1 / (1 - ‖z‖))
    obtain ⟨k2, hk2⟩ := exists_nat_gt (1 - aCoord H (u z))
    refine ⟨k1 + k2, ⟨?_, hzΓ⟩, ?_⟩
    · rw [mem_ball, dist_zero_right]
      push_cast
      have h1 : 1 < (1 - ‖z‖) * (k1 : ℝ) := by
        rw [div_lt_iff₀ hpos] at hk1; linarith
      have h2 : 1 / ((k1 : ℝ) + k2 + 2) < 1 - ‖z‖ := by
        rw [div_lt_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ k2 := by positivity
        nlinarith
      linarith
    · simp only [Set.mem_preimage, Set.mem_Ioi]
      push_cast
      have : (0 : ℝ) ≤ k1 := by positivity
      linarith

theorem ela_S_open (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0) (k : ℕ) : IsOpen (elaS H Γ u k) := by
  obtain ⟨ha, -⟩ := ela_aw_contDiffOn H hH J hJ u hu hu0
  have hsub : ball (0 : ℂ) (1 - 1 / ((k : ℝ) + 2)) \ Γ ⊆ closedBall 0 1 \ Γ := by
    refine Set.diff_subset_diff_left (ball_subset_closedBall.trans (closedBall_subset_closedBall ?_))
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    linarith
  exact (ha.continuousOn.mono hsub).isOpen_inter_preimage
    (isOpen_ball.sdiff (ela_isClosed Γ)) isOpen_Ioi

theorem energy_le_loopAction_of_aCoord_eq_zero_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (hΓ₁ : (Γ : Set ℂ) ⊆ ball 0 1)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ Γ) u)
    (hbd : ∀ z ∈ sphere (0 : ℂ) 1, aCoord H (u z) = 0)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    energy H (ball 0 1 \ Γ) u ≤ ENNReal.ofReal (loopAction H u (ccwLoop 1)) := by
  set L := loopAction H u (ccwLoop 1) with hL
  obtain ⟨ha, hw⟩ := ela_aw_contDiffOn H hH J hJ u hu hu0
  have hwd : ∀ z ∈ sphere (0 : ℂ) 1,
      DifferentiableWithinAt ℝ (fun z => proj H (u z)) (closedBall 0 1) z := by
    intro z hz
    have hzΓ : z ∉ Γ := fun h => by
      have := hΓ₁ h
      rw [mem_ball, dist_zero_right] at this
      rw [mem_sphere, dist_zero_right] at hz
      linarith
    have hzB : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
    have hmem : closedBall (0 : ℂ) 1 \ Γ ∈ 𝓝[closedBall 0 1] z := by
      have : (Γ : Set ℂ)ᶜ ∈ 𝓝 z := (ela_isClosed Γ).isOpen_compl.mem_nhds (by simpa using hzΓ)
      exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds this)
    exact ((hw z ⟨hzB, hzΓ⟩).mono_of_mem_nhdsWithin hmem).differentiableWithinAt (by simp)
  -- the limit of the boundary terms
  have hlim : ∀ φ, Admissible φ → ∀ ε, 0 < ε → ∀ K : ℝ,
      Tendsto (fun R => buBdry (elaW H Γ u φ ε K) R) (𝓝[<] 1)
        (𝓝 (elaChi φ ε K 0 ^ 2 * L)) := by
    intro φ hφ ε hε K
    have h := ela_tendsto_buBdry (elaW H Γ u φ ε K) (ela_W_contDiffOn H hH J hJ Γ u hu hu0 hΓ hφ hε K).1
    have hval : (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, elaG (elaW H Γ u φ ε K) (circleMap 0 1 θ) =
        elaChi φ ε K 0 ^ 2 * L := by
      rw [hL, ela_loopAction_eq H u hwd, mul_left_comm,
        ← intervalIntegral.integral_const_mul (elaChi φ ε K 0 ^ 2)]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      have hs : circleMap (0 : ℂ) 1 θ ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere, dist_zero_right, ela_norm_circleMap zero_le_one]
      exact ela_G_sphere H hH J hJ Γ hΓ₁ u hu hu0 hbd hφ hε K hs
    rw [hval] at h
    exact h
  -- the bound on `ball R₀ \ Γ` with the cutoff
  have hR₀ : ∀ φ, Admissible φ → ∀ ε, 0 < ε → ∀ K : ℝ, ∀ R₀, 0 < R₀ → R₀ < 1 →
      ∫⁻ z in ball 0 R₀ \ Γ, ENNReal.ofReal
        (Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z) ≤
      ENNReal.ofReal ((1 + ε) * max L 0) := by
    intro φ hφ ε hε K R₀ h0 h1
    have hb : ∫⁻ z in ball 0 R₀ \ Γ, ENNReal.ofReal
        (Real.smoothTransition (aCoord H (u z) + K) ^ 2 * energyDensity H φ u z) ≤
        ENNReal.ofReal (elaChi φ ε K 0 ^ 2 * L) := by
      refine ge_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp (hlim φ hφ ε hε K)) ?_
      filter_upwards [Ioo_mem_nhdsLT h1] with R hR
      exact (lintegral_mono_set (Set.diff_subset_diff_left (ball_subset_ball hR.1.le))).trans
        (ela_ball_bound H hH J hJ Γ u hu hu0 hhol hΓ hφ hε K (h0.trans hR.1) hR.2)
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hχ : elaChi φ ε K 0 ^ 2 = (φ 0 + ε) * Real.smoothTransition (0 + K) ^ 2 :=
      ela_chi_sq hφ hε K 0
    have hc0 : 0 ≤ elaChi φ ε K 0 ^ 2 := sq_nonneg _
    have hc1 : elaChi φ ε K 0 ^ 2 ≤ 1 + ε := by
      rw [hχ]
      have hb0 := Real.smoothTransition.nonneg (0 + K)
      have hb1 := Real.smoothTransition.le_one (0 + K)
      have hφ0 := hφ.2.2 0
      have : Real.smoothTransition (0 + K) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hM : L ≤ max L 0 := le_max_left _ _
    have hM0 : 0 ≤ max L 0 := le_max_right _ _
    calc elaChi φ ε K 0 ^ 2 * L ≤ elaChi φ ε K 0 ^ 2 * max L 0 :=
          mul_le_mul_of_nonneg_left hM hc0
      _ ≤ (1 + ε) * max L 0 := mul_le_mul_of_nonneg_right hc1 hM0
  -- the bound for each admissible `φ`
  have hφbd : ∀ φ, Admissible φ → ∀ ε, 0 < ε →
      ∫⁻ z in ball 0 1 \ Γ, ENNReal.ofReal (energyDensity H φ u z) ≤
        ENNReal.ofReal ((1 + ε) * max L 0) := by
    intro φ hφ ε hε
    rw [← ela_iUnion_S H Γ u, setLIntegral_iUnion_of_directed _ (ela_S_mono H Γ u).directed_le]
    refine iSup_le fun k => ?_
    have hr0 : 0 < 1 - 1 / ((k : ℝ) + 2) := by
      have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by
        have : (0 : ℝ) ≤ k := by positivity
        linarith)
      linarith
    have hr1 : 1 - 1 / ((k : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((k : ℝ) + 2) := by positivity
      linarith
    calc ∫⁻ z in elaS H Γ u k, ENNReal.ofReal (energyDensity H φ u z)
        ≤ ∫⁻ z in elaS H Γ u k, ENNReal.ofReal
            (Real.smoothTransition (aCoord H (u z) + k) ^ 2 * energyDensity H φ u z) := by
          refine setLIntegral_mono' (ela_S_open H hH J hJ Γ u hu hu0 k).measurableSet
            fun z hz => ?_
          have hz' := hz.2
          simp only [Set.mem_preimage, Set.mem_Ioi] at hz'
          rw [Real.smoothTransition.one_of_one_le (by linarith)]
          simp
      _ ≤ ∫⁻ z in ball 0 (1 - 1 / ((k : ℝ) + 2)) \ Γ, ENNReal.ofReal
            (Real.smoothTransition (aCoord H (u z) + k) ^ 2 * energyDensity H φ u z) :=
          lintegral_mono_set Set.inter_subset_left
      _ ≤ ENNReal.ofReal ((1 + ε) * max L 0) := hR₀ φ hφ ε hε k _ hr0 hr1
  -- let `ε → 0`
  have hfin : ∀ φ, Admissible φ →
      ∫⁻ z in ball 0 1 \ Γ, ENNReal.ofReal (energyDensity H φ u z) ≤ ENNReal.ofReal L := by
    intro φ hφ
    have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * max L 0)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal ((1 + 0) * max L 0))) :=
      ((ENNReal.continuous_ofReal.comp
        ((continuous_const.add continuous_id).mul continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have h := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hφbd φ hφ ε hε)
    refine h.trans (le_of_eq ?_)
    rw [show ((1 : ℝ) + 0) * max L 0 = max L 0 by ring]
    rcases le_total L 0 with hL0 | hL0
    · rw [max_eq_right hL0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hL0]
    · rw [max_eq_left hL0]
  unfold energy
  exact iSup₂_le fun φ hφ => hfin φ hφ

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (hΓ₁ : (Γ : Set ℂ) ⊆ ball 0 1)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ Γ) u)
    (hbd : ∀ z ∈ sphere (0 : ℂ) 1, aCoord H (u z) = 0)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    energy H (ball 0 1 \ Γ) u ≤ ENNReal.ofReal (loopAction H u (ccwLoop 1)) :=
  energy_le_loopAction_of_aCoord_eq_zero_aux H hH J hJ Γ hΓ₁ u hu hu0 hhol hbd hΓ
