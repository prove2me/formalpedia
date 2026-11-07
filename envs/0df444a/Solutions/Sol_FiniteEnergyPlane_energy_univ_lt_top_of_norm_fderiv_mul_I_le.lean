-- Prove2me | solution 1 for FiniteEnergyPlane.energy_univ_lt_top_of_norm_fderiv_mul_I_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T17:22:00.64003+00:00
-- url     : https://prove2.me/submissions/e255b095-7b90-475f-adf4-2f7c171de8db

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg_of_isJHolomorphicOn
import Theorems.Thm_FiniteEnergyPlane_setIntegral_ball_omega0_fderiv_eq
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface



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

open ZCS
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `|ω₀(x, y)| ≤ C ‖x‖ ‖y‖`. -/
theorem ifl_abs_omega0_le {n : ℕ} (x y : V n) :
    |omega0 x y| ≤ (2 * (n + 1) : ℝ) * (‖x‖ * ‖y‖) := by
  unfold omega0 dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hj : ∀ k, |j0 x k| ≤ ‖x‖ := by
    intro k
    unfold j0
    split_ifs
    · rw [abs_neg]; exact norm_le_pi_norm x _
    · exact norm_le_pi_norm x _
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (2 * (n + 1)))),
      |j0 x k * y k| ≤ ‖x‖ * ‖y‖ := by
    intro k _
    rw [abs_mul]
    exact mul_le_mul (hj k) (norm_le_pi_norm y k) (abs_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans (le_of_eq ?_)
  simp

/-- The energy density for `χ²` is the `ω₀`-density of `χ(a) • w`. -/
theorem ifl_density_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
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
theorem ifl_bdry_form {n : ℕ} (a : ℂ → ℝ) (w : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (z v : ℂ) (ha : DifferentiableAt ℝ a z) (hw : DifferentiableAt ℝ w z) :
    omega0 (χ (a z) • w z) (fderiv ℝ (fun z => χ (a z) • w z) z v) =
      χ (a z) ^ 2 * omega0 (w z) (fderiv ℝ w z v) := by
  have hca : HasFDerivAt (fun y => χ (a y)) (deriv χ (a z) • fderiv ℝ a z) z :=
    (hχ (a z)).hasDerivAt.comp_hasFDerivAt z ha.hasFDerivAt
  have hW : HasFDerivAt (fun z => χ (a z) • w z) _ z := hca.smul hw.hasFDerivAt
  rw [hW.fderiv]
  simp only [← omegaL_apply]
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, map_add, map_smul, h0]
  ring

theorem energy_univ_lt_top_of_norm_fderiv_mul_I_le_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (K : ℝ)
    (hK : ∀ z, ‖fderiv ℝ (fun z => proj H (u z)) z (z * Complex.I)‖ ≤ K) :
    energy H Set.univ u < ⊤ := by
  obtain ⟨-, hprojs, haCs, hrep, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hw : ContDiff ℝ ∞ w :=
    contDiffOn_univ.1 (hprojs.comp hu.contDiffOn (fun z _ => hu0 z))
  have ha : ContDiff ℝ ∞ a :=
    contDiffOn_univ.1 (haCs.comp hu.contDiffOn (fun z _ => hu0 z))
  have had : ∀ z, DifferentiableAt ℝ a z := fun z => (ha.differentiable (by simp)) z
  have hwd : ∀ z, DifferentiableAt ℝ w z := fun z => (hw.differentiable (by simp)) z
  obtain ⟨M, hM⟩ := (isCompact_energySurface H hH).exists_bound_of_continuousOn
    (continuous_norm.continuousOn (s := energySurface H))
  have hMw : ∀ z, ‖w z‖ ≤ M := fun z => by
    have := hM (w z) (hrep (u z) (hu0 z)).1
    simpa using this
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMw 0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set Cn : ℝ := 2 * (n + 1) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  set B : ℝ := 2 * Cn * (M * K) with hB
  have hB0 : 0 ≤ B := by positivity
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := B * (π * 1)))
  refine iSup₂_le fun φ hφ => ?_
  set χ : ℝ → ℝ := fun s => Real.sqrt (φ s + 1) with hχdef
  have hφε : ∀ s, 0 < φ s + 1 := fun s => by linarith [(hφ.2.2 s).1]
  have hχ : ContDiff ℝ ∞ χ := (hφ.1.add contDiff_const).sqrt fun s => (hφε s).ne'
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hχ2 : ∀ s, χ s ^ 2 = φ s + 1 := fun s => Real.sq_sqrt (hφε s).le
  set W : ℂ → V n := fun z => χ (a z) • w z with hWdef
  have hWc : ContDiff ℝ ∞ W := (hχ.comp ha).smul hw
  have hfun : (fun s => χ s ^ 2) = fun s => φ s + 1 := funext hχ2
  have hden : ∀ z, omega0 (fderiv ℝ W z 1) (fderiv ℝ W z Complex.I) =
      energyDensity H (fun s => φ s + 1) u z := fun z => by
    rw [← hfun]
    exact ifl_density_eq H u χ hχd z (had z) (hwd z)
  have hnn := fun z => energyDensity_nonneg_of_isJHolomorphicOn H hH J hJ Set.univ u
    (fun z _ => hu0 z) hhol φ hφ (Set.mem_univ z)
  have hcmp : ∀ z, energyDensity H φ u z ≤ energyDensity H (fun s => φ s + 1) u z := by
    intro z
    have hd : deriv (fun s => φ s + 1) (a z) = deriv φ (a z) := by simp
    have h2 := (hnn z).2
    simp only [dlambdaDensity] at h2
    simp only [energyDensity]
    rw [show deriv (fun s => φ s + 1) (aCoord H (u z)) = deriv φ (aCoord H (u z)) from hd]
    linarith
  -- the disc bound
  have hball : ∀ R : ℝ, 0 < R → ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H φ u z) ≤
      ENNReal.ofReal (B * (π * 1)) := by
    intro R hR
    have hint : IntegrableOn (fun z => energyDensity H (fun s => φ s + 1) u z) (ball 0 R) := by
      have hc : Continuous (fun z => energyDensity H (fun s => φ s + 1) u z) := by
        simp_rw [← hden, ← omegaL_apply]
        have hd : Continuous (fderiv ℝ W) := hWc.continuous_fderiv (by simp)
        exact (omegaL.continuous₂).comp₂ (hd.clm_apply continuous_const)
          (hd.clm_apply continuous_const)
      exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
        ball_subset_closedBall
    have hS := setIntegral_ball_omega0_fderiv_eq W hWc R hR
    have hbd : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖omega0 (W (circleMap 0 R θ))
        (fderiv ℝ W (circleMap 0 R θ) (circleMap 0 R θ * Complex.I))‖ ≤ B := by
      intro θ _
      set z := circleMap 0 R θ with hz
      have hform := ifl_bdry_form a w χ hχd z (z * Complex.I) (had z) (hwd z)
      rw [show W z = χ (a z) • w z from rfl,
        show fderiv ℝ W z = fderiv ℝ (fun z => χ (a z) • w z) z from rfl, hform, hχ2,
        Real.norm_eq_abs, abs_mul, abs_of_pos (hφε _)]
      have h1 : φ (a z) + 1 ≤ 2 := by linarith [(hφ.2.2 (a z)).2]
      have h2 := ifl_abs_omega0_le (w z) (fderiv ℝ w z (z * Complex.I))
      have h3 : ‖w z‖ * ‖fderiv ℝ w z (z * Complex.I)‖ ≤ M * K :=
        mul_le_mul (hMw z) (hK z) (norm_nonneg _) hM0
      have h4 : |omega0 (w z) (fderiv ℝ w z (z * Complex.I))| ≤ Cn * (M * K) :=
        h2.trans (mul_le_mul_of_nonneg_left h3 hCn0)
      calc (φ (a z) + 1) * |omega0 (w z) (fderiv ℝ w z (z * Complex.I))|
          ≤ 2 * (Cn * (M * K)) := mul_le_mul h1 h4 (abs_nonneg _) (by norm_num)
        _ = B := by rw [hB]; ring
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hval : ∫ z in ball 0 R, energyDensity H (fun s => φ s + 1) u z ≤ B * (π * 1) := by
      simp_rw [← hden]
      rw [hS]
      have h2π : |2 * π - 0| = 2 * π := by rw [sub_zero, abs_of_pos (by positivity)]
      rw [h2π, Real.norm_eq_abs] at hI
      have := le_abs_self (∫ θ in (0 : ℝ)..2 * π, omega0 (W (circleMap 0 R θ))
        (fderiv ℝ W (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)))
      linarith
    have hφεn : ∀ z, 0 ≤ energyDensity H (fun s => φ s + 1) u z := fun z =>
      (hnn z).1.trans (hcmp z)
    calc ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H φ u z)
        ≤ ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H (fun s => φ s + 1) u z) :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hcmp z)
      _ = ENNReal.ofReal (∫ z in ball 0 R, energyDensity H (fun s => φ s + 1) u z) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφεn)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hval
  -- exhaust by balls
  set μ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (energyDensity H φ u z))
    with hμdef
  have hμ : ∀ s : Set ℂ, MeasurableSet s →
      ∫⁻ z in s, ENNReal.ofReal (energyDensity H φ u z) = μ s := fun s hs =>
    (withDensity_apply _ hs).symm
  have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) ((N : ℝ) + 1)) := fun i j hij =>
    ball_subset_ball (by have : (i : ℝ) ≤ j := by exact_mod_cast hij
                         linarith)
  have hunion : ⋃ N : ℕ, ball (0 : ℂ) ((N : ℝ) + 1) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 (by linarith)⟩
  have hN : ∀ N : ℕ, (μ ∘ fun N : ℕ => ball (0 : ℂ) ((N : ℝ) + 1)) N ≤
      ENNReal.ofReal (B * (π * 1)) := by
    intro N
    rw [Function.comp_apply, ← hμ _ measurableSet_ball]
    exact hball _ (by positivity)
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion, ← hμ _ MeasurableSet.univ] at h
  exact le_of_tendsto' h hN

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (K : ℝ)
    (hK : ∀ z, ‖fderiv ℝ (fun z => proj H (u z)) z (z * Complex.I)‖ ≤ K) :
    energy H Set.univ u < ⊤ :=
  energy_univ_lt_top_of_norm_fderiv_mul_I_le_aux H hH J hJ u hu hu0 hhol K hK
