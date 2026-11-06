-- Prove2me | solution 1 for BianchiIX.exists_scaled_coreAngle_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:34:10.337659+00:00
-- url     : https://prove2.me/submissions/4e1e564d-3189-45f1-9ec4-2e673e874814

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_convex_positiveIntegralClock_target
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_positiveIntegralClock_symm
import Theorems.Thm_BianchiIX_hasDerivAt_toCoreAngleState_scaled
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_positiveIntegralClock_symm_zero
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fromCoreAngleState_toCoreAngleState {y : ProjectiveState} (hv : 0 < y 2) :
    fromCoreAngleState (coreAngle (y 0) (y 2)) (toCoreAngleState y) = y := by
  ext i
  fin_cases i
  · exact (coreAngle_coordinates hv).2
  · rfl
  · exact (coreAngle_coordinates hv).1
  · change y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) = y 3
    rw [(coreAngle_coordinates hv).1]
    field_simp

end
end

/-- Integrating the positive angle rate constructs its inverse on the entire chosen interval. -/
theorem solution {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {s : ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (ha : ContinuousOn a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hβ : ∀ t ∈ I, HasDerivAt β (a t • projectiveField (β t)) t)
    (hv : ∀ t ∈ I, 0 < β t 2)
    (hd : ∀ t ∈ I, 0 < coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        coreAngle (β (e.symm z) 0) (β (e.symm z) 2) = z + coreAngle (β s 0) (β s 2) ∧
        HasDerivAt (fun u => toCoreAngleState (β (e.symm u)))
          (coreAngleField (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z)))) z ∧
        fromCoreAngleState (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z))) = β (e.symm z)) := by
  let q : ℝ → ℝ := fun t => a t * coreRadius (β t 0) (β t 2) *
    coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)
  have hcoord (i : Fin 4) : ContinuousOn (fun t => β t i) I :=
    fun t ht => (hasDerivAt_pi.mp (hβ t ht) i).continuousAt.continuousWithinAt
  have hR : ContinuousOn (fun t => coreRadius (β t 0) (β t 2)) I := by
    unfold coreRadius coreEnergy
    exact (((hcoord 0).sub continuousOn_const).pow 2 |>.add ((hcoord 2).pow 2)).sqrt
  have hq : ContinuousOn q I := by
    apply (ha.mul hR).mul
    exact continuousOn_const.sub (((hcoord 1).sub (hcoord 3)).pow 2 |>.div (hR.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (coreRadius_pos (hv t ht)))))
  have hqpos : ∀ t ∈ I, 0 < q t := fun t ht =>
    mul_pos (mul_pos (ha_pos t ht) (coreRadius_pos (hv t ht))) (hd t ht)
  have hz (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun u => coreAngle (β u 0) (β u 2)) (q t) t :=
    hasDerivAt_coreAngle_scaled (hβ t ht) (hv t ht)
  have hg (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun u => integralClock q s u + coreAngle (β s 0) (β s 2)) (q t) t :=
    (hasStrictDerivAt_integralClock hI ho hq hs ht).hasDerivAt.add_const _
  have heq : I.EqOn (fun t => coreAngle (β t 0) (β t 2))
      (fun t => integralClock q s t + coreAngle (β s 0) (β s 2)) :=
    ho.eqOn_of_deriv_eq hI.isPreconnected
      (fun t ht => (hz t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hz t ht).deriv.trans (hg t ht).deriv.symm) hs (by rw [integralClock_initial, zero_add])
  let e := positiveIntegralClock hI ho hq hs hqpos
  have he0 : e s = 0 := integralClock_initial q s
  refine ⟨e, rfl, ?_, convex_positiveIntegralClock_target hI ho hq hs hqpos,
    he0 ▸ e.map_source hs, positiveIntegralClock_symm_zero hI ho hq hs hqpos,
    strictMonoOn_integralClock hI ho hq hs hqpos, ?_⟩
  · intro t ht
    change integralClock q s t = _
    linarith [heq ht]
  · intro z hzmem
    have ht : e.symm z ∈ I := e.map_target hzmem
    have htime : coreAngle (β (e.symm z) 0) (β (e.symm z) 2) = z + coreAngle (β s 0) (β s 2) := by
      have H := heq ht
      change _ = e (e.symm z) + _ at H
      rw [e.right_inv hzmem] at H
      exact H
    have hinv := hasDerivAt_positiveIntegralClock_symm hI ho hq hs hqpos hzmem
    have hstate := (hasDerivAt_toCoreAngleState_scaled (hβ _ ht) (hv _ ht) (ne_of_gt (hd _ ht))).scomp z hinv
    have hstate' : HasDerivAt (fun u => toCoreAngleState (β (e.symm u)))
        (coreAngleField (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z)))) z := by
      change HasDerivAt _ ((1 / q (e.symm z)) • (q (e.symm z) • _)) z at hstate
      simp only [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt (hqpos _ ht)), one_smul, htime] at hstate
      convert! hstate using 1
    refine ⟨htime, hstate', ?_⟩
    rw [← htime]
    exact fromCoreAngleState_toCoreAngleState (hv _ ht)
