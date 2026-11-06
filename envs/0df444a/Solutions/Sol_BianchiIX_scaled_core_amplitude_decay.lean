-- Prove2me | solution 1 for BianchiIX.scaled_core_amplitude_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:35:43.731633+00:00
-- url     : https://prove2.me/submissions/0a75f896-7322-47a4-8a48-ebdd1e665889

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_strong_velocity
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_weak_product_directional
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_coupling_nonneg {k u v w : ℝ} (hk : 6 ≤ k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w) : 0 ≤ coupling u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  exact mul_nonneg hu.1 (by linarith)

end
end

/-- Quantitative amplitude decay uses the actual accumulated projective clock. -/
theorem solution {β : ℝ → ProjectiveState} {a τ : ℝ → ℝ} {I : Set ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (ha : ∀ u ∈ I, 0 ≤ a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hτ : ∀ u ∈ I, HasDerivAt τ (a u) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    β t 1 ≤ β s 1 * Real.exp ((-k ^ 2 / 10) * (τ t - τ s)) ∧
      β t 2 * β t 3 ≤ (β s 2 * β s 3) * Real.exp (-2 * (τ t - τ s)) := by
  constructor
  · apply le_exp_of_clock_deriv_le hI (fun u hh => hasDerivAt_pi.mp (hβ u hh) 1) hτ ?_ hs ht hst
    intro u hh
    have H := mul_le_mul_of_nonneg_left (coreBootstrap_strong_velocity hk (hr u hh) (hu u hh) (hw u hh)) (ha u hh)
    change a u * strongVelocity (β u 0) (β u 1) (β u 2) (β u 3) ≤ _
    convert! H using 1
    ring
  · have hP (u : ℝ) (hh : u ∈ I) :
        HasDerivAt (fun v => β v 2 * β v 3)
          (a u * (-2 * (1 + coupling (β u 1) (β u 2) (β u 3)) * (β u 2 * β u 3))) u := by
      have H := (hasDerivAt_pi.mp (hβ u hh) 2).mul (hasDerivAt_pi.mp (hβ u hh) 3)
      convert! H using 1
      change _ = a u * activeVelocity (β u 0) (β u 1) (β u 2) (β u 3) * β u 3 +
        β u 2 * (a u * weakVelocity (β u 0) (β u 1) (β u 2) (β u 3))
      rw [show a u * activeVelocity (β u 0) (β u 1) (β u 2) (β u 3) * β u 3 +
          β u 2 * (a u * weakVelocity (β u 0) (β u 1) (β u 2) (β u 3)) =
          a u * (activeVelocity (β u 0) (β u 1) (β u 2) (β u 3) * β u 3 +
            β u 2 * weakVelocity (β u 0) (β u 1) (β u 2) (β u 3)) by ring,
        weak_product_directional]
    apply le_exp_of_clock_deriv_le hI hP hτ ?_ hs ht hst
    intro u hh
    have hC := coreBootstrap_coupling_nonneg hk (hv u hh) (hu u hh) (hw u hh).1
    have hprod : 0 ≤ a u * coupling (β u 1) (β u 2) (β u 3) * (β u 2 * β u 3) :=
      mul_nonneg (mul_nonneg (ha u hh) hC) (mul_nonneg (by linarith [hv u hh]) (hw u hh).1)
    nlinarith
