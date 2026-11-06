-- Prove2me | solution 1 for BianchiIX.ode_variation_remainder
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:07:31.972492+00:00
-- url     : https://prove2.me/submissions/bcb09c57-bcc2-4b82-9c5d-8b981be7e2e4

import Theorems.Thm_BianchiIX_ode_norm_le_gronwall_uIcc
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

section
noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.ode_quadratic_remainder {f : E → E} {D : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (D x) x) {S : Set E} (hS : Convex ℝ S)
    {K : ℝ≥0} (hK : LipschitzOnWith K D S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x - D x (y - x)‖ ≤ K * ‖y - x‖ ^ 2 := by
  let g : E → E := fun z => f z - D x z
  have hg (z : E) : HasFDerivAt g (D z - D x) z := (hf z).sub (D x).hasFDerivAt
  have hbound (z : E) (hz : z ∈ segment ℝ x y) : ‖D z - D x‖ ≤ K * ‖y - x‖ :=
    (hK.norm_sub_le (hS.segment_subset hx hy hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have H := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [g, map_sub, sub_sub_sub_comm, pow_two, mul_assoc] using H

end
end

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- The variational equation controls the actual nonlinear remainder in any state space. -/
theorem solution {f : E → E} {D : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (D x) x) {α β : ℝ → E} {J : ℝ → E →L[ℝ] E}
    {t₀ t : ℝ} {S : Set E} (hS : Convex ℝ S) {K L : ℝ} {C : ℝ≥0}
    (hD : LipschitzOnWith C D S)
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (f (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (f (β u)) u)
    (hαS : ∀ u ∈ uIcc t₀ t, α u ∈ S) (hβS : ∀ u ∈ uIcc t₀ t, β u ∈ S)
    (hJ : ∀ u ∈ uIcc t₀ t, HasDerivAt J ((D (α u)).comp (J u)) u)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ E)
    (hDnorm : ∀ u ∈ uIcc t₀ t, ‖D (α u)‖ ≤ K)
    (hclose : ∀ u ∈ uIcc t₀ t, ‖β u - α u‖ ≤ L * ‖β t₀ - α t₀‖) :
    ‖β t - α t - J t (β t₀ - α t₀)‖ ≤
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖β t₀ - α t₀‖ ^ 2 := by
  let h := β t₀ - α t₀
  let e := fun u => β u - α u - J u h
  let de := fun u => f (β u) - f (α u) - D (α u) (J u h)
  have he (u : ℝ) (hu : u ∈ uIcc t₀ t) : HasDerivAt e (de u) u := by
    convert! ((hβ u hu).sub (hα u hu)).sub ((hJ u hu).clm_apply (hasDerivAt_const u h)) using 1
    simp [de]
  have hb (u : ℝ) (hu : u ∈ uIcc t₀ t) : ‖de u‖ ≤ K * ‖e u‖ + C * L ^ 2 * ‖h‖ ^ 2 := by
    have hde : de u = D (α u) (e u) + (f (β u) - f (α u) - D (α u) (β u - α u)) := by
      simp only [de, e, map_sub]
      abel
    rw [hde]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((D (α u)).le_opNorm (e u)).trans
        (mul_le_mul_of_nonneg_right (hDnorm u hu) (norm_nonneg _))
    · apply (ode_quadratic_remainder hf hS hD (hαS u hu) (hβS u hu)).trans
      calc
        (C : ℝ) * ‖β u - α u‖ ^ 2 ≤ C * (L * ‖h‖) ^ 2 := by gcongr; exact hclose u hu
        _ = C * L ^ 2 * ‖h‖ ^ 2 := by ring
  have H := ode_norm_le_gronwall_uIcc he (δ := 0) (by simp [e, h, hJinit]) hb
  have hscale : gronwallBound 0 K (C * L ^ 2 * ‖h‖ ^ 2) |t - t₀| =
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖h‖ ^ 2 := by
    unfold gronwallBound
    split_ifs <;> ring
  simpa only [hscale, e, h] using H
