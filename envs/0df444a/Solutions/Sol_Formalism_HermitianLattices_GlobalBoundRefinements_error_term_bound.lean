-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.error_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:46.614069+00:00
-- url     : https://prove2.me/submissions/6d3e3e6e-a4c1-47b4-b26d-2b4ac31cd604

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : ExponentBudgetLogBound := by
  intro ι inst1 W nT m t N b L logT C₀ hW hnT hm ht hN0 hNb htm hl0 hl
  have hc0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnT' : (nT : ℝ) ≤ Fintype.card ι := by exact_mod_cast hnT
  have hsumW0 : 0 ≤ ∑ τ, W τ := Finset.sum_nonneg (fun τ _ => (hW τ).1)
  have hsumW : ∑ τ, W τ ≤ (Fintype.card ι : ℝ) * (2 * b) := by
    calc ∑ τ, W τ ≤ ∑ _τ : ι, 2 * b := Finset.sum_le_sum (fun τ _ => (hW τ).2)
      _ = (Fintype.card ι : ℝ) * (2 * b) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA : (nT : ℝ) * ((t : ℝ) + 1) ≤ (Fintype.card ι : ℝ) * (2 * t) :=
    mul_le_mul hnT' (by linarith) (by positivity) hc0
  have hB : (nT : ℝ) * ((t : ℝ) + 1) * ((m : ℝ) + 1) ≤ (Fintype.card ι : ℝ) * (2 * t) * (2 * m) :=
    mul_le_mul hA (by linarith) (by positivity) (by positivity)
  have hC : (Fintype.card ι : ℝ) * ((t : ℝ) * m) ≤ (Fintype.card ι : ℝ) * b :=
    mul_le_mul_of_nonneg_left htm hc0
  have hD : (Fintype.card ι : ℝ) * N ≤ (Fintype.card ι : ℝ) * b :=
    mul_le_mul_of_nonneg_left hNb hc0
  have hE : 0 ≤ (Fintype.card ι : ℝ) * N := mul_nonneg hc0 hN0
  have hF : 0 ≤ (nT : ℝ) * ((t : ℝ) + 1) * ((m : ℝ) + 1) := by positivity
  have hBC : (Fintype.card ι : ℝ) * (2 * t) * (2 * m) = 4 * ((Fintype.card ι : ℝ) * ((t : ℝ) * m)) := by
    ring
  have hW2 : (Fintype.card ι : ℝ) * (2 * b) = 2 * ((Fintype.card ι : ℝ) * b) := by ring
  have hS0 : 0 ≤ 2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4 := by
    linarith
  have hS : 2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4
      ≤ 6 * ((Fintype.card ι : ℝ) * b) := by
    linarith
  have hCL : 0 ≤ C₀ * m * L := le_trans hl0 hl
  refine ⟨mul_nonneg hS0 hl0, ?_⟩
  calc (2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4) * logT
      ≤ (2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4) * (C₀ * m * L) :=
        mul_le_mul_of_nonneg_left hl hS0
    _ ≤ (6 * ((Fintype.card ι : ℝ) * b)) * (C₀ * m * L) := mul_le_mul_of_nonneg_right hS hCL
    _ = 6 * C₀ * Fintype.card ι * b * m * L := by ring
end Formalism.HermitianLattices.GlobalBoundRefinements
