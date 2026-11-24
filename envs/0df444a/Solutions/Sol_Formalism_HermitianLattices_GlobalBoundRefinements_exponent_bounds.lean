-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:06.766196+00:00
-- url     : https://prove2.me/submissions/8906105e-5960-4c7b-83c3-a16bad9f992a

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
theorem _root_.solution : TableauExponentRange := by
  intro μ T j last first s nu1 hfirst hnu hs hnu1
  have hcard : (μ.cells.filter (fun c => T c.1 c.2 = j)).card ≤ μ.rowLen 0 := by
    calc (μ.cells.filter (fun c => T c.1 c.2 = j)).card ≤ (range (μ.rowLen 0)).card := by
          apply Finset.card_le_card_of_injOn (fun c => c.2)
          · intro c hc
            have hc' : c ∈ μ.cells ∧ T c.1 c.2 = j := by simpa using hc
            obtain ⟨i, k⟩ := c
            have h1 : (i, k) ∈ μ := hc'.1
            have h2 := μ.mem_iff_lt_rowLen.mp h1
            have h3 := μ.rowLen_anti 0 i (Nat.zero_le i)
            simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range]
            omega
          · intro a ha b hb hab
            have ha' : a ∈ μ.cells ∧ T a.1 a.2 = j := by simpa using ha
            have hb' : b ∈ μ.cells ∧ T b.1 b.2 = j := by simpa using hb
            obtain ⟨i, k⟩ := a
            obtain ⟨i', k'⟩ := b
            simp only at hab
            subst hab
            have hi : (i, k) ∈ μ := ha'.1
            have hi' : (i', k) ∈ μ := hb'.1
            have ea := ha'.2
            have eb := hb'.2
            simp only at ea eb
            rcases lt_trichotomy i i' with h | h | h
            · have := SemistandardYoungTableau.col_strict (T := T) h hi'
              exfalso
              omega
            · rw [h]
            · have := SemistandardYoungTableau.col_strict (T := T) h hi
              exfalso
              omega
      _ = μ.rowLen 0 := Finset.card_range _
  have hc : (((μ.cells.filter (fun c => T c.1 c.2 = j)).card : ℕ) : ℤ) ≤ (μ.rowLen 0 : ℤ) := by
    exact_mod_cast hcard
  refine ⟨by omega, by omega, max_le (by omega) hnu1⟩
end Formalism.HermitianLattices.GlobalBoundRefinements
