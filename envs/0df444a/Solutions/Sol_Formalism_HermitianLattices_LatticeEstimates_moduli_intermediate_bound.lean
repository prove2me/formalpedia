-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.moduli_intermediate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:23.607151+00:00
-- url     : https://prove2.me/submissions/e06918f2-73d0-4a9b-bc5d-84e3905987f9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution : Ms_between := by
  intro R G _ _ _ _ r
  have : Nat.card (Fin r → G) = Nat.card G ^ r := by simp [Nat.card_fun]
  rw [← this]
  apply Nat.card_le_card_of_surjective (fun s : Fin r → G =>
    (⟨Submodule.span R (Set.range s), s, rfl⟩ :
      {H : Submodule R G // ∃ s : Fin r → G, Submodule.span R (Set.range s) = H}))
  rintro ⟨H, s, rfl⟩
  exact ⟨s, rfl⟩
end Formalism.HermitianLattices.LatticeEstimates
