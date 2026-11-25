-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.theorem_B_entry_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:27.393794+00:00
-- url     : https://prove2.me/submissions/915cd5b1-15a7-4313-8329-101066c38943

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unipotent_upper_inverse
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_local_integral_entries_of_signature_preserving
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_Final_local_integral_entries_of_signature_preserving


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ThmBEntryDiag := by
  intro M N hM hN
  rw [unipotent_upper_inverse N hN]
  have e : (M * (Formalism.SLP.GlobalBoundRefinements.J * N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J)) 0 0 =
      M 0 0 * star (N 0 0) - M 0 1 * star (N 0 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.SLP.GlobalBoundRefinements.J, Matrix.vecMul, dotProduct]; ring
  rw [e]
  obtain ⟨_, hM01, _⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.local_integral_entries_of_signature_preserving M hM
  obtain ⟨_, hN01, _⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.local_integral_entries_of_signature_preserving N hN
  calc _ ≤ ‖M 0 0 * star (N 0 0)‖ + ‖M 0 1 * star (N 0 1)‖ := norm_sub_le _ _
    _ = _ := by simp [hM01, hN01]
end Formalism.HermitianLatticeCounting.P
