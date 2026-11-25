-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitian_sphere_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:56.706059+00:00
-- url     : https://prove2.me/submissions/9f4dfee0-2ab3-4c39-ad6a-3f23fad738f9

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_herm_rec

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
theorem _root_.solution : HermSphereCount := by
  intro K L _ _ _ _ _ h2 M c hc
  induction M with
  | zero =>
    rw [s5a4_herm_rec h2 0 c]
    have : IsEmpty {x : Fin 0 → L // ∑ i, Algebra.norm K (x i) = c} :=
      ⟨fun x => by have := x.2; simp at this; exact hc this.symm⟩
    rw [Nat.card_of_isEmpty]; simp
  | succ M ih =>
    rw [s5a4_herm_rec h2 (M + 1) c, ih]; ring
end Formalism.HermitianLatticeCounting.P
