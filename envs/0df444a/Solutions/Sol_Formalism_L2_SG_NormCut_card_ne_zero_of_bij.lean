-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.card_ne_zero_of_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:48.128435+00:00
-- url     : https://prove2.me/submissions/44bd412d-7d02-4c8d-9007-6c4ae6a7f144

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type} [Group I] [Fintype I]
namespace Formalism.L2.SG.NormCut
theorem _root_.solution {C : Type*} (A U : Set I) (s : C → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I))) :
    (Nat.card A : ℂ) ≠ 0 ∧ (Nat.card U : ℂ) ≠ 0 := by
  obtain ⟨⟨a, c, u⟩, -⟩ := hb.2 1
  haveI : Nonempty A := ⟨a⟩
  haveI : Nonempty U := ⟨u⟩
  exact ⟨by exact_mod_cast (Nat.card_pos (α := A)).ne', by exact_mod_cast (Nat.card_pos (α := U)).ne'⟩
end Formalism.L2.SG.NormCut
