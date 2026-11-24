-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.hostE_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:19.422174+00:00
-- url     : https://prove2.me/submissions/0f5b0687-08d7-486c-a6f7-2e707a025167

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (ζ a b : L) : hostE ζ a b = ℚ⟮ζ + ζ⁻¹, a, b⟯ := by
  rw [hostE.eq_1, E0.eq_1, F1.eq_1, ← IntermediateField.adjoin_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto
end Formalism.FrobeniusOrbits.Galois
