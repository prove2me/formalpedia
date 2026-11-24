-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_wordOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:47.563529+00:00
-- url     : https://prove2.me/submissions/787ceffd-6c0c-4cbc-a647-74f64ef5a043

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (e : Fin r × Fin n →₀ ℕ) :
    wordOf e = (cwLetters r n).map fun l => (l.1, l.2.1, e l.2.2) := by
  unfold wordOf cwLetters
  rw [List.map_flatMap]
  congr 1
  funext s
  rw [List.map_filterMap]
  congr 1
  funext a
  split_ifs <;> rfl
end Formalism.L2.G.Model.TS
