-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_Phi_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:18.395682+00:00
-- url     : https://prove2.me/submissions/7c832159-f6a5-4761-a2e8-01df79a1eda9

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
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_Phi (l :: w) G = cwl_tau l (cwl_Phi w G) := rfl
end Formalism.L2.G.Model.TS
