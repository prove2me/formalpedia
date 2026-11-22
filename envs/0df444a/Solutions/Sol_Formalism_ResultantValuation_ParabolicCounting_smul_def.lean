-- Prove2me | solution 1 for Formalism.ResultantValuation.ParabolicCounting.smul_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:39.298189+00:00
-- url     : https://prove2.me/submissions/aa296cee-db89-460b-adf4-d44f18121172

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ResultantValuation
open Module
open Formalism.ResultantValuation.ParabolicCounting
variable (F : Type) [Field F] (r t : ℕ)
attribute [local instance] act
namespace Formalism.ResultantValuation.ParabolicCounting
theorem _root_.solution (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    g • W = W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F)) := rfl
end Formalism.ResultantValuation.ParabolicCounting
