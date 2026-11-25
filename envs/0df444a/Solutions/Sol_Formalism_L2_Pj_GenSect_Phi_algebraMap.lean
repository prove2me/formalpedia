-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.Phi_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:40:20.562815+00:00
-- url     : https://prove2.me/submissions/3180a1fa-04f9-4433-991a-40fa7bdc59ad

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0)
    (a : ΩT Ω D m) :
    Phi x j₀ hinj (algebraMap (ΩT Ω D m) (RS K Ω D m) a) =
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) :=
  IsLocalization.lift_eq _ _
end Formalism.L2.Pj.GenSect
