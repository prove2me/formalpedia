-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.psi_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:25:11.666991+00:00
-- url     : https://prove2.me/submissions/2c22708e-dfeb-430b-9897-199e44cc574a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA

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
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) :
    psi x j₀ (X p) = gs x j₀ p := by
  first
  | (rw [psi, aeval_X])
  | simp [psi]
end Formalism.L2.Pj.GenSect
