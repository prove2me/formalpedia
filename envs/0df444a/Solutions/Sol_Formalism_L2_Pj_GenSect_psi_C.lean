-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.psi_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:26:10.605039+00:00
-- url     : https://prove2.me/submissions/8c23bae7-a263-4fbd-a3de-dd827304801a

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
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (a : Ω) :
    psi (D := D) x j₀ (C a) = C a := by
  first
  | (rw [psi, aeval_C, MvPolynomial.algebraMap_eq])
  | simp [psi]
  | exact (psi x j₀).commutes a
end Formalism.L2.Pj.GenSect
