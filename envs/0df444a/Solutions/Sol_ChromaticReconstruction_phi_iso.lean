-- Prove2me | solution 1 for ChromaticReconstruction.phi_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:19.325499+00:00
-- url     : https://prove2.me/submissions/af756bb2-54e4-4897-b03a-a03e2cab1901

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_chromSymm_iso

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G') :
    phi G = phi G' := by
  unfold phi; rw [chromSymm_iso e]
end ChromaticReconstruction
