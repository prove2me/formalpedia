-- Prove2me | solution 1 for Formalism.L2.Pj.evalAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:40.961831+00:00
-- url     : https://prove2.me/submissions/27d46bce-0912-430c-82ed-97f46c9b722d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
namespace Formalism.L2.Pj
theorem _root_.solution (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f * g) y = evalAt pts mapR f y * evalAt pts mapR g y := by
  unfold evalAt; split_ifs <;> simp
end Formalism.L2.Pj
