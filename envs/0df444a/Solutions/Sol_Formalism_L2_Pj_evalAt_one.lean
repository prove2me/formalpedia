-- Prove2me | solution 1 for Formalism.L2.Pj.evalAt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.988038+00:00
-- url     : https://prove2.me/submissions/fa735a35-3d06-492e-bee4-994df199c33c

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
theorem _root_.solution {S : Type} [CommRing S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    evalAt pts mapR (1 : Rules pts) y = 1 := by
  unfold evalAt; rw [dif_pos h]; simp
end Formalism.L2.Pj
