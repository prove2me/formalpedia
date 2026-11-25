-- Prove2me | solution 1 for Formalism.L2.Pj.actL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:11.085994+00:00
-- url     : https://prove2.me/submissions/de12a405-cdee-4217-a74a-9cbce7948a34

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply

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
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {G : Type} [Group G]
variable (actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop)
namespace Formalism.L2.Pj
theorem _root_.solution (g : G) (f : Rules pts) (p : TRing K) (y : pts p.R) :
    actL pts actR g f p y = f p (mvPt pts actR g y) := rfl
end Formalism.L2.Pj
