-- Prove2me | solution 1 for Formalism.L2.Pj.hkOp_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:03.608546+00:00
-- url     : https://prove2.me/submissions/c548d358-1fc1-493c-bc7f-7ad033773623

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeStabSet

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
variable (hkIdx : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], pts Ω → Type)
variable (quotR : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), hkIdx Ω y → pts Ω → Prop)
variable {pts mapR borR hkIdx quotR}
namespace Formalism.L2.Pj
theorem _root_.solution [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (f : secW pts mapR borR e) :
    HkRel pts mapR hkIdx quotR c f (hkOp hE hD hF f) := (hE f.1 f.2).choose_spec.2
end Formalism.L2.Pj
