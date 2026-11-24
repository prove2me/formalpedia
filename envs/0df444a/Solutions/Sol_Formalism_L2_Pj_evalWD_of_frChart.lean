-- Prove2me | solution 1 for Formalism.L2.Pj.evalWD_of_frChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:49.69133+00:00
-- url     : https://prove2.me/submissions/50458ff0-b621-4ef4-8ea7-816110b6bf53

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Theorems.Thm_Formalism_L2_Pj_chartAt_val
import Theorems.Thm_Formalism_L2_Pj_eq_of_locM

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
variable {pts mapR borR}
namespace Formalism.L2.Pj
theorem _root_.solution (h : FrChart pts mapR) : EvalWD pts mapR := by
  intro f hf S _ _ p q φ ψ y z w hy hz
  apply eq_of_locM (K := K)
  intro m hm
  haveI := hm
  obtain ⟨A, u, c, hc⟩ := h S w m
  rw [chartAt_val hf hc hy, chartAt_val hf hc hz]
end Formalism.L2.Pj
