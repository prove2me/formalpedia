-- Prove2me | solution 1 for Formalism.L2.Th1.E.Main.fac_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:59.792318+00:00
-- url     : https://prove2.me/submissions/a9d64a8c-5038-43ff-b552-f2ea670f2f4c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Main
namespace Formalism.L2.Th1.E.Main
theorem _root_.solution (hF : FacShape) {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
    (W : WeierstrassCurve K) (hW : IntCurve W) {T : Type} [AddCommGroup T]
    (π : T →+ W.toAffine.Point) (hI : IntPts W π) (P Q : T) (hP : π P ≠ 0) (hQ : π Q ≠ 0) :
    ∃ e, UnitAt e (C (px W (π Q)) - xT W (π P)) := by
  obtain ⟨h0, h1, h2⟩ := hF K W hW (π P) (π Q) hP hQ (hI P hP).1 (hI P hP).2 (hI Q hQ).1
    (hI Q hQ).2
    (fun h => by rw [← map_add] at h ⊢; exact (hI _ h).1)
    (fun h => by rw [← map_sub] at h ⊢; exact (hI _ h).1)
  by_cases ha : π P + π Q = 0
  · by_cases hq : π Q + π Q = 0
    · refine ⟨2, h2 ?_ hq⟩
      have : π P - π Q = (π P + π Q) - (π Q + π Q) := by abel
      rw [this, ha, hq, sub_zero]
    · exact ⟨1, h1 (Or.inl ha) hq⟩
  · by_cases hs : π P - π Q = 0
    · by_cases hq : π Q + π Q = 0
      · exact ⟨2, h2 hs hq⟩
      · exact ⟨1, h1 (Or.inr hs) hq⟩
    · exact ⟨0, h0 ha hs⟩
end Formalism.L2.Th1.E.Main
