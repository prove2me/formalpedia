-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.pick_many
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:35.954936+00:00
-- url     : https://prove2.me/submissions/b55bb631-2c09-40ed-ba4d-2425a22b4754

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pick_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (lo hi : ℝ) (B : Finset ℝ) : ∀ (m : ℕ) (Q : Finset ℝ),
    9 * ((Q.card : ℝ) + m + B.card) + 1 ≤ hi - lo →
    ∃ ys : List ℝ, ys.length = m ∧
      (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q|) ∧
      ys.Pairwise (fun y y' => 4 < |y - y'|)
  | 0, Q, _ => ⟨[], rfl, by simp, List.Pairwise.nil⟩
  | m + 1, Q, h => by
    classical
    push_cast at h
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := pick_one lo hi Q B (by linarith)
    have hc : ((insert y Q).card : ℝ) ≤ Q.card + 1 := by exact_mod_cast Finset.card_insert_le y Q
    obtain ⟨ys, hl, hys, hp⟩ := solution lo hi B m (insert y Q) (by linarith)
    refine ⟨y :: ys, by simp [hl], ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨h1, h2, h3, h4, h5⟩
      · obtain ⟨a, b, c, d, e⟩ := hys z hz
        exact ⟨a, b, c, d, fun q hq => e q (Finset.mem_insert_of_mem hq)⟩
    · refine List.Pairwise.cons (fun z hz => ?_) hp
      have := (hys z hz).2.2.2.2 y (Finset.mem_insert_self y Q)
      rwa [abs_sub_comm] at this
end Formalism.FourierDecayAlt.P.PBD
