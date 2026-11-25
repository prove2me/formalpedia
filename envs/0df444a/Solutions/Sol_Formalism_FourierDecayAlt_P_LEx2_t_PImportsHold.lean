-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_PImportsHold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:03.723216+00:00
-- url     : https://prove2.me/submissions/de86230a-be85-4c4f-9b24-6f0a1b0e2bb5

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : PImportsHold := by
  intro hPR hFit S hL h6 hn hRoots w hlen
  obtain ⟨hsub, _, _⟩ := hFit S hL h6
  have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
  have hI : S.α < S.β := by nlinarith
  have hJ : (S.step w).J = S.box w.length := by
    simp [Step.J, Sys.box, S.step_a, S.step_L]
  have hPf : (S.step w).P = fun Y => ∏ s, (Y + S.lam s) := by funext Y; exact S.step_P w Y
  have hmid := hsub w.length hlen
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hPf]
    apply Continuous.continuousOn
    fun_prop
  · intro Y hY h0
    rw [hJ] at hY
    have hm := hmid hY
    rw [S.step_P, Finset.prod_eq_zero_iff] at h0
    obtain ⟨s, _, hs⟩ := h0
    apply hRoots s
    have : -S.lam s = Y := by linarith
    rw [this]
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · intro Y s hY hYs
    rw [hJ] at hY hYs
    have hm := hmid hY
    have hms := hmid hYs
    rw [S.step_P, S.step_P]
    have hs : |(-s)| ≤ S.L := by
      rw [abs_neg, abs_le]
      constructor <;> linarith [hY.1, hY.2, hYs.1, hYs.2]
    have := hPR _ S.lam S.α S.β S.L (Y + s) (-s) hI
      (fun t ht => hRoots t ⟨ht.1.le, ht.2.le⟩) (by linarith) hn hs hms.1 hms.2
      (by rw [add_neg_cancel_right]; exact hm.1) (by rw [add_neg_cancel_right]; exact hm.2)
    simpa [add_neg_cancel_right] using this
end Formalism.FourierDecayAlt.P.LEx2
