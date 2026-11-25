-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.instance_lattice_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:43:14.135956+00:00
-- url     : https://prove2.me/submissions/564e6a2c-88ff-4f8f-af8c-03a636a12f73

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : InstLatticeSums := by
  intro hL hI hB h1 h2 h3 h4 h5 h6
  obtain ⟨C, hC, H⟩ := hL hB
  refine ⟨C * 2 ^ ((5:ℝ) - 5 / 2), ?_, ?_⟩
  · have : (1:ℝ) ≤ 2 ^ ((5:ℝ) - 5 / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  intro E W _ _ _ D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hI' hΘ hG
  obtain ⟨hs, hid, _⟩ := hI h1 h2 h3 h4 h5 h6 E W D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hI' (by linarith) hG
  refine ⟨hs, ?_⟩
  have hK : D.K = 5 := hInst.2.1
  have := H E W D e _ _ Θ 2 hInst.2.2.1 (by omega) (by norm_num) (by linarith) hid
  rw [hK] at this ⊢
  simpa using this
end Formalism.FourierDecayAlt.P
