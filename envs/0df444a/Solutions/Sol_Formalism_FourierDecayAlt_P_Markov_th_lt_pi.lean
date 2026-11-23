-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.th_lt_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:20.691352+00:00
-- url     : https://prove2.me/submissions/fdfe070f-b29f-4e1e-a06f-a71991f28b1f

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution {n k : ℕ} (hk : k < n) : th n k < π := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  unfold th
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos]
end Formalism.FourierDecayAlt.P.Markov
