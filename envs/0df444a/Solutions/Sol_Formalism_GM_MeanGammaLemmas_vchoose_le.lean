-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.vchoose_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:26.671799+00:00
-- url     : https://prove2.me/submissions/33ed2e7d-17b9-4bdb-96eb-4c624bb7d711

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) :
    (padicValNat p (n.choose k) : ℝ) ≤ (Nat.log p n : ℝ) := by
  have := Nat.factorization_choose_le_log (p := p) (n := n) (k := k)
  rw [Nat.factorization_def _ hp.out] at this
  exact_mod_cast this
end Formalism.GM.MeanGammaLemmas
