-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:09.157874+00:00
-- url     : https://prove2.me/submissions/bb4828b6-aa6c-4bae-94e1-c4a62fc2c31c

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {a b : ℕ} (c : K) {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e a b (c • u) := fun m hm => hu m (support_smul hm)
end Formalism.GM.leadingTermLemmas
