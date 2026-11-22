-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:37.618071+00:00
-- url     : https://prove2.me/submissions/b110d1e7-1eab-483a-a978-a43980e80520

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
theorem _root_.solution {a b : ℕ} {u v : MvPolynomial σ K} (hu : BiHom w e a b u) (hv : BiHom w e a b v) :
    BiHom w e a b (u + v) := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hu m h
  · exact hv m h
end Formalism.GM.leadingTermLemmas
