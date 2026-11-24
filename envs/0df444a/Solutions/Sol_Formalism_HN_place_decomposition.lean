-- Prove2me | solution 1 for Formalism.HN.place_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:15.115176+00:00
-- url     : https://prove2.me/submissions/54570c29-58ae-467c-b142-8596e7641d91

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_split_eq
import Theorems.Thm_Formalism_HN_PlaceDecomposition_finrank_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : PlaceSplit := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX N _
  classical
  exact ⟨PlaceDecomposition.split_eq b X N, fun v => PlaceDecomposition.finrank_piece b X hX N v⟩
end Formalism.HN
