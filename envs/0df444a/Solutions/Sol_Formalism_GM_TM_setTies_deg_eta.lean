-- Prove2me | solution 1 for Formalism.GM.TM.setTies_deg_eta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:03.057451+00:00
-- url     : https://prove2.me/submissions/042a66bf-3dfc-4b02-b49b-dff1ecb4b977

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {N : ℕ}
namespace Formalism.GM.TM
theorem _root_.solution (LL : Letters N) (T : TieData) (hT : StrictMono T.pos) (n : Fin T.t → ℕ) (i : Fin T.t)
    (h : T.pos i + 1 < N) : (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by
  unfold Letters.setTies
  have hex : ∃ j, T.pos j + 1 = ((⟨T.pos i + 1, h⟩ : Fin N) : ℕ) := ⟨i, rfl⟩
  simp only [dif_pos hex]
  congr 1
  have := Classical.choose_spec hex
  exact hT.injective (by simpa using this)
end Formalism.GM.TM
