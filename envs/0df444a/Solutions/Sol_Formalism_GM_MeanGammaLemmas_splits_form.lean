-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.splits_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:04.188295+00:00
-- url     : https://prove2.me/submissions/544daf74-2525-4d99-a511-6789ef584893

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
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution {L : Type} [Field L] [IsAlgClosed L] (Dk : L[X]) :
    Dk = C Dk.leadingCoeff * (Dk.roots.map (fun ζ => X - C ζ)).prod ∧ Dk.roots.card = Dk.natDegree := by
  have hc : Multiset.card Dk.roots = Dk.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits Dk)
  exact ⟨(C_leadingCoeff_mul_prod_multiset_X_sub_C hc).symm, hc⟩
end Formalism.GM.MeanGammaLemmas
