-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_eq_span_tableauBideterminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:21.563296+00:00
-- url     : https://prove2.me/submissions/12d35ca1-0c24-43d8-906f-d2df4a213952

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_eq_span_standard_tableauBideterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) = Submodule.span B (Set.range fun I : TIdx mu => qa_P B I) := by
  apply le_antisymm
  · rw [dualWeyl_eq_span_standard_tableauBideterminant B hmu]
    apply Submodule.span_mono
    rintro _ ⟨I, rfl⟩
    exact ⟨I.1, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I
end Formalism.InvariantFactorPaths.ColumnFamilies
