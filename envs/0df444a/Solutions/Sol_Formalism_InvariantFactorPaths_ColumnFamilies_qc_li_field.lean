-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_li_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:51.494218+00:00
-- url     : https://prove2.me/submissions/703579ff-fb23-42e9-9d8c-33a43c96d1b1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_span_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_card_eq

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
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) (F : Type) [Field F] :
    LinearIndependent F (fun i => mapCoord (n := n) F (β i)) := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h1 := linearIndependent_iff_card_eq_finrank_span.1 (hA n mu hmu F)
  have h2 : Set.range (fun i => mapCoord (n := n) F (β i)) = mapCoord (n := n) F '' Set.range β := by
    rw [← Set.range_comp]; rfl
  have h3 : Set.range (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1)) =
      mapCoord (n := n) F '' Set.range (fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [← Set.range_comp]; rfl
  have h4 := qc_span_eq (F := F) (mapCoord (n := n) F) _ _ (hβ.2.1.trans (hS n mu hmu).2.symm)
  rw [Set.finrank, h2, h4, ← h3, ← Set.finrank, ← h1, qc_card_eq hS hmu hβ, dMu, Nat.card_eq_fintype_card]
end Formalism.InvariantFactorPaths.ColumnFamilies
