-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_emb_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:27.891906+00:00
-- url     : https://prove2.me/submissions/c86621f5-06db-4a83-b477-11402a87238f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite

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
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {k : ℕ} (h : S.card = k) (h' : (insert (Fin.last m) (S.map Fin.castSuccEmb)).card = k + 1) :
    ⇑((insert (Fin.last m) (S.map Fin.castSuccEmb)).orderEmbOfFin h') =
      Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (S.orderEmbOfFin h a).castSucc) (Fin.last m) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    induction a using Fin.lastCases with
    | last => simp
    | cast a => simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Fin.castSucc_lt_last _
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt.2 (Fin.le_last _))
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono (Fin.castSucc_lt_castSucc_iff.1 hab))
end Formalism.InvariantFactorPaths.ColumnFamilies
