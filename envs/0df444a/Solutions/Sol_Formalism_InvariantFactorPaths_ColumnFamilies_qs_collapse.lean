-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_collapse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:02.090144+00:00
-- url     : https://prove2.me/submissions/80bad6be-7e76-4f55-afd2-1b231e9d6df8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_res
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) (P : Prop) [Decidable P]
    (F : ℤ → Finset (Fin n)) (hF : P → ∀ c, (F c).card = colH mu c) (f : (ℤ → Finset (Fin n)) → M)
    [∀ I : TIdx mu, Decidable (P ∧ qs_ext mu I = F)] :
    ∑ I : TIdx mu, (if P ∧ qs_ext mu I = F then f (qs_ext mu I) else 0) = if P then f F else 0 := by
  classical
  split_ifs with hP
  · rw [Finset.sum_eq_single (qs_res mu F (hF hP))]
    · rw [if_pos ⟨hP, qs_ext_res hmu F (hF hP)⟩, qs_ext_res hmu]
    · intro I _ hI
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hI (qs_ext_inj mu (by rw [h, qs_ext_res hmu]))
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun I _ => if_neg fun h => hP h.1
end Formalism.InvariantFactorPaths.ColumnFamilies
