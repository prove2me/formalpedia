-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_supp_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:42.805384+00:00
-- url     : https://prove2.me/submissions/cf0146e5-4533-434e-a446-fc39d635f5fa

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_nonvanish
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_exists_max_above


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
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (a : qb_Idx CF → F)
    (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu (∑ x, a x • qb_vecF CF F x) = 0) :
    ∀ x, a x ≠ 0 → CF.mu x.1 ∈ pi := by
  classical
  intro x0 hx0
  by_contra hn
  let s : Finset (Fin n → ℤ) := (univ.filter fun x => a x ≠ 0).image fun x => CF.mu x.1
  have hs0 : CF.mu x0.1 ∈ s := mem_image.2 ⟨x0, by simp [hx0], rfl⟩
  obtain ⟨nu, hnu, hle, hmax⟩ := qb_exists_max_above s hs0
  obtain ⟨x1, hx1, rfl⟩ := mem_image.1 hnu
  have hx1' : a x1 ≠ 0 := (mem_filter.1 hx1).2
  have hout : CF.mu x1.1 ∉ pi := fun hin => hn (hpi.2 _ hin _ (CF.dom _) hle)
  exact hx1' (qb_nonvanish hA CF F a (CF.mu x1.1)
    (fun x hx hle' => hmax _ (mem_image.2 ⟨x, by simp [hx], rfl⟩) hle') (h _ (CF.dom _) hout) x1 rfl)
end Formalism.InvariantFactorPaths.ColumnFamilies
