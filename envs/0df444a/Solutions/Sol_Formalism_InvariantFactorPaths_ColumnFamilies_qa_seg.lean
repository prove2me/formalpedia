-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_seg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.010687+00:00
-- url     : https://prove2.me/submissions/d9dd6b01-e5ae-4f91-8195-48fb9b417948

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (L U : ℤ) (Q : ℤ → Prop) [DecidablePred Q] (hQ : ∀ c, L < c → c + 1 ≤ U → Q (c + 1) → Q c)
    (c : ℤ) (hc : c ∈ Finset.Ioc L U) : Q c ↔ c - L ≤ ((Finset.Ioc L U).filter Q).card := by
  rw [Finset.mem_Ioc] at hc
  have hdown : ∀ k : ℕ, ∀ d, L < d → d + k ≤ U → Q (d + k) → Q d := by
    intro k
    induction k with
    | zero => intro d _ _ h; simpa using h
    | succ k ih =>
      intro d hd hU h
      apply ih d hd (by push_cast at hU; omega)
      apply hQ _ (by omega) (by push_cast at hU; omega)
      have : d + (k : ℤ) + 1 = d + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact h
  have hdown' : ∀ d e, L < d → d ≤ e → e ≤ U → Q e → Q d := by
    intro d e hd hde he h
    have := hdown (e - d).toNat d hd (by omega)
    apply this
    have h3 : d + ((e - d).toNat : ℤ) = e := by omega
    rw [h3]; exact h
  constructor
  · intro h
    have : Finset.Ioc L c ⊆ (Finset.Ioc L U).filter Q := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hd.1, hd.2.trans hc.2⟩, hdown' d c hd.1 hd.2 hc.2 h⟩
    have h2 := Finset.card_le_card this
    rw [Int.card_Ioc] at h2
    omega
  · intro h
    by_contra hn
    have : (Finset.Ioc L U).filter Q ⊆ Finset.Ioo L c := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd
      rw [Finset.mem_Ioo]
      refine ⟨hd.1.1, ?_⟩
      by_contra hle
      exact hn (hdown' c d hc.1 (not_lt.mp hle) hd.1.2 hd.2)
    have h2 := Finset.card_le_card this
    rw [Int.card_Ioo] at h2
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
