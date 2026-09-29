-- Prove2me | solution 1 for Freiman.middleRepair_cert_interpret_uniform
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:53:53.974162+00:00
-- url     : https://prove2.me/submissions/a0b326c7-3661-413c-b925-82f820d1d86e

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

private theorem normalized_idem (c : MiddleCore) : middleNormalized (middleNormalized c) = middleNormalized c := by
  unfold middleNormalized
  split_ifs <;> first | rfl | (simp_all only [not_le]; order)

private theorem bounds_normalized (c : MiddleCore) : middleBounds (middleNormalized c) = middleBounds c := by
  simp only [middleBounds, normalized_idem]

theorem solution :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ c : MiddleCore, middleRegular c → (∃ f : Fin 11, 9≤f.val ∧ middleRepairCertDomain c f.val ∧ middleRepairCertActualFamily c f.val) → middleRepairGood c := by
  intro hcriterion _hchild _horder c hc hex
  obtain ⟨f, hf, _hd, ha⟩ := hex
  have hs := ha ⟨.uniform, ([2],[]), true, ([1],[]), false, []⟩
    (by simp [middleCertSpecs, hf])
  have he := hs (by simp [middleCertHolds])
  apply (hcriterion c hc).mpr
  unfold middleRepairCertSpecHolds at hs
  simp only [middleRepairCertEndpoint, middleRepairCertIncoming, middleRepairAct,
    Bool.false_eq_true, ↓reduceIte] at he
  simp only [middleRepairChild, middleRepairRawChild, bounds_normalized]
  split_ifs with hp
  · simpa only [hp, ↓reduceIte] using he
  · have he' := he
    simp only [hp, ↓reduceIte, neg_le_neg_iff] at he'
    exact he'

#print axioms solution
