-- Prove2me | solution 1 for CutwidthCircuitLB.claim_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:04:05.140438+00:00
-- url     : https://prove2.me/submissions/04ce09bb-7e57-457c-b30e-dacbb00846a8

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
import Definitions.Def_CutwidthCircuitLB_ROBP_Computes
import Definitions.Def_CutwidthCircuitLB_ROBP_past
import Definitions.Def_CutwidthCircuitLB_ROBP_PSet
import Definitions.Def_CutwidthCircuitLB_ROBP_QSet
import Definitions.Def_CutwidthCircuitLB_rect

open CutwidthCircuitLB in
theorem solution {n : ℕ} (R : ROBP n) (f : (Fin n → Bool) → Bool) (hf : R.Computes f)
    (i : Fin (R.len + 1)) (v : Fin (R.layerSize i)) (x : Fin n → Bool)
    (hx : x ∈ rect (R.past i) (R.PSet i v) (R.QSet i v)) :
    f x = true := by
  classical
  obtain ⟨⟨x1, hx1, vs1, es1, h1s, h1v, h1c⟩, ⟨x2, hx2, vs2, es2, h2v, h2a, h2c⟩⟩ := hx
  apply (hf x).1
  let vs : (t : Fin (R.len + 1)) → Fin (R.layerSize t) := fun t =>
    if t.val < i.val then vs1 t else vs2 t
  let es : (t : Fin R.len) → Fin (R.edges t).length := fun t =>
    if t.val < i.val then es1 t else es2 t
  have hmemPast : ∀ (t : Fin R.len) (j : Fin n), t.val < i.val → R.tag t = some j → j ∈ R.past i := by
    intro t j ht hj
    simp only [ROBP.past, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, ht, hj⟩
  have hnotPast : ∀ (t : Fin R.len) (j : Fin n), i.val ≤ t.val → R.tag t = some j → j ∉ R.past i := by
    intro t j ht hj hjp
    simp only [ROBP.past, Finset.mem_filter, Finset.mem_univ, true_and] at hjp
    obtain ⟨t', ht', hj'⟩ := hjp
    obtain ⟨t0, _, huniq⟩ := R.tag_unique j
    have e1 := huniq t hj
    have e2 := huniq t' hj'
    have : t = t' := e1.trans e2.symm
    rw [this] at ht
    omega
  refine ⟨vs, es, ?_, ?_, ?_⟩
  · -- start
    show (if (0 : Fin (R.len + 1)).val < i.val then vs1 0 else vs2 0) = R.start
    by_cases hi : (0 : Fin (R.len + 1)).val < i.val
    · rw [if_pos hi]; exact h1s
    · rw [if_neg hi]
      have hi0 : i = 0 := Fin.ext (by simp at hi ⊢; omega)
      subst hi0
      rw [h2v, ← h1v, h1s]
  · -- accept
    show (if (Fin.last R.len).val < i.val then vs1 (Fin.last R.len) else vs2 (Fin.last R.len)) = R.accept
    rw [if_neg (by simp; omega)]
    exact h2a
  · intro t _ ht
    by_cases hti : t.val < i.val
    · obtain ⟨c1, c2, c3⟩ := h1c t (Nat.zero_le _) hti
      have hes : es t = es1 t := by simp only [es, if_pos hti]
      have hvs1 : vs t.castSucc = vs1 t.castSucc := by
        simp only [vs, Fin.coe_castSucc, if_pos hti]
      refine ⟨by rw [hes, hvs1]; exact c1, ?_, fun j hj => ?_⟩
      · rw [hes]
        by_cases hsi : t.succ.val < i.val
        · have : vs t.succ = vs1 t.succ := by simp only [vs, if_pos hsi]
          rw [this]; exact c2
        · have : vs t.succ = vs2 t.succ := by simp only [vs, if_neg hsi]
          rw [this]
          have hti' : t.succ = i := Fin.ext (by simp at hsi ⊢; omega)
          rw [c2, hti', h2v, h1v]
      · rw [hes, c3 j hj]
        have hp := hmemPast t j hti hj
        have e1 := hx1 ⟨j, hp⟩
        exact e1
    · have hti' : i.val ≤ t.val := by omega
      obtain ⟨c1, c2, c3⟩ := h2c t hti' ht
      have hes : es t = es2 t := by simp only [es, if_neg hti]
      have hvs1 : vs t.castSucc = vs2 t.castSucc := by
        simp only [vs, Fin.coe_castSucc, if_neg hti]
      have hvs2 : vs t.succ = vs2 t.succ := by
        simp only [vs]; rw [if_neg (by simp; omega)]
      refine ⟨by rw [hes, hvs1]; exact c1, by rw [hes, hvs2]; exact c2, fun j hj => ?_⟩
      rw [hes, c3 j hj]
      have hp := hnotPast t j hti' hj
      have e2 := hx2 ⟨j, Finset.mem_compl.2 hp⟩
      exact e2
