-- Prove2me | solution 1 for CongestionApproxPNE.case_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:20:26.017532+00:00
-- url     : https://prove2.me/submissions/9016625d-cd72-4384-9b92-5179469c2e1b

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_HarksKlimm_Consistency_load
import Definitions.Def_CongestionApproxPNE_playerCost
import Definitions.Def_CongestionApproxPNE_gadget

set_option autoImplicit false
open scoped NNReal

namespace Aux_CongestionApproxPNE_case_one

open HarksKlimm.Consistency CongestionApproxPNE

variable {d n k : ℕ} {w : ℝ≥0} {hw : 0 < w} {β : ℝ}

lemma AB (a b : Fin (n + 1)) : Fin.castAdd (n + 1) a ≠ Fin.natAdd (n + 1) b := by
  intro h
  have h1 := congrArg Fin.val h
  rw [Fin.coe_castAdd, Fin.coe_natAdd] at h1
  have := a.isLt
  omega

lemma BA (a b : Fin (n + 1)) : Fin.natAdd (n + 1) b ≠ Fin.castAdd (n + 1) a :=
  (AB a b).symm

lemma AA {a b : Fin (n + 1)} (hab : a ≠ b) : Fin.castAdd (n + 1) a ≠ Fin.castAdd (n + 1) b := by
  intro h
  apply hab
  have h1 := congrArg Fin.val h
  rw [Fin.coe_castAdd, Fin.coe_castAdd] at h1
  exact Fin.ext h1

lemma BB {a b : Fin (n + 1)} (hab : a ≠ b) : Fin.natAdd (n + 1) a ≠ Fin.natAdd (n + 1) b := by
  intro h
  apply hab
  have h1 := congrArg Fin.val h
  rw [Fin.coe_natAdd, Fin.coe_natAdd] at h1
  exact Fin.ext (by omega)

lemma notmem_pair {N : ℕ} {x a b : Fin N} (h1 : x ≠ a) (h2 : x ≠ b) :
    x ∉ ({a, b} : Finset (Fin N)) := by
  simp [h1, h2]

lemma B_notin_imA (b : Fin (n + 1)) :
    Fin.natAdd (n + 1) b ∉ Finset.univ.image (Fin.castAdd (n + 1)) := by
  rw [Finset.mem_image]
  rintro ⟨x, _, hx⟩
  exact AB x b hx

lemma A_notin_imB (a : Fin (n + 1)) :
    Fin.castAdd (n + 1) a ∉ Finset.univ.image (Fin.natAdd (n + 1)) := by
  rw [Finset.mem_image]
  rintro ⟨x, _, hx⟩
  exact AB a x hx.symm

lemma demand0 : (gadget d n k w hw β).demand 0 = 1 := by simp [gadget]

lemma demandi {j : Fin (n + 1)} (hj : j ≠ 0) : (gadget d n k w hw β).demand j = w := by
  simp [gadget, hj]

lemma cost_hubA (x : ℝ≥0) :
    (gadget d n k w hw β).cost (Fin.castAdd (n + 1) 0) x = (x : ℝ) ^ k := by
  simp [gadget]

lemma cost_hubB (x : ℝ≥0) :
    (gadget d n k w hw β).cost (Fin.natAdd (n + 1) 0) x = (x : ℝ) ^ k := by
  simp [gadget]

lemma cost_other (f : Fin ((n + 1) + (n + 1))) (h1 : f ≠ Fin.castAdd (n + 1) 0)
    (h2 : f ≠ Fin.natAdd (n + 1) 0) (x : ℝ≥0) :
    (gadget d n k w hw β).cost f x = β * (x : ℝ) ^ d := by
  show (if f = Fin.castAdd (n + 1) 0 ∨ f = Fin.natAdd (n + 1) 0 then (x : ℝ) ^ k
    else β * (x : ℝ) ^ d) = β * (x : ℝ) ^ d
  rw [if_neg (by rintro (h | h) <;> contradiction)]

lemma strat0 (S : Finset (Fin ((n + 1) + (n + 1))))
    (hS : S ∈ (gadget d n k w hw β).strategies 0) :
    S = Finset.univ.image (Fin.castAdd (n + 1)) ∨ S = Finset.univ.image (Fin.natAdd (n + 1)) := by
  simpa [gadget] using hS

lemma strati {i : Fin (n + 1)} (hi : i ≠ 0) (S : Finset (Fin ((n + 1) + (n + 1))))
    (hS : S ∈ (gadget d n k w hw β).strategies i) :
    S = {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) i} ∨
      S = {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) i} := by
  simpa [gadget, hi] using hS

lemma memA (j m : Fin n) :
    Fin.castAdd (n + 1) j.succ ∈
      ({Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ} : Finset (Fin ((n + 1) + (n + 1))))
      ↔ j = m := by
  constructor
  · intro hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (AB j.succ 0 h).elim
    · by_contra hjm
      exact AA (fun e => hjm (Fin.succ_injective _ e)) h
  · rintro rfl
    simp

lemma memB (j m : Fin n) :
    Fin.natAdd (n + 1) j.succ ∈
      ({Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ} : Finset (Fin ((n + 1) + (n + 1))))
      ↔ j = m := by
  constructor
  · intro hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (BA 0 j.succ h).elim
    · by_contra hjm
      exact BB (fun e => hjm (Fin.succ_injective _ e)) h
  · rintro rfl
    simp

lemma sum_none (L : Fin n → Finset (Fin ((n + 1) + (n + 1)))) (f : Fin ((n + 1) + (n + 1)))
    (h : ∀ m, f ∉ L m) : ∑ m : Fin n, (if f ∈ L m then w else 0) = 0 :=
  Finset.sum_eq_zero fun m _ => if_neg (h m)

lemma sum_all (L : Fin n → Finset (Fin ((n + 1) + (n + 1)))) (f : Fin ((n + 1) + (n + 1)))
    (h : ∀ m, f ∈ L m) : ∑ m : Fin n, (if f ∈ L m then w else 0) = (n : ℝ≥0) * w := by
  rw [Finset.sum_congr rfl fun m _ => if_pos (h m)]
  simp

lemma sum_one (L : Fin n → Finset (Fin ((n + 1) + (n + 1)))) (f : Fin ((n + 1) + (n + 1)))
    (j : Fin n) (h : ∀ m, f ∈ L m ↔ j = m) : ∑ m : Fin n, (if f ∈ L m then w else 0) = w := by
  have e : ∀ m : Fin n, (if f ∈ L m then w else 0) = if j = m then w else 0 := by
    intro m
    by_cases hm : j = m
    · rw [if_pos ((h m).mpr hm), if_pos hm]
    · rw [if_neg (fun hf => hm ((h m).mp hf)), if_neg hm]
  rw [Finset.sum_congr rfl fun m _ => e m]
  simp

lemma load_eval (p : (gadget d n k w hw β).Profile) (H : Finset (Fin ((n + 1) + (n + 1))))
    (L : Fin n → Finset (Fin ((n + 1) + (n + 1))))
    (hH : (p 0).val = H) (hL : ∀ m : Fin n, (p m.succ).val = L m) (f : Fin ((n + 1) + (n + 1))) :
    load (gadget d n k w hw β) p f =
      (if f ∈ H then 1 else 0) + ∑ m : Fin n, (if f ∈ L m then w else 0) := by
  unfold load
  rw [Fin.sum_univ_succ, hH, demand0]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hL m, demandi (Fin.succ_ne_zero m)]

lemma sum_imA (g : Fin ((n + 1) + (n + 1)) → ℝ) :
    ∑ f ∈ Finset.univ.image (Fin.castAdd (n + 1)), g f =
      g (Fin.castAdd (n + 1) 0) + ∑ j : Fin n, g (Fin.castAdd (n + 1) j.succ) := by
  have hinj : Function.Injective (Fin.castAdd (n + 1) : Fin (n + 1) → Fin ((n + 1) + (n + 1))) :=
    fun a b hab => by_contra fun hne => AA hne hab
  rw [Finset.sum_image hinj.injOn, Fin.sum_univ_succ]

lemma sum_imB (g : Fin ((n + 1) + (n + 1)) → ℝ) :
    ∑ f ∈ Finset.univ.image (Fin.natAdd (n + 1)), g f =
      g (Fin.natAdd (n + 1) 0) + ∑ j : Fin n, g (Fin.natAdd (n + 1) j.succ) := by
  have hinj : Function.Injective (Fin.natAdd (n + 1) : Fin (n + 1) → Fin ((n + 1) + (n + 1))) :=
    fun a b hab => by_contra fun hne => BB hne hab
  rw [Finset.sum_image hinj.injOn, Fin.sum_univ_succ]

lemma memImA (a : Fin (n + 1)) :
    Fin.castAdd (n + 1) a ∈ Finset.univ.image (Fin.castAdd (n + 1)) :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

lemma memImB (a : Fin (n + 1)) :
    Fin.natAdd (n + 1) a ∈ Finset.univ.image (Fin.natAdd (n + 1)) :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

end Aux_CongestionApproxPNE_case_one

open Aux_CongestionApproxPNE_case_one in
open HarksKlimm.Consistency CongestionApproxPNE in
theorem solution (d n k : ℕ) (w : ℝ≥0) (hw : 0 < w) (β : ℝ) (hd : 2 ≤ d) (hk1 : 1 ≤ k)
    (hkd : k ≤ d) (hw1 : w ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (s : (gadget d n k w hw β).Profile) (h : Fin ((n + 1) + (n + 1)))
    (hh : h = Fin.castAdd (n + 1) 0 ∨ h = Fin.natAdd (n + 1) 0)
    (hheavy : h ∈ (s 0).val) (halone : ∀ i : Fin (n + 1), i ≠ 0 → h ∉ (s i).val) :
    playerCost (gadget d n k w hw β) s 0 = 1 + (n : ℝ) * β * (1 + (w : ℝ)) ^ d ∧
      ∀ t : (gadget d n k w hw β).Strategy 0, t ≠ s 0 →
        playerCost (gadget d n k w hw β) (Function.update s 0 t) 0 =
          (1 + (n : ℝ) * (w : ℝ)) ^ k + (n : ℝ) * β := by
  rcases hh with rfl | rfl
  · -- heavy player alone on a₀
    have hs0 : (s 0).val = Finset.univ.image (Fin.castAdd (n + 1)) := by
      rcases strat0 _ (s 0).2 with h0 | h0
      · exact h0
      · exact (A_notin_imB 0 (h0 ▸ hheavy)).elim
    have hl : ∀ m : Fin n,
        (s m.succ).val = {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ} := by
      intro m
      rcases strati (Fin.succ_ne_zero m) _ (s m.succ).2 with h1 | h1
      · exact (halone m.succ (Fin.succ_ne_zero m) (by rw [h1]; simp)).elim
      · exact h1
    refine ⟨?_, ?_⟩
    · have e0 : (gadget d n k w hw β).cost (Fin.castAdd (n + 1) 0)
          (load (gadget d n k w hw β) s (Fin.castAdd (n + 1) 0)) = 1 := by
        rw [load_eval s _ (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) hs0 hl,
          if_pos (memImA 0),
          sum_none (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) _
            (fun m => notmem_pair (AB 0 0) (AA (Fin.succ_ne_zero m).symm)),
          add_zero, cost_hubA]
        simp
      have ej : ∀ j : Fin n, (gadget d n k w hw β).cost (Fin.castAdd (n + 1) j.succ)
          (load (gadget d n k w hw β) s (Fin.castAdd (n + 1) j.succ)) =
            β * (1 + (w : ℝ)) ^ d := by
        intro j
        rw [load_eval s _ (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) hs0 hl,
          if_pos (memImA j.succ),
          sum_one (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) _ j
            (fun m => memA j m),
          cost_other _ (AA (Fin.succ_ne_zero j)) (AB j.succ 0), NNReal.coe_add, NNReal.coe_one]
      unfold playerCost
      rw [hs0, sum_imA, e0]
      simp only [ej]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    · intro t ht
      have ht' : t.val = Finset.univ.image (Fin.natAdd (n + 1)) := by
        rcases strat0 _ t.2 with h1 | h1
        · exact absurd (Subtype.ext (h1.trans hs0.symm)) ht
        · exact h1
      have hs'0 : (Function.update s 0 t 0).val = Finset.univ.image (Fin.natAdd (n + 1)) := by
        rw [Function.update_self]
        exact ht'
      have hl' : ∀ m : Fin n, (Function.update s 0 t m.succ).val =
          {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ} := by
        intro m
        rw [Function.update_of_ne (Fin.succ_ne_zero m)]
        exact hl m
      have e0 : (gadget d n k w hw β).cost (Fin.natAdd (n + 1) 0)
          (load (gadget d n k w hw β) (Function.update s 0 t) (Fin.natAdd (n + 1) 0)) =
            (1 + (n : ℝ) * (w : ℝ)) ^ k := by
        rw [load_eval _ _ (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) hs'0 hl',
          if_pos (memImB 0),
          sum_all (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) _
            (fun m => by simp),
          cost_hubB]
        push_cast
        first | done | ring
      have ej : ∀ j : Fin n, (gadget d n k w hw β).cost (Fin.natAdd (n + 1) j.succ)
          (load (gadget d n k w hw β) (Function.update s 0 t) (Fin.natAdd (n + 1) j.succ)) =
            β := by
        intro j
        rw [load_eval _ _ (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) hs'0 hl',
          if_pos (memImB j.succ),
          sum_none (fun m => {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) m.succ}) _
            (fun m => notmem_pair (BB (Fin.succ_ne_zero j)) (BA m.succ j.succ)),
          add_zero, cost_other _ (BA 0 j.succ) (BB (Fin.succ_ne_zero j))]
        simp
      unfold playerCost
      rw [hs'0, sum_imB, e0]
      simp only [ej]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · -- heavy player alone on b₀
    have hs0 : (s 0).val = Finset.univ.image (Fin.natAdd (n + 1)) := by
      rcases strat0 _ (s 0).2 with h0 | h0
      · exact (B_notin_imA 0 (h0 ▸ hheavy)).elim
      · exact h0
    have hl : ∀ m : Fin n,
        (s m.succ).val = {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ} := by
      intro m
      rcases strati (Fin.succ_ne_zero m) _ (s m.succ).2 with h1 | h1
      · exact h1
      · exact (halone m.succ (Fin.succ_ne_zero m) (by rw [h1]; simp)).elim
    refine ⟨?_, ?_⟩
    · have e0 : (gadget d n k w hw β).cost (Fin.natAdd (n + 1) 0)
          (load (gadget d n k w hw β) s (Fin.natAdd (n + 1) 0)) = 1 := by
        rw [load_eval s _ (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) hs0 hl,
          if_pos (memImB 0),
          sum_none (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) _
            (fun m => notmem_pair (BA 0 0) (BB (Fin.succ_ne_zero m).symm)),
          add_zero, cost_hubB]
        simp
      have ej : ∀ j : Fin n, (gadget d n k w hw β).cost (Fin.natAdd (n + 1) j.succ)
          (load (gadget d n k w hw β) s (Fin.natAdd (n + 1) j.succ)) =
            β * (1 + (w : ℝ)) ^ d := by
        intro j
        rw [load_eval s _ (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) hs0 hl,
          if_pos (memImB j.succ),
          sum_one (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) _ j
            (fun m => memB j m),
          cost_other _ (BA 0 j.succ) (BB (Fin.succ_ne_zero j)), NNReal.coe_add, NNReal.coe_one]
      unfold playerCost
      rw [hs0, sum_imB, e0]
      simp only [ej]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    · intro t ht
      have ht' : t.val = Finset.univ.image (Fin.castAdd (n + 1)) := by
        rcases strat0 _ t.2 with h1 | h1
        · exact h1
        · exact absurd (Subtype.ext (h1.trans hs0.symm)) ht
      have hs'0 : (Function.update s 0 t 0).val = Finset.univ.image (Fin.castAdd (n + 1)) := by
        rw [Function.update_self]
        exact ht'
      have hl' : ∀ m : Fin n, (Function.update s 0 t m.succ).val =
          {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ} := by
        intro m
        rw [Function.update_of_ne (Fin.succ_ne_zero m)]
        exact hl m
      have e0 : (gadget d n k w hw β).cost (Fin.castAdd (n + 1) 0)
          (load (gadget d n k w hw β) (Function.update s 0 t) (Fin.castAdd (n + 1) 0)) =
            (1 + (n : ℝ) * (w : ℝ)) ^ k := by
        rw [load_eval _ _ (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) hs'0 hl',
          if_pos (memImA 0),
          sum_all (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) _
            (fun m => by simp),
          cost_hubA]
        push_cast
        first | done | ring
      have ej : ∀ j : Fin n, (gadget d n k w hw β).cost (Fin.castAdd (n + 1) j.succ)
          (load (gadget d n k w hw β) (Function.update s 0 t) (Fin.castAdd (n + 1) j.succ)) =
            β := by
        intro j
        rw [load_eval _ _ (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) hs'0 hl',
          if_pos (memImA j.succ),
          sum_none (fun m => {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) m.succ}) _
            (fun m => notmem_pair (AA (Fin.succ_ne_zero j)) (AB j.succ m.succ)),
          add_zero, cost_other _ (AA (Fin.succ_ne_zero j)) (AB j.succ 0)]
        simp
      unfold playerCost
      rw [hs'0, sum_imA, e0]
      simp only [ej]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
