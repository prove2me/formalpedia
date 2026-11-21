-- Prove2me | solution 1 for CongestionApproxPNE.case_two
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:13:55.335178+00:00
-- url     : https://prove2.me/submissions/f38cb823-aaca-4304-83fb-e14d251abb0c

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_HarksKlimm_Consistency_load
import Definitions.Def_CongestionApproxPNE_playerCost
import Definitions.Def_CongestionApproxPNE_gadget

set_option autoImplicit false
open scoped NNReal

namespace Aux_CongestionApproxPNE_case_two

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

lemma load_ge_two (s : (gadget d n k w hw β).Profile) (f : Fin ((n + 1) + (n + 1)))
    (i : Fin (n + 1)) (hi : i ≠ 0) (h0 : f ∈ (s 0).val) (hi' : f ∈ (s i).val) :
    (1 + w : ℝ≥0) ≤ load (gadget d n k w hw β) s f := by
  unfold load
  have hsub := Finset.sum_le_sum_of_subset
    (f := fun j => if f ∈ (s j).val then (gadget d n k w hw β).demand j else 0)
    (Finset.subset_univ ({0, i} : Finset (Fin (n + 1))))
  rw [Finset.sum_pair (Ne.symm hi)] at hsub
  simp only [if_pos h0, if_pos hi', demand0, demandi hi] at hsub
  exact hsub

lemma load_ge_one (s : (gadget d n k w hw β).Profile) (f : Fin ((n + 1) + (n + 1)))
    (j : Fin (n + 1)) (hj : f ∈ (s j).val) :
    (gadget d n k w hw β).demand j ≤ load (gadget d n k w hw β) s f := by
  unfold load
  have h := Finset.single_le_sum
    (f := fun j => if f ∈ (s j).val then (gadget d n k w hw β).demand j else 0)
    (fun _ _ => zero_le) (Finset.mem_univ j)
  simp only [if_pos hj] at h
  exact h

lemma load_le_hub (s : (gadget d n k w hw β).Profile) (f : Fin ((n + 1) + (n + 1)))
    (h0 : f ∉ (s 0).val) :
    load (gadget d n k w hw β) s f ≤ (n : ℝ≥0) * w := by
  unfold load
  rw [Fin.sum_univ_succ]
  simp only [if_neg h0, zero_add]
  calc ∑ j : Fin n, (if f ∈ (s j.succ).val then (gadget d n k w hw β).demand j.succ else 0)
      ≤ ∑ _j : Fin n, w := Finset.sum_le_sum fun j _ => by
        split_ifs
        · exact (demandi (Fin.succ_ne_zero j)).le
        · exact zero_le
    _ = (n : ℝ≥0) * w := by simp

lemma load_le_priv (s : (gadget d n k w hw β).Profile) (f : Fin ((n + 1) + (n + 1)))
    (i : Fin (n + 1)) (hi : i ≠ 0) (hpriv : ∀ j, j ≠ 0 → j ≠ i → f ∉ (s j).val) :
    load (gadget d n k w hw β) s f ≤ 1 + w := by
  unfold load
  rw [Fintype.sum_eq_add 0 i (Ne.symm hi)]
  swap
  · intro j hj
    exact if_neg (hpriv j hj.1 hj.2)
  try dsimp only
  apply add_le_add
  · split_ifs
    · exact demand0.le
    · exact zero_le
  · split_ifs
    · exact (demandi hi).le
    · exact zero_le

end Aux_CongestionApproxPNE_case_two

open Aux_CongestionApproxPNE_case_two in
open HarksKlimm.Consistency CongestionApproxPNE in
theorem solution (d n k : ℕ) (w : ℝ≥0) (hw : 0 < w) (β : ℝ) (hd : 2 ≤ d) (hk1 : 1 ≤ k)
    (hkd : k ≤ d) (hw1 : w ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (s : (gadget d n k w hw β).Profile) (h : Fin ((n + 1) + (n + 1)))
    (hh : h = Fin.castAdd (n + 1) 0 ∨ h = Fin.natAdd (n + 1) 0)
    (i : Fin (n + 1)) (hi : i ≠ 0) (hheavy : h ∈ (s 0).val) (hshare : h ∈ (s i).val) :
    (1 + (w : ℝ)) ^ k + β * (w : ℝ) ^ d ≤ playerCost (gadget d n k w hw β) s i ∧
      ∀ t : (gadget d n k w hw β).Strategy i, t ≠ s i →
        playerCost (gadget d n k w hw β) (Function.update s i t) i ≤
          ((n : ℝ) * (w : ℝ)) ^ k + β * (1 + (w : ℝ)) ^ d := by
  have h0i : (0 : Fin (n + 1)) ≠ i := Ne.symm hi
  rcases hh with rfl | rfl
  · -- heavy player and player i share the hub a₀
    have hs0 : (s 0).val = Finset.univ.image (Fin.castAdd (n + 1)) := by
      rcases strat0 _ (s 0).2 with h0 | h0
      · exact h0
      · exact (A_notin_imB 0 (h0 ▸ hheavy)).elim
    have hsi : (s i).val = {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) i} := by
      rcases strati hi _ (s i).2 with h1 | h1
      · exact h1
      · exact (notmem_pair (AB 0 0) (AA h0i) (h1 ▸ hshare)).elim
    refine ⟨?_, ?_⟩
    · have L1 := load_ge_two s _ i hi hheavy hshare
      have L2 := load_ge_one s (Fin.natAdd (n + 1) i) i (by rw [hsi]; simp)
      rw [demandi hi] at L2
      have L1r : 1 + (w : ℝ) ≤ (load (gadget d n k w hw β) s (Fin.castAdd (n + 1) 0) : ℝ) := by
        exact_mod_cast L1
      have L2r : (w : ℝ) ≤ (load (gadget d n k w hw β) s (Fin.natAdd (n + 1) i) : ℝ) := by
        exact_mod_cast L2
      unfold playerCost
      rw [hsi, Finset.sum_pair (AB 0 i), cost_hubA,
        cost_other _ (BA 0 i) (BB hi)]
      exact add_le_add (pow_le_pow_left₀ (by positivity) L1r k)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) L2r d) hβ0)
    · intro t ht
      have htv : t.val = {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) i} := by
        rcases strati hi _ t.2 with h1 | h1
        · exact absurd (Subtype.ext (h1.trans hsi.symm)) ht
        · exact h1
      have hs'0 : (Function.update s i t 0).val = (s 0).val := by
        rw [Function.update_of_ne h0i]
      have U1 := load_le_hub (Function.update s i t) (Fin.natAdd (n + 1) 0)
        (by rw [hs'0, hs0]; exact B_notin_imA 0)
      have U2 := load_le_priv (Function.update s i t) (Fin.castAdd (n + 1) i) i hi
        (fun j hj0 hji => by
          rw [Function.update_of_ne hji]
          rcases strati hj0 _ (s j).2 with h1 | h1
          · rw [h1]; exact notmem_pair (AA hi) (AB i j)
          · rw [h1]; exact notmem_pair (AB i 0) (AA (Ne.symm hji)))
      have U1r : (load (gadget d n k w hw β) (Function.update s i t) (Fin.natAdd (n + 1) 0) : ℝ)
          ≤ (n : ℝ) * (w : ℝ) := by exact_mod_cast U1
      have U2r : (load (gadget d n k w hw β) (Function.update s i t) (Fin.castAdd (n + 1) i) : ℝ)
          ≤ 1 + (w : ℝ) := by exact_mod_cast U2
      unfold playerCost
      rw [Function.update_self, htv, Finset.sum_pair (BA i 0), cost_hubB,
        cost_other _ (AA hi) (AB i 0)]
      exact add_le_add (pow_le_pow_left₀ (by positivity) U1r k)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) U2r d) hβ0)
  · -- heavy player and player i share the hub b₀
    have hs0 : (s 0).val = Finset.univ.image (Fin.natAdd (n + 1)) := by
      rcases strat0 _ (s 0).2 with h0 | h0
      · exact (B_notin_imA 0 (h0 ▸ hheavy)).elim
      · exact h0
    have hsi : (s i).val = {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) i} := by
      rcases strati hi _ (s i).2 with h1 | h1
      · exact (notmem_pair (BA 0 0) (BB h0i) (h1 ▸ hshare)).elim
      · exact h1
    refine ⟨?_, ?_⟩
    · have L1 := load_ge_two s _ i hi hheavy hshare
      have L2 := load_ge_one s (Fin.castAdd (n + 1) i) i (by rw [hsi]; simp)
      rw [demandi hi] at L2
      have L1r : 1 + (w : ℝ) ≤ (load (gadget d n k w hw β) s (Fin.natAdd (n + 1) 0) : ℝ) := by
        exact_mod_cast L1
      have L2r : (w : ℝ) ≤ (load (gadget d n k w hw β) s (Fin.castAdd (n + 1) i) : ℝ) := by
        exact_mod_cast L2
      unfold playerCost
      rw [hsi, Finset.sum_pair (BA i 0), cost_hubB,
        cost_other _ (AA hi) (AB i 0)]
      exact add_le_add (pow_le_pow_left₀ (by positivity) L1r k)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) L2r d) hβ0)
    · intro t ht
      have htv : t.val = {Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) i} := by
        rcases strati hi _ t.2 with h1 | h1
        · exact h1
        · exact absurd (Subtype.ext (h1.trans hsi.symm)) ht
      have hs'0 : (Function.update s i t 0).val = (s 0).val := by
        rw [Function.update_of_ne h0i]
      have U1 := load_le_hub (Function.update s i t) (Fin.castAdd (n + 1) 0)
        (by rw [hs'0, hs0]; exact A_notin_imB 0)
      have U2 := load_le_priv (Function.update s i t) (Fin.natAdd (n + 1) i) i hi
        (fun j hj0 hji => by
          rw [Function.update_of_ne hji]
          rcases strati hj0 _ (s j).2 with h1 | h1
          · rw [h1]; exact notmem_pair (BA 0 i) (BB (Ne.symm hji))
          · rw [h1]; exact notmem_pair (BB hi) (BA j i))
      have U1r : (load (gadget d n k w hw β) (Function.update s i t) (Fin.castAdd (n + 1) 0) : ℝ)
          ≤ (n : ℝ) * (w : ℝ) := by exact_mod_cast U1
      have U2r : (load (gadget d n k w hw β) (Function.update s i t) (Fin.natAdd (n + 1) i) : ℝ)
          ≤ 1 + (w : ℝ) := by exact_mod_cast U2
      unfold playerCost
      rw [Function.update_self, htv, Finset.sum_pair (AB 0 i), cost_hubA,
        cost_other _ (BA 0 i) (BB hi)]
      exact add_le_add (pow_le_pow_left₀ (by positivity) U1r k)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) U2r d) hβ0)
