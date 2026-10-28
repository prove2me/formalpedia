-- Prove2me | solution 1 for ConservativeAD.AutoDiff.M_eq_prod_J
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:00:26.705853+00:00
-- url     : https://prove2.me/submissions/aea7f65d-df2b-470f-8a03-50fb9a4745ae

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_Program
import Definitions.Def_ConservativeAD_AutoDiff_ProofMatrices

namespace Aux_ConservativeAD_M_eq_prod_J
open ConservativeAD.AutoDiff ConservativeAD.AutoDiff.Program

variable {p q : ℕ} (P : Program p q)

/-- the rows-so-far matrix -/
noncomputable def Rm (d : P.Choice) (m : ℕ) : Matrix (Fin q) (Fin p) ℝ :=
  fun i j => if i.val < m then P.fwdRow d i j else 0

def Lm (m : ℕ) : List (Fin q) := (List.finRange q).filter (fun j => p ≤ j.val ∧ j.val < m)

theorem Lm_succ (m : ℕ) (hpm : p ≤ m) (hm : m < q) :
    Lm (p := p) (q := q) (m + 1) = Lm (p := p) (q := q) m ++ [⟨m, hm⟩] := by
  have hpw : (List.finRange q).Pairwise (· < ·) := (List.sortedLT_finRange q).pairwise
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact hpw.filter _
  · rw [List.pairwise_append]
    refine ⟨hpw.filter _, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    unfold Lm at ha
    have := (List.mem_filter.mp ha).2
    simp only [decide_eq_true_eq] at this
    exact Fin.lt_iff_val_lt_val.mpr this.2
  · intro a
    unfold Lm
    simp only [List.mem_append, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_singleton]
    constructor
    · intro h
      by_cases ha : a.val < m
      · exact Or.inl ⟨h.1, ha⟩
      · exact Or.inr (Fin.ext (show a.val = m by omega))
    · rintro (h | h)
      · exact ⟨h.1, by omega⟩
      · subst h; exact ⟨hpm, by simp⟩

theorem prod_append_single (d : P.Choice) (L : List (Fin q)) (k : Fin q) :
    ((L ++ [k]).reverse.map (P.Jmat d)).prod = P.Jmat d k * (L.reverse.map (P.Jmat d)).prod := by
  simp [List.reverse_append, List.map_append, List.prod_append]

theorem Jp_eq (d : P.Choice) : Jp p q = Rm P d p := by
  funext i j
  unfold Jp Rm
  by_cases hi : i.val < p
  · rw [if_pos hi, Program.fwdRow, dif_pos hi]
    by_cases hij : i.val = j.val
    · rw [if_pos hij]
      have : (⟨i.val, hi⟩ : Fin p) = j := Fin.ext hij
      rw [this]; simp
    · rw [if_neg hij]
      have : (⟨i.val, hi⟩ : Fin p) ≠ j := fun h => hij (by rw [← h])
      simp [EuclideanSpace.single_apply, Ne.symm this]
  · rw [if_neg hi, if_neg]
    intro h; have := j.isLt; omega

theorem step (d : P.Choice) (k : Fin q) (hk : p ≤ k.val) :
    P.Jmat d k * Rm P d k.val = Rm P d (k.val + 1) := by
  funext i j
  have hR : ∀ i j, Rm P d k.val i j = if i.val < k.val then P.fwdRow d i j else 0 := fun _ _ => rfl
  unfold Program.Jmat
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply]
  have hek : ∀ x : Fin q, e k x = if x = k then 1 else 0 := by
    intro x; unfold e; simp [Pi.single_apply]
  have h1 : (Matrix.vecMul (e k) (Rm P d k.val)) j = 0 := by
    simp only [Matrix.vecMul, dotProduct, hek, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ k]
    simp [hR]
  rw [h1, mul_zero, sub_zero]
  by_cases hik : i = k
  · subst hik
    rw [hek, if_pos rfl, one_mul]
    have hRk : Rm P d i.val i j = 0 := by simp [hR]
    rw [hRk, zero_add]
    have hRk1 : Rm P d (i.val + 1) i j = P.fwdRow d i j := by simp [Rm]
    rw [hRk1]
    -- the new row
    have hnp : ¬ i.val < p := by omega
    conv_rhs => rw [Program.fwdRow, dif_neg hnp]
    have hlift : ∀ l, (WithLp.ofLp (P.lift i (d i))) l =
        ∑ t, if (P.parents i).get t = l then d i t else 0 := fun l => rfl
    simp only [Matrix.vecMul, dotProduct, hlift]
    calc ∑ l, (∑ t, if (P.parents i).get t = l then d i t else 0) * Rm P d i.val l j
        = ∑ l, ∑ t, (if (P.parents i).get t = l then d i t * Rm P d i.val l j else 0) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun t _ => ?_
          split_ifs <;> simp
      _ = ∑ t, ∑ l, (if (P.parents i).get t = l then d i t * Rm P d i.val l j else 0) :=
          Finset.sum_comm
      _ = ∑ t, d i t * P.fwdRow d ((P.parents i).get t) j := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_univ, if_true]
          have hlt : (P.parents i).get t < i := P.parents_lt i _ (List.get_mem _ _)
          rw [hR, if_pos (Fin.lt_iff_val_lt_val.mp hlt)]
      _ = _ := by
          simp [WithLp.ofLp_sum, WithLp.ofLp_smul]
  · rw [hek, if_neg hik, zero_mul, add_zero]
    have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
    simp only [Rm]
    by_cases h : i.val < k.val
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem prod_eq (d : P.Choice) (m : ℕ) (hpm : p ≤ m) (hmq : m ≤ q) :
    ((Lm (p := p) (q := q) m).reverse.map (P.Jmat d)).prod * Jp p q = Rm P d m := by
  induction m, hpm using Nat.le_induction with
  | base =>
    have : Lm (p := p) (q := q) p = [] := by
      unfold Lm
      rw [List.filter_eq_nil_iff]
      intro a _
      simp only [decide_eq_true_eq, not_and, not_lt]
      intro h; exact h
    rw [this, List.reverse_nil, List.map_nil, List.prod_nil, Matrix.one_mul]
    exact Jp_eq P d
  | succ m hpm ih =>
    rw [Lm_succ m hpm (by omega), prod_append_single, Matrix.mul_assoc, ih (by omega)]
    exact step P d ⟨m, by omega⟩ hpm

end Aux_ConservativeAD_M_eq_prod_J

open ConservativeAD.AutoDiff ConservativeAD.AutoDiff.Program Aux_ConservativeAD_M_eq_prod_J in
theorem solution {p q : ℕ} (P : Program p q) (d : P.Choice) (k : Fin q) (hk : p ≤ k.val) :
    P.Mmat d k = P.jprod d k * Jp p q := by
  have hL : (List.finRange q).filter (fun j => p ≤ j.val ∧ j ≤ k) = Lm (p := p) (q := q) (k.val + 1) := by
    unfold Lm
    apply List.filter_congr
    intro j _
    simp only [decide_eq_decide, Fin.le_iff_val_le_val]
    omega
  unfold Program.jprod
  rw [hL, prod_eq P d (k.val + 1) (by omega) k.isLt]
  funext i j
  unfold Program.Mmat Rm
  simp only [Fin.le_iff_val_le_val]
  by_cases h : i.val ≤ k.val
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
