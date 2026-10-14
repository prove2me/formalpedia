-- Prove2me | solution 1 for FixpNash.DivFree.fixedPoint_iff_isMixedNash
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:47:07.828561+00:00
-- url     : https://prove2.me/submissions/40842289-6f65-43ed-9864-8c6c3a7ae5ef

import Mathlib
import Definitions.Def_FixpNash_DivFree_Map

open scoped BigOperators
open FixpNash.DivFree DGPNash.NashMap AGT

private lemma nf_strict {α : Type*} [Fintype α] (z : α → ℝ) (a b : ℝ) (hab : a < b)
    (hb : 0 < ∑ j, max (z j-b) 0) : (∑ j, max (z j-b) 0) < ∑ j, max (z j-a) 0 := by
  classical
  have hj : ∃ j, b < z j := by
    by_contra! hn
    have he : (∑ j, max (z j-b) 0) = 0 := Finset.sum_eq_zero fun j _ => max_eq_right (sub_nonpos.mpr (hn j))
    linarith
  obtain ⟨j, hj⟩ := hj
  apply Finset.sum_lt_sum (fun k _ => max_le_max (by linarith) le_rfl)
  refine ⟨j, Finset.mem_univ j, ?_⟩
  rw [max_eq_left (by linarith : 0 ≤ z j-b), max_eq_left (by linarith : 0 ≤ z j-a)]
  linarith

private lemma nf_root {α : Type*} [Fintype α] [Nonempty α] (z : α → ℝ) :
    (∑ j, max (z j - sInf {t : ℝ | (∑ j, max (z j-t) 0) ≤ 1}) 0) = 1 ∧
      ∀ t, (∑ j, max (z j-t) 0) = 1 → t = sInf {t : ℝ | (∑ j, max (z j-t) 0) ≤ 1} := by
  classical
  let j : α := Classical.choice inferInstance
  let b := Finset.univ.sup' Finset.univ_nonempty z
  have hz (k : α) : z k ≤ b := Finset.le_sup' z (Finset.mem_univ k)
  have hcont : Continuous (fun t : ℝ => ∑ k, max (z k-t) 0) := by fun_prop
  have hlo : 1 ≤ ∑ k, max (z k-(z j-1)) 0 := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => le_max_right (z k-(z j-1)) 0) (Finset.mem_univ j)
    have he : max (z j-(z j-1)) 0 = 1 := by rw [show z j-(z j-1)=1 by ring]; norm_num
    rwa [he] at h
  have hhi : (∑ k, max (z k-b) 0) = 0 := Finset.sum_eq_zero fun k _ => max_eq_right (sub_nonpos.mpr (hz k))
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (by linarith [hz j] : z j-1 ≤ b) hcont.continuousOn ⟨by linarith, hlo⟩
  have he : sInf {a : ℝ | (∑ k, max (z k-a) 0) ≤ 1} = t := by
    apply IsLeast.csInf_eq
    refine ⟨ht.le, ?_⟩
    intro a ha
    change (∑ k, max (z k-a) 0) ≤ 1 at ha
    by_contra! hn
    have hh := nf_strict z a t hn (by linarith)
    linarith
  rw [he]
  refine ⟨ht, ?_⟩
  intro a ha
  rcases lt_trichotomy a t with hl | he | hr
  · have h := nf_strict z a t hl (by linarith); linarith
  · exact he
  · have h := nf_strict z t a hr (by linarith); linarith

private lemma nf_prof {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (x : ∀ i, S i → ℝ) (i : ι) (w : S i → ℝ)
    (s : ∀ i, S i) : profileProb (Function.update x i w) s =
      w (s i) * ∏ k ∈ Finset.univ.erase i, x k (s k) := by
  classical
  unfold profileProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

private lemma nf_mix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (w : S i → ℝ) :
    expectedPayoff u (Function.update x i w) i = ∑ j, w j * purePayoff u x i j := by
  classical
  unfold purePayoff expectedPayoff
  simp_rw [nf_prof, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp [mul_ite, ite_mul, mul_assoc]

private lemma nf_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) :
    expectedPayoff u x i = ∑ j, x i j * purePayoff u x i j := by
  simpa only [Function.update_eq_self] using nf_mix u x i (x i)

private lemma nf_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) :
    IsMixedNash u x ↔ IsMixedProfile x ∧ ∀ i j, purePayoff u x i j ≤ expectedPayoff u x i := by
  classical
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i j => h i (fun k => if k=j then 1 else 0) ?_⟩
    constructor
    · intro k; dsimp; split_ifs <;> norm_num
    · simp
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro i w hw
    rw [nf_mix]
    calc
      (∑ j, w j * purePayoff u x i j) ≤ ∑ j, w j * expectedPayoff u x i :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h i j) (hw.1 j))
      _ = expectedPayoff u x i := by rw [← Finset.sum_mul, hw.2, one_mul]

private lemma nf_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hNE : IsMixedNash u x) :
    ∀ i j, 0 < x i j → purePayoff u x i j = expectedPayoff u x i := by
  classical
  have h := (nf_pure u x).mp hNE
  intro i j hj
  have hz : ∑ k, x i k * (expectedPayoff u x i - purePayoff u x i k) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (h.1 i).2, one_mul, ← nf_self]
    ring
  have hp (k : S i) : 0 ≤ x i k * (expectedPayoff u x i-purePayoff u x i k) :=
    mul_nonneg ((h.1 i).1 k) (sub_nonneg.mpr (h.2 i k))
  have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hp k) (Finset.mem_univ j)
  rw [hz] at hh
  nlinarith [h.2 i j]

private lemma nf_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hNE : IsMixedNash u x) :
    ∀ i j, max (hVal u x i j - expectedPayoff u x i) 0 = x i j := by
  intro i j
  unfold hVal
  by_cases hj : 0 < x i j
  · rw [nf_support u x hNE i j hj]
    simp only [add_sub_cancel_right, max_eq_left hj.le]
  · have hz : x i j = 0 := le_antisymm (le_of_not_gt hj) ((hNE.1 i).1 j)
    rw [hz, zero_add]
    exact max_eq_right (sub_nonpos.mpr (((nf_pure u x).mp hNE).2 i j))

private lemma nf_at_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hS : ∀ i, Nonempty (S i))
    (x : ∀ i, S i → ℝ) (hNE : IsMixedNash u x) (i : ι) :
    threshold u x i = expectedPayoff u x i := by
  letI := hS i
  apply ((nf_root (hVal u x i)).2 _ ?_).symm
  simp_rw [nf_equilibrium u x hNE]
  exact (hNE.1 i).2

private lemma nf_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hfix : G u x = x) :
    ∀ i j, (0 < x i j → purePayoff u x i j = threshold u x i) ∧
      (x i j = 0 → purePayoff u x i j ≤ threshold u x i) := by
  intro i j
  have he : max (x i j + purePayoff u x i j - threshold u x i) 0 = x i j :=
    congrArg (fun y => y i j) hfix
  have hl := le_max_left (x i j + purePayoff u x i j - threshold u x i) 0
  constructor
  · intro hx
    by_cases hn : 0 ≤ x i j + purePayoff u x i j - threshold u x i
    · rw [max_eq_left hn] at he; linarith
    · rw [max_eq_right (le_of_not_ge hn)] at he; linarith
  · intro hx
    rw [he] at hl
    linarith

private lemma nf_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hS : ∀ i, Nonempty (S i))
    (x : ∀ i, S i → ℝ) (hx : IsMixedProfile x) : G u x = x ↔ IsMixedNash u x := by
  constructor
  · intro hfix
    have h := nf_fixed u x hfix
    have he (i : ι) : expectedPayoff u x i = threshold u x i := by
      rw [nf_self]
      calc
        (∑ j, x i j * purePayoff u x i j) = ∑ j, x i j * threshold u x i := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hp : 0 < x i j
          · rw [(h i j).1 hp]
          · have hz : x i j = 0 := le_antisymm (le_of_not_gt hp) ((hx i).1 j)
            rw [hz, zero_mul, zero_mul]
        _ = threshold u x i := by rw [← Finset.sum_mul, (hx i).2, one_mul]
    apply (nf_pure u x).mpr
    refine ⟨hx, ?_⟩
    intro i j
    rw [he]
    by_cases hp : 0 < x i j
    · exact ((h i j).1 hp).le
    · exact (h i j).2 (le_antisymm (le_of_not_gt hp) ((hx i).1 j))
  · intro hNE
    funext i j
    unfold G
    rw [nf_at_equilibrium u hS x hNE i]
    exact nf_equilibrium u x hNE i j

private lemma nf_prefix (n : ℕ) (z : Fin (n+1) → ℝ) (hz : Antitone z) (t : ℝ)
    (ht : (∑ k, max (z k-t) 0) = 1) :
    t = Finset.univ.sup' Finset.univ_nonempty (fun l : Fin (n+1) =>
      ((∑ k ∈ Finset.Iic l, z k)-1) / ((l : ℕ)+1 : ℝ)) := by
  classical
  let A := Finset.univ.filter (fun k => t < z k)
  have hA : A.Nonempty := by
    by_contra hn
    have hh (k : Fin (n+1)) : z k ≤ t := by
      by_contra! hp
      exact hn ⟨k, by simp [A, hp]⟩
    have he : (∑ k, max (z k-t) 0) = 0 := Finset.sum_eq_zero fun k _ => max_eq_right (sub_nonpos.mpr (hh k))
    linarith
  let l := A.max' hA
  have hl : t < z l := (Finset.mem_filter.mp (A.max'_mem hA)).2
  have he : A = Finset.Iic l := by
    ext k
    constructor
    · intro hk
      exact Finset.mem_Iic.mpr (Finset.le_max' A k hk)
    · intro hk
      have hk' : k ≤ l := Finset.mem_Iic.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hl.trans_le (hz hk')⟩
  have ha : (∑ k ∈ A, (z k-t)) = 1 := by
    calc
      (∑ k ∈ A, (z k-t)) = ∑ k, max (z k-t) 0 := by
        dsimp [A]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : t < z k
        · simp [h, max_eq_left (sub_nonneg.mpr h.le)]
        · simp [h, max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]
      _ = 1 := ht
  rw [he] at ha
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Fin.card_Iic,
    Nat.cast_add, Nat.cast_one] at ha
  have heq : ((∑ k ∈ Finset.Iic l, z k)-1) / ((l : ℕ)+1 : ℝ) = t := by
    apply (div_eq_iff (by positivity : ((l : ℕ)+1 : ℝ) ≠ 0)).mpr
    nlinarith
  apply le_antisymm
  · rw [← heq]
    exact Finset.le_sup' (fun q : Fin (n+1) => ((∑ k ∈ Finset.Iic q, z k)-1) / ((q : ℕ)+1 : ℝ)) (Finset.mem_univ l)
  · apply Finset.sup'_le _ _
    intro q hq
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℕ)+1)).mpr
    have hb : (∑ k ∈ Finset.Iic q, (z k-t)) ≤ 1 := by
      calc
        (∑ k ∈ Finset.Iic q, (z k-t)) ≤ ∑ k ∈ Finset.Iic q, max (z k-t) 0 :=
          Finset.sum_le_sum (fun k _ => le_max_left _ _)
        _ ≤ ∑ k, max (z k-t) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => le_max_right _ _)
        _ = 1 := ht
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Fin.card_Iic,
      Nat.cast_add, Nat.cast_one] at hb
    nlinarith


 theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (hS : ∀ i, Nonempty (S i)) (x : ∀ i, S i → ℝ)
    (hx : AGT.IsMixedProfile x) :
    G u x = x ↔ AGT.IsMixedNash u x := by
  exact nf_iff u hS x hx
#print axioms solution
