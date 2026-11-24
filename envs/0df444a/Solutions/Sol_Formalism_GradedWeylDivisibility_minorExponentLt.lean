-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.minorExponentLt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:59.317739+00:00
-- url     : https://prove2.me/submissions/258afe66-37be-4052-bc3a-a30e5bc7a0b0

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_MinorExpLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
open scoped MonomialOrder
private theorem cmIdx_val_eq {r n : ℕ} (v : Fin r × Fin n) :
    ((cmIdx r n v : Fin (n * r)) : ℕ) = v.1.val + r * v.2.val := by
  first
  | rfl
  | (simp only [cmIdx, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, finProdFinEquiv_apply_val]; done)
  | (simp [cmIdx, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]; done)
  | (simp [cmIdx]; ring)
private theorem col_lt_or_col_eq_row_lt_of_cmIdx_lt {r n : ℕ} {v w : Fin r × Fin n}
    (h : cmIdx r n v < cmIdx r n w) :
    v.2.val < w.2.val ∨ (v.2 = w.2 ∧ v.1 < w.1) := by
  have h0 : ((cmIdx r n v : Fin (n * r)) : ℕ) < ((cmIdx r n w : Fin (n * r)) : ℕ) := h
  rw [cmIdx_val_eq, cmIdx_val_eq] at h0
  have hv1 := v.1.isLt
  have hw1 := w.1.isLt
  rcases lt_trichotomy v.2.val w.2.val with h1 | h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨Fin.ext h1, ?_⟩
    rw [h1] at h0
    show v.1.val < w.1.val
    omega
  · exfalso
    have hm : r * (w.2.val + 1) ≤ r * v.2.val := by
      first
      | exact Nat.mul_le_mul_left r h1
      | exact Nat.mul_le_mul_left h1 r
      | exact Nat.mul_le_mul (le_refl r) h1
    rw [Nat.mul_add, Nat.mul_one] at hm
    first
    | omega
    | linarith
private theorem domCongr_cmIdx_apply_cmIdx {r n : ℕ} (x : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    (Finsupp.domCongr (cmIdx r n) x) (cmIdx r n v) = x v := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])
  | (simp; done)
private theorem sum_single_castLE_apply' {r n s : ℕ} (τ : Fin s → Fin r) (hs : s ≤ n) (b : Fin r) (t : Fin n) :
    (∑ q : Fin s, Finsupp.single (τ q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
      if h : t.val < s then (if τ ⟨t.val, h⟩ = b then 1 else 0) else 0 := by
  rw [Finsupp.finset_sum_apply]
  by_cases h : t.val < s
  · rw [dif_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · rw [Finsupp.single_apply]
      by_cases hb : τ ⟨t.val, h⟩ = b
      · have hp : (τ ⟨t.val, h⟩, Fin.castLE hs ⟨t.val, h⟩) = (b, t) := by
          first
          | exact Prod.ext hb (Fin.ext rfl)
          | exact Prod.ext_iff.2 ⟨hb, Fin.ext rfl⟩
          | (subst hb; rfl)
        rw [if_pos hp, if_pos hb]
      · rw [if_neg, if_neg hb]
        intro he
        exact hb (congrArg Prod.fst he)
    · intro q _ hq
      rw [Finsupp.single_apply, if_neg]
      intro he
      apply hq
      apply Fin.ext
      have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
      exact h2
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro q _
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply h
    have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
    have h3 := q.isLt
    have h4 : (Fin.castLE hs q).val = q.val := rfl
    omega
private theorem toLex_lt_of_eq_below_of_apply_lt {N : ℕ} (x y : Fin N →₀ ℕ) (i : Fin N)
    (h1 : ∀ j, j < i → x j = y j) (h2 : x i < y i) : toLex x < toLex y := by
  first
  | exact ⟨i, h1, h2⟩
  | exact Finsupp.Lex.lt_of_forall_lt_of_lt _ _ i h1 h2
  | (show Finsupp.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (show Pi.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (rw [Finsupp.lex_def]; exact ⟨i, h1, h2⟩)
private theorem colLex_lt_of_toLex_domCongr_cmIdx_lt {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ}
    (h : toLex (Finsupp.domCongr (cmIdx r n) c) <
      toLex (Finsupp.domCongr (cmIdx r n) d)) :
    c ≺[colLex r n] d := h
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : MinorExpLt := by
  intro r n s I hs hI σ hσ
  have hex : ∃ q, σ q ≠ q := by
    by_contra h
    push_neg at h
    apply hσ
    ext x
    first
    | (rw [h x]; rfl)
    | simp [h x]
  obtain ⟨q0, hq0, hmin⟩ := (wellFounded_lt (α := Fin s)).has_min {q | σ q ≠ q} hex
  have hq0' : σ q0 ≠ q0 := hq0
  have hfix : ∀ q, q < q0 → σ q = q := fun q hq => by
    by_contra h
    exact hmin q h hq
  have hgt : q0 < σ q0 := by
    rcases lt_trichotomy (σ q0) q0 with h | h | h
    · exact absurd (σ.injective (hfix _ h)) h.ne
    · exact absurd h hq0'
    · exact h
  have hIlt : I q0 < I (σ q0) := hI hgt
  have hA : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I (σ ⟨t.val, h⟩) = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' (fun q => I (σ q)) hs b t
  have hB : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I ⟨t.val, h⟩ = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' I hs b t
  have hcq : (Fin.castLE hs q0).val = q0.val := rfl
  have ht0 : (Fin.castLE hs q0).val < s := q0.isLt
  have e1 : (⟨(Fin.castLE hs q0).val, ht0⟩ : Fin s) = q0 := Fin.ext rfl
  apply colLex_lt_of_toLex_domCongr_cmIdx_lt
  apply toLex_lt_of_eq_below_of_apply_lt _ _ (cmIdx r n (I q0, Fin.castLE hs q0))
  · intro j hj
    obtain ⟨v, rfl⟩ := (cmIdx r n).surjective j
    rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx]
    obtain ⟨b, t⟩ := v
    rw [hA, hB]
    have hlt := col_lt_or_col_eq_row_lt_of_cmIdx_lt hj
    try dsimp only at hlt
    rcases hlt with hlt | ⟨rfl, hb⟩
    · have ht : t.val < s := by
        have := q0.isLt
        omega
      have hlt' : (⟨t.val, ht⟩ : Fin s) < q0 := by
        show t.val < q0.val
        omega
      rw [dif_pos ht, dif_pos ht, hfix _ hlt']
    · rw [dif_pos ht0, dif_pos ht0, e1, if_neg (lt_trans hb hIlt).ne', if_neg hb.ne']
  · rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx, hA, hB]
    rw [dif_pos ht0, dif_pos ht0, e1, if_neg hIlt.ne', if_pos (rfl : I q0 = I q0)]
    exact Nat.zero_lt_one
end Formalism.GradedWeylDivisibility
