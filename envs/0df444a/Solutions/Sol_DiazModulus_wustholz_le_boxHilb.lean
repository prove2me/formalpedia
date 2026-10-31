-- Prove2me | solution 1 for DiazModulus.wustholz_le_boxHilb
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:01:14.712271+00:00
-- url     : https://prove2.me/submissions/ab1325d8-bd72-4fcb-ae71-4ba638fc66ef

import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_derivation_pow_mul_mem
import Theorems.Thm_DiazModulus_card_multiIndex
import Theorems.Thm_DiazModulus_card_le_boxHilb_of_linearIndependent
import Theorems.Thm_DiazModulus_exists_boxHilb_family
import Theorems.Thm_DiazModulus_restrictSupport_block_filtration

open Complex ComplexConjugate

/-! # Wüstholz's inequality (8.20) at finite level
Take a family `e_1, …, e_h` in the box `T`, independent modulo `J`, with `h = h_J(T)` (F4), and
the multi-indices `α : Fin n → {0, …, S₀}` with `|α| ≤ S₀`, of which there are `C(S₀ + n, n)`
(W4). The products `e_i·Q^α` lie in the box `T + S₀·C_Q` (the box filtration T1, `Q_j` in the
box `C_Q`). They are independent modulo `A`: given a relation `Σ g_{i,α} e_i Q^α ∈ A`, show
`g_{i,β} = 0` by strong induction on `|β|`. Apply `D^β = D_{w_{k_1}}⋯D_{w_{k_r}}` along a list
`ks` with counts `β` (length `|β| ≤ S₀`, entries `w_k ∈ W`): since `A ⊆ vanishOrd J W S₀` the
image lies in `J`. Lemma 8.16 (W3) turns `D^β(e_iQ^α)` into `[α = β]·β!·e_i` modulo `J` when
`|α| ≥ |β|`, and the terms with `|α| < |β|` have `g = 0` by induction. So
`Σ_i g_{i,β}·β!·e_i ∈ J`, and independence modulo `J` with `β! ≠ 0` in `ℂ` gives `g_{i,β} = 0`.
F3 then bounds the number `C(S₀ + n, n)·h_J(T)` of products by `h_A(T + S₀·C_Q)`. -/

namespace C13_W5
open DiazModulus MvPolynomial Finset

variable {A₀ A₁ : Type*}

theorem box_mono {T T' : A₀ ⊕ A₁ → ℕ} (h : ∀ b, T b ≤ T' b) :
    torusBox ℂ A₀ A₁ T ≤ torusBox ℂ A₀ A₁ T' := by
  unfold torusBox blockBox
  apply MvPolynomial.restrictSupport_mono
  intro m hm
  simp only [Set.mem_ofPred_eq] at hm ⊢
  exact fun b => (hm b).trans (h b)

theorem one_mem_box : (1 : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) ∈ torusBox ℂ A₀ A₁ 0 := by
  unfold torusBox blockBox
  rw [MvPolynomial.restrictSupport_eq_span]
  exact Submodule.subset_span ⟨0, by simp, by simp⟩

theorem prod_pow_mem [Finite A₀] [Finite A₁] {n : ℕ} (Q : Fin n → MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)
    (CQ : A₀ ⊕ A₁ → ℕ) (hQ : ∀ j, Q j ∈ torusBox ℂ A₀ A₁ CQ) (α : Fin n → ℕ) (s : Finset (Fin n)) :
    ∏ j ∈ s, Q j ^ α j ∈ torusBox ℂ A₀ A₁ (fun b => (∑ j ∈ s, α j) * CQ b) := by
  classical
  have hmul := (restrictSupport_block_filtration (K := ℂ) (σ := A₀ ⊕ (A₁ × Bool))
    (Sum.map id Prod.fst)).1
  have hpow : ∀ (j : Fin n) (k : ℕ), Q j ^ k ∈ torusBox ℂ A₀ A₁ (fun b => k * CQ b) := by
    intro j k
    induction k with
    | zero =>
      rw [pow_zero]
      exact box_mono (T := 0) (fun b => by simp) one_mem_box
    | succ k ih =>
      rw [pow_succ]
      exact box_mono (fun b => le_of_eq (by simp only [Pi.add_apply]; ring))
        (hmul _ _ _ _ ih (hQ j))
  induction s using Finset.induction_on with
  | empty =>
      rw [prod_empty]
      exact box_mono (T := 0) (fun b => by simp) one_mem_box
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact box_mono (fun b => le_of_eq (by simp only [Pi.add_apply, sum_insert ha]; ring))
      (hmul _ _ _ _ (hpow a (α a)) ih)

theorem mk_smul (I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (c : ℂ)
    (y : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :
    Ideal.Quotient.mk I (c • y) = c • Ideal.Quotient.mk I y :=
  map_smul (Ideal.Quotient.mkₐ ℂ I) c y

/-- A list with prescribed counts `β`. -/
theorem exists_list {n : ℕ} (β : Fin n → ℕ) :
    ∃ ks : List (Fin n), (fun i => ks.count i) = β ∧ ks.length = ∑ i, β i := by
  classical
  refine ⟨(∑ i, β i • ({i} : Multiset (Fin n))).toList, ?_, ?_⟩
  · funext i
    rw [← Multiset.coe_count, Multiset.coe_toList]
    simp [Multiset.count_sum', Multiset.count_singleton]
  · rw [Multiset.length_toList]
    simp [Multiset.card_sum]

end C13_W5

open DiazModulus C13_W5 in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (J A : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (S₀ n : ℕ) (hA : (A : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ⊆ vanishOrd J W S₀)
    (w : Fin n → (A₀ → ℂ) × (A₁ → ℂ)) (hw : ∀ i, w i ∈ W) (Q : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (CQ : A₀ ⊕ A₁ → ℕ)
    (hQbox : ∀ j, Q j ∈ torusBox ℂ A₀ A₁ CQ) (hQ : ∀ j, Q j ∈ J)
    (hwQ : ∀ i j, torusDeriv (w i) (Q j) - (if i = j then 1 else 0) ∈ J) (T : A₀ ⊕ A₁ → ℕ) :
    (S₀ + n).choose n * boxHilb (torusBox ℂ A₀ A₁) J T ≤ boxHilb (torusBox ℂ A₀ A₁) A (T + S₀ • CQ) := by
  classical
  obtain ⟨hmul, hfin, -⟩ := DiazModulus.restrictSupport_block_filtration (K := ℂ)
    (σ := A₀ ⊕ (A₁ × Bool)) (Sum.map id Prod.fst)
  have hFfin : ∀ T', FiniteDimensional ℂ ↥(torusBox ℂ A₀ A₁ T') := hfin
  obtain ⟨e, he, hli, -⟩ := DiazModulus.exists_boxHilb_family (torusBox ℂ A₀ A₁) hFfin J T
  let Λ := {α : Fin n → Fin (S₀ + 1) // ∑ i, (α i : ℕ) ≤ S₀}
  have hΛ : Fintype.card Λ = (S₀ + n).choose n := by
    rw [Fintype.card_subtype]
    exact DiazModulus.card_multiIndex n S₀
  let f : Fin (boxHilb (torusBox ℂ A₀ A₁) J T) × Λ → MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ :=
    fun p => e p.1 * ∏ j, Q j ^ (p.2.1 j : ℕ)
  have hf : ∀ p, f p ∈ torusBox ℂ A₀ A₁ (T + S₀ • CQ) := by
    intro p
    have hQα : ∏ j, Q j ^ (p.2.1 j : ℕ) ∈ torusBox ℂ A₀ A₁ (S₀ • CQ) := box_mono (fun b => by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact Nat.mul_le_mul_right _ p.2.2)
      (prod_pow_mem Q CQ hQbox (fun j => (p.2.1 j : ℕ)) Finset.univ)
    exact hmul _ _ _ _ (he p.1) hQα
  -- the derivative along a list of indices
  let Dk : List (Fin n) → Module.End ℂ (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :=
    fun ks => (ks.map fun i => (torusDeriv (w i)).toLinearMap).prod
  have hDk : ∀ ks, Dk ks = torusDerivList (ks.map w) := by
    intro ks
    simp only [Dk, torusDerivList, List.map_map, Function.comp_def]
  have hlin : LinearIndependent ℂ (fun p => Ideal.Quotient.mk A (f p)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set x := ∑ p, g p • f p with hx
    have hxA : x ∈ A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hx, map_sum, ← hg]
      exact Finset.sum_congr rfl (fun p _ => mk_smul A (g p) (f p))
    have key : ∀ m, ∀ p : Fin (boxHilb (torusBox ℂ A₀ A₁) J T) × Λ, ∑ i, (p.2.1 i : ℕ) = m → g p = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ihm =>
      intro p hp
      obtain ⟨i₀, β₀⟩ := p
      change ∑ i, (β₀.1 i : ℕ) = m at hp
      let β : Fin n → ℕ := fun i => (β₀.1 i : ℕ)
      obtain ⟨ks, hcount, hlen⟩ := exists_list β
      have hlenm : ks.length = m := by rw [hlen]; exact hp
      have hJ : Dk ks x ∈ J := by
        rw [hDk]
        refine hA hxA (ks.map w) (by rw [List.length_map, hlenm, ← hp]; exact β₀.2) ?_
        intro v hv
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
        exact hw k
      let N : ℂ := ((∏ i, (β i).factorial : ℕ) : ℂ)
      have hterm : ∀ p : Fin (boxHilb (torusBox ℂ A₀ A₁) J T) × Λ, g p • Ideal.Quotient.mk J (Dk ks (f p)) =
          if p.2 = β₀ then (g p * N) • Ideal.Quotient.mk J (e p.1) else 0 := by
        intro p
        by_cases hsm : ∑ i, (p.2.1 i : ℕ) < m
        · rw [ihm _ hsm p rfl, zero_smul]
          split_ifs with hpe
          · rw [hpe] at hsm
            exact absurd hp (by omega)
          · rfl
        · have hks : ks.length ≤ ∑ i, (p.2.1 i : ℕ) := by omega
          have hW := DiazModulus.derivation_pow_mul_mem (fun i => torusDeriv (w i)) J Q hQ hwQ
            (e p.1) (fun i => (p.2.1 i : ℕ)) ks hks
          have hmk : Ideal.Quotient.mk J (Dk ks (f p)) = Ideal.Quotient.mk J
              (if (fun i => ks.count i) = (fun i => (p.2.1 i : ℕ)) then
                ((∏ i, ((p.2.1 i : ℕ)).factorial : ℕ) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) * e p.1
              else 0) := Ideal.Quotient.eq.mpr hW
          rw [hmk]
          by_cases hpe : p.2 = β₀
          · have hc : (fun i => ks.count i) = (fun i => (p.2.1 i : ℕ)) := by
              rw [hcount, hpe]
            rw [if_pos hc, if_pos hpe, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, mk_smul,
              smul_smul]
            simp only [N, β, hpe]
          · have hc : ¬(fun i => ks.count i) = (fun i => (p.2.1 i : ℕ)) := by
              intro hc
              apply hpe
              apply Subtype.ext
              funext i
              exact Fin.ext ((congrFun hc i).symm.trans (congrFun hcount i))
            rw [if_neg hc, if_neg hpe, map_zero, smul_zero]
      have hsum : ∑ i, (g (i, β₀) * N) • Ideal.Quotient.mk J (e i) = 0 := by
        have h0 : Ideal.Quotient.mk J (Dk ks x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hJ
        have h0' : ∑ p, g p • Ideal.Quotient.mk J (Dk ks (f p)) = 0 := by
          rw [← h0, hx, map_sum, map_sum]
          exact Finset.sum_congr rfl (fun p _ => by rw [LinearMap.map_smul, mk_smul])
        rw [Finset.sum_congr rfl (fun p _ => hterm p), Fintype.sum_prod_type] at h0'
        have hin : ∀ i : Fin (boxHilb (torusBox ℂ A₀ A₁) J T), (∑ b : Λ, if b = β₀ then (g (i, b) * N) • Ideal.Quotient.mk J (e i)
            else 0) = (g (i, β₀) * N) • Ideal.Quotient.mk J (e i) := by
          intro i
          rw [Finset.sum_eq_single β₀ (fun b _ hb => if_neg hb)
            (fun hn => absurd (Finset.mem_univ _) hn), if_pos rfl]
        rw [Finset.sum_congr rfl (fun i _ => hin i)] at h0'
        exact h0'
      have hg0 := Fintype.linearIndependent_iff.mp hli (fun i => g (i, β₀) * N) hsum i₀
      have hN : N ≠ 0 := by
        simp only [N, ne_eq, Nat.cast_eq_zero]
        exact (Finset.prod_pos (fun i _ => Nat.factorial_pos _)).ne'
      exact (mul_eq_zero.mp hg0).resolve_right hN
    exact fun p => key _ p rfl
  have := DiazModulus.card_le_boxHilb_of_linearIndependent (torusBox ℂ A₀ A₁) hFfin A
    (T + S₀ • CQ) f hf hlin
  rw [Fintype.card_prod, Fintype.card_fin, hΛ, mul_comm] at this
  exact this
