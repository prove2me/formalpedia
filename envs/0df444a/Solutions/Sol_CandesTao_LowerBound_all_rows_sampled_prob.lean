-- Prove2me | solution 1 for CandesTao.LowerBound.all_rows_sampled_prob
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:59:03.856174+00:00
-- url     : https://prove2.me/submissions/62107ee6-4ef8-4cc9-8685-fc0940657806

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

namespace CandesTao.LowerBound

open scoped BigOperators

/-- Probability that a Bernoulli set avoids a fixed set `T`. -/
theorem aux_arsp_avoid {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) (T : Finset α) :
    ∑ Ω : Finset α,
        (if Disjoint T Ω then p ^ Ω.card * (1 - p) ^ (Fintype.card α - Ω.card) else 0)
      = (1 - p) ^ T.card := by
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun Ω : Finset α => Disjoint T Ω) = (Tᶜ).powerset := by
    ext Ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    constructor
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxT
      exact Finset.disjoint_left.mp h hxT hx
    · intro h
      rw [Finset.disjoint_left]
      intro x hxT hxΩ
      have := h hxΩ
      rw [Finset.mem_compl] at this
      exact this hxT
  rw [hfil]
  have h2 : T.card + (Tᶜ).card = Fintype.card α := Finset.card_add_card_compl T
  calc ∑ Ω ∈ (Tᶜ).powerset, p ^ Ω.card * (1 - p) ^ (Fintype.card α - Ω.card)
      = ∑ Ω ∈ (Tᶜ).powerset,
          (1 - p) ^ T.card * (p ^ Ω.card * (1 - p) ^ ((Tᶜ).card - Ω.card)) := by
        apply Finset.sum_congr rfl
        intro Ω hΩ
        have h1 : Ω.card ≤ (Tᶜ).card := Finset.card_le_card (Finset.mem_powerset.mp hΩ)
        have : Fintype.card α - Ω.card = T.card + ((Tᶜ).card - Ω.card) := by omega
        rw [this, pow_add]
        ring
    _ = (1 - p) ^ T.card * (p + (1 - p)) ^ (Tᶜ).card := by
        rw [← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
    _ = (1 - p) ^ T.card := by simp

/-- Inclusion–exclusion form of the indicator that every `S a` meets `Ω`. -/
theorem aux_arsp_indicator {n : ℕ} {α : Type*} [DecidableEq α]
    (S : Fin n → Finset α) (Ω : Finset α) :
    (if (∀ a, ∃ e ∈ S a, e ∈ Ω) then (1 : ℝ) else 0)
      = ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : ℝ) ^ J.card * (if Disjoint (J.biUnion S) Ω then (1 : ℝ) else 0) := by
  have key : (if (∀ a, ∃ e ∈ S a, e ∈ Ω) then (1 : ℝ) else 0)
      = ∏ a, (-(if Disjoint (S a) Ω then (1 : ℝ) else 0) + 1) := by
    by_cases h : ∀ a, ∃ e ∈ S a, e ∈ Ω
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro a _
      obtain ⟨e, he, heΩ⟩ := h a
      rw [if_neg (Finset.not_disjoint_iff.mpr ⟨e, he, heΩ⟩)]
      ring
    · rw [if_neg h]
      symm
      push Not at h
      obtain ⟨a, ha⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      have hd : Disjoint (S a) Ω := by
        rw [Finset.disjoint_left]
        intro e he heΩ
        exact ha e he heΩ
      rw [if_pos hd]
      ring
  rw [key, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_boole]
  congr 2
  exact propext (Finset.disjoint_biUnion_left J S Ω).symm

end CandesTao.LowerBound

open CandesTao.LowerBound
open MatrixCompletion

theorem solution (n ℓ : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Fin n → Finset (Fin n × Fin n))
    (hdisj : Pairwise (fun a b => Disjoint (S a) (S b)))
    (hcard : ∀ a, (S a).card = ℓ) :
    bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => ∀ a, ∃ e ∈ S a, e ∈ Ω) =
      (1 - (1 - p) ^ ℓ) ^ n := by
  classical
  unfold bernoulliEventProb bernoulliObservationWeight
  set N := Fintype.card (Fin n × Fin n)
  have hind : ∀ Ω : Finset (Fin n × Fin n),
      (if (∀ a, ∃ e ∈ S a, e ∈ Ω) then p ^ Ω.card * (1 - p) ^ (N - Ω.card) else 0)
      = ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ J.card *
          (if Disjoint (J.biUnion S) Ω then p ^ Ω.card * (1 - p) ^ (N - Ω.card) else 0) := by
    intro Ω
    have h := aux_arsp_indicator S Ω
    have e1 : (if (∀ a, ∃ e ∈ S a, e ∈ Ω) then p ^ Ω.card * (1 - p) ^ (N - Ω.card) else 0)
        = (if (∀ a, ∃ e ∈ S a, e ∈ Ω) then (1 : ℝ) else 0) *
            (p ^ Ω.card * (1 - p) ^ (N - Ω.card)) := by
      split_ifs <;> ring
    rw [e1, h, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    split_ifs <;> ring
  refine Eq.trans (Finset.sum_congr (g := fun Ω => ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ J.card *
        (if Disjoint (J.biUnion S) Ω then p ^ Ω.card * (1 - p) ^ (N - Ω.card) else 0))
      rfl (fun Ω _ => ?_)) ?_
  · convert hind Ω
  rw [Finset.sum_comm]
  have hJ : ∀ J ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∑ Ω : Finset (Fin n × Fin n), (-1 : ℝ) ^ J.card *
          (if Disjoint (J.biUnion S) Ω then p ^ Ω.card * (1 - p) ^ (N - Ω.card) else 0)
        = (-(1 - p) ^ ℓ) ^ J.card * 1 ^ (n - J.card) := by
    intro J _
    rw [← Finset.mul_sum, aux_arsp_avoid p (J.biUnion S)]
    have hc : (J.biUnion S).card = J.card * ℓ := by
      rw [Finset.card_biUnion]
      · rw [Finset.sum_congr rfl (fun a _ => hcard a), Finset.sum_const, smul_eq_mul]
      · intro a _ b _ hab
        exact hdisj hab
    rw [hc, one_pow, mul_one, neg_pow ((1 - p) ^ ℓ), ← pow_mul, mul_comm ℓ J.card]
  rw [Finset.sum_congr rfl hJ]
  have hn : (Finset.univ : Finset (Fin n)).card = n := by simp
  have := Finset.sum_pow_mul_eq_add_pow (-(1 - p) ^ ℓ) (1 : ℝ) (Finset.univ : Finset (Fin n))
  rw [hn] at this
  rw [this]
  ring
