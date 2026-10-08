-- Prove2me | solution 1 for CoffmanMitrani1980.Region.lemma1_priority_vector_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:10:10.30172+00:00
-- url     : https://prove2.me/submissions/b807b2e9-7bbf-43ec-a402-9cd34f9f1ef2

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model

set_option autoImplicit false

open Finset

namespace CM80Aux
open CoffmanMitrani1980.Region

variable {M : ℕ} (p : Params M)

lemma rho_pos (i : Fin M) : 0 < p.rho i := div_pos (p.lam_pos i) (p.mu_pos i)

lemma a_pos (i : Fin M) : 0 < p.a i := div_pos (rho_pos p i) (p.mu_pos i)

lemma sum_rho_lt (s : Finset (Fin M)) : ∑ i ∈ s, p.rho i < 1 := by
  have h := p.load_lt_one
  exact lt_of_le_of_lt
    (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _ => (rho_pos p i).le)) h

lemma f_empty : p.f ∅ = 0 := by simp [Params.f]

lemma marg (s : Finset (Fin M)) (x : Fin M) (hx : x ∉ s) :
    p.f (insert x s) - p.f s = p.a x / (1 - ∑ i ∈ s, p.rho i - p.rho x)
      + (∑ i ∈ s, p.a i) * p.rho x /
          ((1 - ∑ i ∈ s, p.rho i) * (1 - ∑ i ∈ s, p.rho i - p.rho x)) := by
  have h1 : 0 < 1 - ∑ i ∈ insert x s, p.rho i := sub_pos.2 (sum_rho_lt p _)
  have h2 : 0 < 1 - ∑ i ∈ s, p.rho i := sub_pos.2 (sum_rho_lt p _)
  rw [sum_insert hx] at h1
  unfold Params.f
  rw [sum_insert hx, sum_insert hx]
  have h1' : 1 - ∑ i ∈ s, p.rho i - p.rho x ≠ 0 := by linarith
  have h1'' : 1 - (p.rho x + ∑ i ∈ s, p.rho i) ≠ 0 := by linarith
  have h2' : 1 - ∑ i ∈ s, p.rho i ≠ 0 := h2.ne'
  rw [div_add_div _ _ h1' (mul_ne_zero h2' h1'), div_sub_div _ _ h1'' h2', div_eq_div_iff
    (mul_ne_zero h1'' h2') (mul_ne_zero h1' (mul_ne_zero h2' h1'))]
  ring

lemma supermod (A B : Finset (Fin M)) (hBA : B ⊆ A) (x : Fin M) (hx : x ∉ A) :
    p.f (insert x B) - p.f B ≤ p.f (insert x A) - p.f A := by
  rw [marg p B x (fun h => hx (hBA h)), marg p A x hx]
  have hA1 : 0 < 1 - ∑ i ∈ insert x A, p.rho i := sub_pos.2 (sum_rho_lt p _)
  rw [sum_insert hx] at hA1
  have hRA : ∑ i ∈ B, p.rho i ≤ ∑ i ∈ A, p.rho i :=
    sum_le_sum_of_subset_of_nonneg hBA (fun i _ _ => (rho_pos p i).le)
  have haA : ∑ i ∈ B, p.a i ≤ ∑ i ∈ A, p.a i :=
    sum_le_sum_of_subset_of_nonneg hBA (fun i _ _ => (a_pos p i).le)
  have haB : 0 ≤ ∑ i ∈ B, p.a i := sum_nonneg (fun i _ => (a_pos p i).le)
  have hrx := rho_pos p x
  have hax := a_pos p x
  have hA2 : 0 < 1 - ∑ i ∈ A, p.rho i - p.rho x := by linarith
  have hA3 : 0 < 1 - ∑ i ∈ A, p.rho i := by linarith
  apply add_le_add
  · apply div_le_div_of_nonneg_left hax.le hA2
    linarith
  · apply div_le_div₀ (mul_nonneg (haB.trans haA) hrx.le)
      (mul_le_mul_of_nonneg_right haA hrx.le) (mul_pos hA3 hA2)
    apply mul_le_mul (by linarith) (by linarith) hA2.le (by linarith)

lemma mem_topSet (π : Equiv.Perm (Fin M)) (k : ℕ) (i : Fin M) :
    i ∈ topSet π k ↔ ((π.symm i : Fin M) : ℕ) < k := by
  unfold topSet
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨π.symm i, h, by simp⟩

lemma topSet_succ (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) :
    topSet π (k + 1) = insert (π ⟨k, hk⟩) (topSet π k) := by
  ext i
  simp only [mem_insert, mem_topSet]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr h
    · left
      subst h
      simp
  · rintro (rfl | h)
    · simp
    · omega

lemma notMem_topSet (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) :
    π ⟨k, hk⟩ ∉ topSet π k := by
  rw [mem_topSet]
  simp

lemma topSet_zero (π : Equiv.Perm (Fin M)) : topSet π 0 = ∅ := by
  ext i
  simp [mem_topSet]

lemma topSet_M (π : Equiv.Perm (Fin M)) : topSet π M = univ := by
  ext i
  simp [mem_topSet]

noncomputable def d (π : Equiv.Perm (Fin M)) (i : Fin M) : ℝ :=
  p.f (topSet π ((π.symm i : ℕ) + 1)) - p.f (topSet π (π.symm i : ℕ))

lemma key (π : Equiv.Perm (Fin M)) (g : Finset (Fin M)) :
    ∀ k ≤ M, p.f (g ∩ topSet π k) ≤ ∑ i ∈ g ∩ topSet π k, d p π i ∧
      ∑ i ∈ topSet π k, d p π i = p.f (topSet π k) := by
  intro k
  induction k with
  | zero => intro _; simp [topSet_zero, f_empty]
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hk' : k < M := by omega
    have hxS : π ⟨k, hk'⟩ ∉ topSet π k := notMem_topSet π k hk'
    have hdx : d p π (π ⟨k, hk'⟩) = p.f (topSet π (k + 1)) - p.f (topSet π k) := by
      simp [d]
    rw [topSet_succ π k hk'] at hdx ⊢
    constructor
    · by_cases hxg : π ⟨k, hk'⟩ ∈ g
      · rw [inter_insert_of_mem hxg, sum_insert (fun h => hxS (mem_inter.1 h).2)]
        have := supermod p (topSet π k) (g ∩ topSet π k) inter_subset_right _ hxS
        linarith
      · rw [inter_insert_of_notMem hxg]
        exact ih1
    · rw [sum_insert hxS, ih2, hdx]
      ring

end CM80Aux

open CoffmanMitrani1980.Region in
theorem solution {M : ℕ} (p : Params M) (π : Equiv.Perm (Fin M)) :
    p.prioVec π ∈ p.Hss := by
  have hW : ∀ i, p.rho i * p.prioVec π i = CM80Aux.d p π i := fun i => by
    have := (CM80Aux.rho_pos p i).ne'
    unfold Params.prioVec CM80Aux.d
    field_simp
  refine ⟨?_, ?_⟩
  · simp_rw [hW]
    have h := (CM80Aux.key p π univ M le_rfl).2
    rw [CM80Aux.topSet_M] at h
    rw [h]
    unfold Params.f Params.V
    congr 1
    apply sum_congr rfl
    intro i _
    unfold Params.a Params.rho
    rw [div_div, sq]
  · intro g _ _
    rw [sum_congr rfl (fun i _ => hW i)]
    have h := (CM80Aux.key p π g M le_rfl).1
    rw [CM80Aux.topSet_M, inter_univ] at h
    exact h
