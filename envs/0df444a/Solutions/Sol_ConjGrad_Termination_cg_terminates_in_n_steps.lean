-- Prove2me | solution 1 for ConjGrad.Termination.cg_terminates_in_n_steps
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:55:49.113302+00:00
-- url     : https://prove2.me/submissions/14f0bb37-9210-43f6-a74b-9f3cf66613e6

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

lemma aux_cgt_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (u v : Fin n → ℝ) :
    (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
  have hT : Aᵀ = A := by
    have h := hA.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  rw [dotProduct_mulVec, ← mulVec_transpose, hT]

lemma aux_cgt_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (u : Fin n → ℝ)
    (h : u ⬝ᵥ (A *ᵥ u) = 0) : u = 0 := by
  by_contra hu
  have h2 := hA.dotProduct_mulVec_pos hu
  rw [star_trivial, h] at h2
  exact lt_irrefl _ h2

lemma aux_cgt_x {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) :
    (cgStep A s).x = s.x + cgA A s • s.p := rfl

lemma aux_cgt_r {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) :
    (cgStep A s).r = s.r - cgA A s • (A *ᵥ s.p) := rfl

lemma aux_cgt_p {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) :
    (cgStep A s).p = (cgStep A s).r
      + (((cgStep A s).r ⬝ᵥ (cgStep A s).r) / (s.r ⬝ᵥ s.r)) • s.p := rfl

lemma aux_cgt_dr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) (v : Fin n → ℝ) :
    v ⬝ᵥ (cgStep A s).r = v ⬝ᵥ s.r - cgA A s * (v ⬝ᵥ (A *ᵥ s.p)) := by
  rw [aux_cgt_r, dotProduct_sub, dotProduct_smul, smul_eq_mul]

lemma aux_cgt_dp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) (v : Fin n → ℝ) :
    v ⬝ᵥ (cgStep A s).p = v ⬝ᵥ (cgStep A s).r
      + (((cgStep A s).r ⬝ᵥ (cgStep A s).r) / (s.r ⬝ᵥ s.r)) * (v ⬝ᵥ s.p) := by
  rw [aux_cgt_p, dotProduct_add, dotProduct_smul, smul_eq_mul]

lemma aux_cgt_pd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) (v : Fin n → ℝ) :
    (cgStep A s).p ⬝ᵥ v = (cgStep A s).r ⬝ᵥ v
      + (((cgStep A s).r ⬝ᵥ (cgStep A s).r) / (s.r ⬝ᵥ s.r)) * (s.p ⬝ᵥ v) := by
  rw [aux_cgt_p, add_dotProduct, smul_dotProduct, smul_eq_mul]

lemma aux_cgt_rp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → CGState n)
    (hs : ∀ i, s (i + 1) = cgStep A (s i)) (h0 : (s 0).p = (s 0).r) :
    ∀ i, (s i).r = 0 → (s i).p = 0 := by
  intro i
  cases i with
  | zero => intro h; rw [h0, h]
  | succ i =>
    intro h
    rw [hs] at h ⊢
    rw [aux_cgt_p, h]
    simp

lemma aux_cgt_rr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → CGState n)
    (hs : ∀ i, s (i + 1) = cgStep A (s i)) (h0 : (s 0).p = (s 0).r) (v : Fin n → ℝ)
    (m : ℕ) (hv : ∀ j < m, v ⬝ᵥ (s j).p = 0) :
    ∀ j < m, v ⬝ᵥ (s j).r = 0 := by
  intro j hj
  cases j with
  | zero => rw [← h0]; exact hv 0 hj
  | succ j =>
    have h1 := hv (j + 1) hj
    have h2 := hv j (by omega)
    rw [hs, aux_cgt_dp, h2, mul_zero, add_zero] at h1
    rw [hs]
    exact h1

lemma aux_cgt_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (s : ℕ → CGState n)
    (hs : ∀ i, s (i + 1) = cgStep A (s i)) (h0 : (s 0).p = (s 0).r) :
    ∀ i, (∀ j < i, (s i).r ⬝ᵥ (s j).p = 0) ∧
      (s i).r ⬝ᵥ (s i).p = (s i).r ⬝ᵥ (s i).r ∧
      (∀ j < i, (s i).p ⬝ᵥ (A *ᵥ (s j).p) = 0) := by
  have rp := aux_cgt_rp A s hs h0
  intro i
  induction i with
  | zero =>
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [h0],
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i ih =>
    obtain ⟨ihc, ihd, ihb⟩ := ih
    rw [hs i]
    have hc : ∀ j < i + 1, (cgStep A (s i)).r ⬝ᵥ (s j).p = 0 := by
      intro j hj
      rw [dotProduct_comm, aux_cgt_dr]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · have e1 : (s j).p ⬝ᵥ (s i).r = 0 := by rw [dotProduct_comm]; exact ihc j hj
        have e2 : (s j).p ⬝ᵥ (A *ᵥ (s i).p) = 0 := by
          rw [← aux_cgt_symm hA, dotProduct_comm]; exact ihb j hj
        rw [e1, e2]; ring
      · subst hj
        by_cases hP : (s j).p ⬝ᵥ (A *ᵥ (s j).p) = 0
        · have hp := aux_cgt_pos hA _ hP
          rw [hp]; simp
        · rw [dotProduct_comm, ihd, cgA, div_mul_cancel₀ _ hP, sub_self]
    have ha := aux_cgt_rr A s hs h0 _ (i + 1) hc
    refine ⟨hc, ?_, ?_⟩
    · rw [aux_cgt_dp, hc i (Nat.lt_succ_self i), mul_zero, add_zero]
    · intro j hj
      rw [aux_cgt_pd]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [ihb j hj, mul_zero, add_zero]
        have e := aux_cgt_dr A (s j) (cgStep A (s i)).r
        rw [← hs j, ha (j + 1) (by omega), ha j (by omega)] at e
        have hm : cgA A (s j) * ((cgStep A (s i)).r ⬝ᵥ (A *ᵥ (s j).p)) = 0 := by linarith
        rcases mul_eq_zero.mp hm with h1 | h1
        · rw [cgA] at h1
          rcases div_eq_zero_iff.mp h1 with h2 | h2
          · have hp := rp j (dotProduct_self_eq_zero.mp h2)
            rw [hp]; simp
          · have hp := aux_cgt_pos hA _ h2
            rw [hp]; simp
        · exact h1
      · subst hj
        by_cases hP : (s j).p ⬝ᵥ (A *ᵥ (s j).p) = 0
        · have hp := aux_cgt_pos hA _ hP
          simp [hp]
        · have hR : (s j).r ⬝ᵥ (s j).r ≠ 0 := by
            intro h
            apply hP
            rw [rp j (dotProduct_self_eq_zero.mp h)]
            simp
          have e := aux_cgt_dr A (s j) (cgStep A (s j)).r
          rw [ha j (Nat.lt_succ_self j)] at e
          rw [e, cgA]
          field_simp
          ring

lemma aux_cgt_res {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) :
    ∀ i, (cgIter A k x₀ i).r = k - A *ᵥ (cgIter A k x₀ i).x := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    show (cgStep A (cgIter A k x₀ i)).r = k - A *ᵥ (cgStep A (cgIter A k x₀ i)).x
    rw [aux_cgt_r, aux_cgt_x, ih, mulVec_add, mulVec_smul]
    abel

end ConjGrad.Termination

open ConjGrad.Termination
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x₀ : Fin n → ℝ) :
    ∃ m ≤ n, (cgIter A k x₀ m).x = h := by
  have hs : ∀ i, cgIter A k x₀ (i + 1) = cgStep A (cgIter A k x₀ i) := fun i => rfl
  have h0 : (cgIter A k x₀ 0).p = (cgIter A k x₀ 0).r := rfl
  have horth : ∀ i, ∀ j < i, (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ j).r = 0 := fun i =>
    aux_cgt_rr A (cgIter A k x₀) hs h0 _ i (aux_cgt_inv hA (cgIter A k x₀) hs h0 i).1
  have hex : ∃ m ≤ n, (cgIter A k x₀ m).r = 0 := by
    by_contra hne
    push Not at hne
    let f : Fin (n + 1) → (Fin n → ℝ) := fun m => (cgIter A k x₀ (m : ℕ)).r
    have hli : LinearIndependent ℝ f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hd := congrArg (fun v => f i ⬝ᵥ v) hg
      simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero] at hd
      rw [Finset.sum_eq_single i] at hd
      · have hi : f i ⬝ᵥ f i ≠ 0 := by
          intro hz
          exact hne i (Nat.lt_succ_iff.mp i.2) (dotProduct_self_eq_zero.mp hz)
        exact (mul_eq_zero.mp hd).resolve_right hi
      · intro b _ hb
        have hne' : (b : ℕ) ≠ (i : ℕ) := fun e => hb (Fin.ext e)
        rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
        · rw [horth i b hlt, mul_zero]
        · rw [dotProduct_comm, horth b i hlt, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have := hli.fintype_card_le_finrank
    simp at this
  obtain ⟨m, hm, hr⟩ := hex
  refine ⟨m, hm, ?_⟩
  have hres := aux_cgt_res A k x₀ m
  rw [hr] at hres
  apply mulVec_injective_of_isUnit hA.isUnit
  rw [hh]
  exact (sub_eq_zero.mp hres.symm).symm
