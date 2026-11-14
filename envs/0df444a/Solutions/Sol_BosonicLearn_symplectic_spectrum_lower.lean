-- Prove2me | solution 1 for BosonicLearn.symplectic_spectrum_lower
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T07:00:21.079212+00:00
-- url     : https://prove2.me/submissions/4d652165-8944-4ddd-bcb9-5112cf6e139e

import Mathlib

open scoped Matrix

noncomputable section

/-- Squared Euclidean norm of a complex vector. -/
private def nsq {ι : Type} [Fintype ι] (u : ι → ℂ) : ℝ := ∑ i, ‖u i‖ ^ 2

private lemma nsq_smul {ι : Type} [Fintype ι] (z : ℂ) (u : ι → ℂ) : nsq (z • u) = ‖z‖ ^ 2 * nsq u := by
  unfold nsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

private lemma nsq_pos {ι : Type} [Fintype ι] {u : ι → ℂ} (hu : u ≠ 0) : 0 < nsq u := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  unfold nsq
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
  have : 0 < ‖u i‖ := norm_pos_iff.mpr hi
  positivity

/-- `Ω = [[0, 1], [-1, 0]]` preserves the Euclidean norm. -/
private lemma nsq_omega {n : ℕ} (w : Fin n ⊕ Fin n → ℂ) :
    nsq ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *ᵥ w) = nsq w := by
  unfold nsq
  rw [Matrix.fromBlocks_mulVec, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
    zero_add, add_zero, Pi.neg_apply, Function.comp_apply, norm_neg]
  ring

/-- A real symmetric matrix with `S ⪰ c` expands real vectors by at least `c`. -/
private lemma real_expand {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hS : (S - c • (1 : Matrix ι ι ℝ)).PosSemidef) (a : ι → ℝ) :
    c ^ 2 * (a ⬝ᵥ a) ≤ (S *ᵥ a) ⬝ᵥ (S *ᵥ a) := by
  have hp : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hr : 0 ≤ (S *ᵥ a) ⬝ᵥ (S *ᵥ a) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 := hS.dotProduct_mulVec_nonneg a
  have hstar : star a = a := by
    funext i
    simp
  rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul] at h1
  have hcs : (a ⬝ᵥ (S *ᵥ a)) ^ 2 ≤ (a ⬝ᵥ a) * ((S *ᵥ a) ⬝ᵥ (S *ᵥ a)) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (S *ᵥ a)
    simpa [dotProduct, sq] using h
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hr
  · have h2 : c * (a ⬝ᵥ a) ≤ a ⬝ᵥ (S *ᵥ a) := by linarith
    have h3 : (c * (a ⬝ᵥ a)) ^ 2 ≤ (a ⬝ᵥ (S *ᵥ a)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hc hp) h2 2
    have h4 : (a ⬝ᵥ a) * (c ^ 2 * (a ⬝ᵥ a)) ≤ (a ⬝ᵥ a) * ((S *ᵥ a) ⬝ᵥ (S *ᵥ a)) := by
      calc (a ⬝ᵥ a) * (c ^ 2 * (a ⬝ᵥ a)) = (c * (a ⬝ᵥ a)) ^ 2 := by ring
        _ ≤ (a ⬝ᵥ (S *ᵥ a)) ^ 2 := h3
        _ ≤ (a ⬝ᵥ a) * ((S *ᵥ a) ⬝ᵥ (S *ᵥ a)) := hcs
    exact le_of_mul_le_mul_left h4 hpos

/-- The complexification of such a matrix expands complex vectors by at least `c`. -/
private lemma complex_expand {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hS : (S - c • (1 : Matrix ι ι ℝ)).PosSemidef) (v : ι → ℂ) :
    c ^ 2 * nsq v ≤ nsq ((S.map (fun x : ℝ => (x : ℂ))) *ᵥ v) := by
  set a : ι → ℝ := fun j => (v j).re with ha
  set b : ι → ℝ := fun j => (v j).im with hb
  have hre : ∀ i, ((S.map (fun x : ℝ => (x : ℂ))) *ᵥ v) i = (((S *ᵥ a) i : ℝ) : ℂ) +
      (((S *ᵥ b) i : ℝ) : ℂ) * Complex.I := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ha, hb]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (v j)]
    ring
  have h1 : nsq ((S.map (fun x : ℝ => (x : ℂ))) *ᵥ v) =
      (S *ᵥ a) ⬝ᵥ (S *ᵥ a) + (S *ᵥ b) ⬝ᵥ (S *ᵥ b) := by
    unfold nsq
    simp only [dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hre i, Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have h2 : nsq v = a ⬝ᵥ a + b ⬝ᵥ b := by
    unfold nsq
    simp only [dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [h1, h2, mul_add]
  exact add_le_add (real_expand S c hc hS a) (real_expand S c hc hS b)

theorem solution {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hS : (S - c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef) :
    ∀ z ∈ spectrum ℂ ((Matrix.fromBlocks 0 1 (-1) 0 * S).map (fun x : ℝ => (x : ℂ))),
      c ≤ ‖z‖ := by
  intro z hz
  set A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (Matrix.fromBlocks 0 1 (-1) 0 * S).map (fun x : ℝ => (x : ℂ)) with hA
  have hdet : (algebraMap ℂ (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) z - A).det = 0 := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hz
    exact hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero] at hv
    exact hv.symm
  have hfac : A = (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
      S.map (fun x : ℝ => (x : ℂ)) := by
    have h := Matrix.map_mul (L := (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) (M := S) (f := Complex.ofRealHom)
    have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ).map
        (Complex.ofRealHom : ℝ → ℂ) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
      rw [Matrix.fromBlocks_map]
      simp [Matrix.map_neg, Matrix.map_one, Matrix.map_zero]
    rw [hJ] at h
    exact h
  have h1 : nsq (A *ᵥ v) = nsq ((S.map (fun x : ℝ => (x : ℂ))) *ᵥ v) := by
    rw [hfac, ← Matrix.mulVec_mulVec, nsq_omega]
  have h2 := complex_expand S c hc hS v
  rw [← h1, hAv, nsq_smul] at h2
  have hpos := nsq_pos hv0
  have h3 : c ^ 2 ≤ ‖z‖ ^ 2 := le_of_mul_le_mul_right h2 hpos
  exact (pow_le_pow_iff_left₀ hc (norm_nonneg z) two_ne_zero).mp h3
