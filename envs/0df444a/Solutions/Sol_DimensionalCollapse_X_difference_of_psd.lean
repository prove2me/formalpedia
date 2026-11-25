-- Prove2me | solution 1 for DimensionalCollapse.X_difference_of_psd
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:56:36.918051+00:00
-- url     : https://prove2.me/submissions/75ef9095-c512-4970-a183-771ac191af1d

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

set_option autoImplicit false

open Matrix Filter Topology
namespace DimensionalCollapse

lemma xd_alg {N : ℕ} (A : Fin N → Fin N → ℝ) (p q p' q' : Fin N → ℝ)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, A i j = 1 - A i i) :
    (∑ i, ((∑ j ∈ Finset.univ.erase i, A i j * (p' i - p j)) +
        (∑ j ∈ Finset.univ.erase i, A j i * (p i - p j))) * q i) -
      ∑ i, (1 - A i i) * (p' i - p i) * q' i =
    (∑ i, ∑ j, A i j * (p i - p j) * (q i - q j)) -
      ∑ i, (1 - A i i) * (p' i - p i) * (q' i - q i) := by
  have h1 : ∀ i, ∑ j ∈ Finset.univ.erase i, A i j * (p' i - p j) =
      (1 - A i i) * (p' i - p i) + ∑ j, A i j * (p i - p j) := by
    intro i
    have e : ∀ j, A i j * (p' i - p j) = A i j * (p' i - p i) + A i j * (p i - p j) := by
      intro j; ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, ← Finset.sum_mul, hrow,
      Finset.sum_erase _ (by ring)]
  have h2 : ∀ i, ∑ j ∈ Finset.univ.erase i, A j i * (p i - p j) = ∑ j, A j i * (p i - p j) := by
    intro i; rw [Finset.sum_erase _ (by ring)]
  simp only [h1, h2]
  have h3 : ∑ i, ∑ j, A i j * (p i - p j) * (q i - q j) =
      ∑ i, (∑ j, A i j * (p i - p j)) * q i + ∑ i, (∑ j, A j i * (p i - p j)) * q i := by
    have e : ∀ i j, A i j * (p i - p j) * (q i - q j) =
        A i j * (p i - p j) * q i + A i j * (p j - p i) * q j := by intros; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
  rw [h3]
  simp only [add_mul, Finset.sum_add_distrib]
  have e4 : ∀ i, (1 - A i i) * (p' i - p i) * (q' i - q i) =
      (1 - A i i) * (p' i - p i) * q' i - (1 - A i i) * (p' i - p i) * q i := by intros; ring
  simp only [e4, Finset.sum_sub_distrib]
  ring

lemma xd_Z_pos {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) : 0 < partitionZ z z' i := by
  unfold partitionZ
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase i) =>
    (Real.exp_pos (-sqNorm (z i - z j) / 2)).le)
  have := Real.exp_pos (-sqNorm (z i - z' i) / 2)
  linarith

lemma xd_alpha_nonneg {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i j : Fin N) : 0 ≤ alpha z z' i j := by
  unfold alpha
  apply div_nonneg _ (xd_Z_pos z z' i).le
  split_ifs <;> exact (Real.exp_pos _).le

lemma xd_row {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) :
    ∑ j ∈ Finset.univ.erase i, alpha z z' i j = 1 - alpha z z' i i := by
  have hZ := xd_Z_pos z z' i
  have e : ∀ j ∈ Finset.univ.erase i, alpha z z' i j =
      Real.exp (-sqNorm (z i - z j) / 2) / partitionZ z z' i := by
    intro j hj
    unfold alpha; rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  unfold alpha; rw [if_pos rfl]
  field_simp
  unfold partitionZ; ring

lemma xd_alpha_le {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) : alpha z z' i i ≤ 1 := by
  have := xd_row z z' i
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase i) => xd_alpha_nonneg z z' i j)
  linarith

theorem X_difference_of_psd {N n d : ℕ} (x x' : Fin N → Fin n → ℝ)
    (W : Matrix (Fin d) (Fin n) ℝ) :
    Xmat x x' W = Sigma0 x x' W - Sigma1 x x' W ∧
      (Sigma0 x x' W).PosSemidef ∧ (Sigma1 x x' W).PosSemidef := by
  set z := embed W x
  set z' := embed W x'
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Xmat, Sigma0, Sigma1, Matrix.of_apply, Matrix.sub_apply]
    exact xd_alg (alpha z z') (fun i => x i a) (fun i => x i b) (fun i => x' i a)
      (fun i => x' i b) (xd_row z z')
  · have e : Sigma0 x x' W = ∑ i, ∑ j, alpha z z' i j • vecMulVec (x i - x j) (star (x i - x j)) := by
      ext a b
      simp [Sigma0, Matrix.sum_apply, vecMulVec_apply, mul_assoc]; rfl
    rw [e]
    refine Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_sum _ (fun j _ => ?_))
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (xd_alpha_nonneg z z' i j)
  · have e : Sigma1 x x' W = ∑ i, (1 - alpha z z' i i) • vecMulVec (x' i - x i) (star (x' i - x i)) := by
      ext a b
      simp [Sigma1, Matrix.sum_apply, vecMulVec_apply, mul_assoc]; rfl
    rw [e]
    refine Matrix.posSemidef_sum _ (fun i _ => ?_)
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (sub_nonneg.2 (xd_alpha_le z z' i))

end DimensionalCollapse

open DimensionalCollapse in
theorem solution {N n d : ℕ} (x x' : Fin N → Fin n → ℝ)
    (W : Matrix (Fin d) (Fin n) ℝ) :
    Xmat x x' W = Sigma0 x x' W - Sigma1 x x' W ∧
      (Sigma0 x x' W).PosSemidef ∧ (Sigma1 x x' W).PosSemidef :=
  DimensionalCollapse.X_difference_of_psd x x' W
