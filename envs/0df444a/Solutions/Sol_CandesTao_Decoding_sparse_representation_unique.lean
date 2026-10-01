-- Prove2me | solution 1 for CandesTao.Decoding.sparse_representation_unique
-- status  : ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-10-01T04:56:32.137303+00:00
-- url     : https://prove2.me/submissions/1ef1dd60-9f39-415e-a01e-9abc1901fd49

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open CandesTao.Decoding

/-- `‖x‖² = ∑ xᵢ²`. -/
private lemma l2Norm_sq' {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

/-- Cauchy–Schwarz row by row: `‖F x‖² ≤ (∑ᵢⱼ Fᵢⱼ²) ‖x‖²`. -/
private lemma mulVec_sq_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * l2Norm x ^ 2 := by
  rw [l2Norm_sq', l2Norm_sq', Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem solution {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 2 * S ≤ m) (hδ : restrictedIsometryConst F (2 * S) < 1)
    (T T' : Finset (Fin m)) (hT : T.card ≤ S) (hT' : T'.card ≤ S)
    (c c' : Fin m → ℝ) (hc : SupportedOn c T) (hc' : SupportedOn c' T')
    (hf : F.mulVec c = F.mulVec c') : c = c' := by
  classical
  set d : Fin m → ℝ := c - c' with hd_def
  have hd : SupportedOn d (T ∪ T') := by
    intro j hj
    rw [Finset.mem_union, not_or] at hj
    simp [hd_def, hc j hj.1, hc' j hj.2]
  have hcard : (T ∪ T').card ≤ 2 * S := (Finset.card_union_le _ _).trans (by omega)
  have hFd : F.mulVec d = 0 := by
    rw [hd_def, Matrix.mulVec_sub, hf, sub_self]
  -- the admissible set of isometry constants is nonempty
  set K : ℝ := ∑ i, ∑ j, F i j ^ 2 with hK
  have hne : {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ 2 * S → ∀ c : Fin m → ℝ,
      SupportedOn c T →
      (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
      l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}.Nonempty := by
    refine ⟨max 1 K, le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro U _ x _
    have h0 : 0 ≤ l2Norm x ^ 2 := sq_nonneg _
    have h1 : 0 ≤ l2Norm (F.mulVec x) ^ 2 := sq_nonneg _
    have hb := mulVec_sq_le F x
    have hm1 : 1 ≤ max 1 K := le_max_left _ _
    have hmK : K ≤ max 1 K := le_max_right _ _
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨δ, hδmem, hδlt⟩ := exists_lt_of_csInf_lt hne hδ
  have key := (hδmem.2 (T ∪ T') hcard d hd).1
  rw [hFd] at key
  have hz : l2Norm (0 : Fin p → ℝ) ^ 2 = 0 := by rw [l2Norm_sq']; simp
  rw [hz] at key
  have hpos : 0 < 1 - δ := by linarith
  have hd0 : l2Norm d ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    have := mul_pos hpos h
    linarith
  rw [l2Norm_sq'] at hd0
  have hsum : ∑ i, d i ^ 2 = 0 :=
    le_antisymm hd0 (Finset.sum_nonneg fun i _ => sq_nonneg (d i))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (d i))] at hsum
  funext j
  have hj := hsum j (Finset.mem_univ j)
  have : d j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hj
  rw [hd_def, Pi.sub_apply, sub_eq_zero] at this
  exact this
