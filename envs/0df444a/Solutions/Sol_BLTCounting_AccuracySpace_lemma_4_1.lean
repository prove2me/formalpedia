-- Prove2me | solution 1 for BLTCounting.AccuracySpace.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:02:12.234815+00:00
-- url     : https://prove2.me/submissions/e7bc82be-fb97-49c0-8561-35b6e4e808d5

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix BLTCounting.AccuracySpace

namespace AuxLemma41

lemma specNorm_sq_le_frobNorm_sq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    specNorm A ^ 2 ≤ frobNorm A ^ 2 := by
  have hfrob_nn : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  have hop : specNorm A ≤ frobNorm A := by
    unfold specNorm
    refine ContinuousLinearMap.opNorm_le_bound _ hfrob_nn
      fun (x : EuclideanSpace ℂ n) => ?_
    have h_lhs : ‖(Matrix.toEuclideanLin A).toContinuousLinearMap x‖ ^ 2 =
        ∑ i : m, ‖(A *ᵥ x.ofLp) i‖ ^ 2 := by
      change ‖Matrix.toEuclideanLin A x‖ ^ 2 = ∑ i : m, ‖(A *ᵥ x.ofLp) i‖ ^ 2
      rw [PiLp.norm_sq_eq_of_L2, Matrix.toLpLin_apply]
    have h_rhs_x : ‖x‖ ^ 2 = ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    have hsum : ∑ i : m, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤
        (∑ i : m, ∑ j : n, ‖A i j‖ ^ 2) * ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
      calc
        ∑ i : m, ‖(A *ᵥ x.ofLp) i‖ ^ 2
            ≤ ∑ i : m, (∑ j : n, ‖A i j‖ ^ 2) * ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ‖(A *ᵥ x.ofLp) i‖ ≤ ∑ j : n, ‖A i j‖ * ‖x.ofLp j‖ := by
            simpa [Matrix.mulVec, dotProduct, norm_mul] using
              norm_sum_le Finset.univ (fun j : n => A i j * x.ofLp j)
          exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2)
            (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x.ofLp j‖))
        _ = (∑ i : m, ∑ j : n, ‖A i j‖ ^ 2) * ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
          rw [Finset.sum_mul]
    have hfrob_sq : frobNorm A ^ 2 = ∑ i : m, ∑ j : n, ‖A i j‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hsq : ‖(Matrix.toEuclideanLin A).toContinuousLinearMap x‖ ^ 2 ≤
        (frobNorm A * ‖x‖) ^ 2 := by
      rw [h_lhs, mul_pow, hfrob_sq, h_rhs_x]
      exact hsum
    exact le_of_sq_le_sq hsq (mul_nonneg hfrob_nn (norm_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) hop 2

lemma rpow_neg_quarter_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 / 4 : ℝ))) ^ 2 = (Real.sqrt x)⁻¹ := by
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hx.le,
    show -(1 / 4 : ℝ) * ((2 : ℕ) : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]

lemma inv_sqrt_le_two_sub (r : ℕ) (hr : 1 ≤ r) :
    1 / Real.sqrt (r : ℝ) ≤ 2 * (Real.sqrt (r : ℝ) - Real.sqrt (((r - 1 : ℕ) : ℝ))) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hr)
  have hsqrt_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr_pos
  have hcast : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by simp [Nat.cast_sub hr]
  have hdiff : (Real.sqrt (r : ℝ) - Real.sqrt ((r : ℝ) - 1)) *
      (Real.sqrt (r : ℝ) + Real.sqrt ((r : ℝ) - 1)) = 1 := by
    have hnn : 0 ≤ (r : ℝ) - 1 := sub_nonneg.mpr (Nat.one_le_cast.mpr hr)
    calc
      (Real.sqrt (r : ℝ) - Real.sqrt ((r : ℝ) - 1)) *
          (Real.sqrt (r : ℝ) + Real.sqrt ((r : ℝ) - 1))
          = Real.sqrt (r : ℝ) ^ 2 - Real.sqrt ((r : ℝ) - 1) ^ 2 := by ring
      _ = (r : ℝ) - ((r : ℝ) - 1) := by rw [Real.sq_sqrt hr_pos.le, Real.sq_sqrt hnn]
      _ = 1 := by ring
  have hsum_le : Real.sqrt (r : ℝ) + Real.sqrt ((r : ℝ) - 1) ≤ 2 * Real.sqrt (r : ℝ) := by
    have hle : Real.sqrt ((r : ℝ) - 1) ≤ Real.sqrt (r : ℝ) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  rw [hcast, div_le_iff₀ hsqrt_pos]
  calc
    (1 : ℝ) = (Real.sqrt (r : ℝ) - Real.sqrt ((r : ℝ) - 1)) *
        (Real.sqrt (r : ℝ) + Real.sqrt ((r : ℝ) - 1)) := hdiff.symm
    _ ≤ (Real.sqrt (r : ℝ) - Real.sqrt ((r : ℝ) - 1)) * (2 * Real.sqrt (r : ℝ)) := by
      refine mul_le_mul_of_nonneg_left hsum_le ?_
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    _ = 2 * (Real.sqrt (r : ℝ) - Real.sqrt ((r : ℝ) - 1)) * Real.sqrt (r : ℝ) := by ring

lemma sum_inv_sqrt_le (M : ℕ) :
    ∑ r ∈ Finset.Ico 1 (M + 1), (1 / Real.sqrt (r : ℝ)) ≤ 2 * Real.sqrt (M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hstep := inv_sqrt_le_two_sub (M + 1) (by omega)
    have hsub : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by simp
    rw [hsub] at hstep
    push_cast at hstep ⊢
    linarith

lemma half_antidiag_bound (k : ℕ) (hk : 2 ≤ k) :
    ∑ r ∈ Finset.Ico 1 (k / 2 + 1),
      (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ)))) ≤ 2 := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    ∑ r ∈ Finset.Ico 1 (k / 2 + 1), (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ))))
        ≤ ∑ r ∈ Finset.Ico 1 (k / 2 + 1),
          (Real.sqrt (2 / (k : ℝ)) * (1 / Real.sqrt (r : ℝ))) := by
      refine Finset.sum_le_sum fun r hr => ?_
      rw [Finset.mem_Ico] at hr
      have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
      have hkr : (k : ℝ) / 2 ≤ ((k - r : ℕ) : ℝ) := by
        have h1 : 2 * r ≤ k := by omega
        have h2 : r ≤ k := by omega
        rw [Nat.cast_sub h2]
        have h1' : (2 : ℝ) * (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        linarith
      have hprod : (r : ℝ) * ((k : ℝ) / 2) ≤ (r : ℝ) * (((k - r : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hkr hr_pos.le
      have hpos_lhs : 0 < (r : ℝ) * ((k : ℝ) / 2) := mul_pos hr_pos (half_pos hk_pos)
      have hsqrt_le : Real.sqrt ((r : ℝ) * ((k : ℝ) / 2)) ≤
          Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ))) :=
        Real.sqrt_le_sqrt hprod
      have hinv : 1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ))) ≤
          1 / Real.sqrt ((r : ℝ) * ((k : ℝ) / 2)) :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos_lhs) hsqrt_le
      refine le_trans hinv (le_of_eq ?_)
      rw [Real.sqrt_mul hr_pos.le, Real.sqrt_div hk_pos.le, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hr_pos), ne_of_gt (Real.sqrt_pos.mpr hk_pos)]
    _ = Real.sqrt (2 / (k : ℝ)) * ∑ r ∈ Finset.Ico 1 (k / 2 + 1), (1 / Real.sqrt (r : ℝ)) := by
      rw [← Finset.mul_sum]
    _ ≤ Real.sqrt (2 / (k : ℝ)) * (2 * Real.sqrt (((k / 2 : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_le (k / 2)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 / (k : ℝ)) * (2 * Real.sqrt ((k : ℝ) / 2)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (Real.sqrt_nonneg _)
      refine Real.sqrt_le_sqrt ?_
      have hdiv : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
      have hdiv' : (2 : ℝ) * (((k / 2 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hdiv
      linarith
    _ = 2 := by
      have h1 : Real.sqrt (2 / (k : ℝ)) * Real.sqrt ((k : ℝ) / 2) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have hmul : (2 / (k : ℝ)) * ((k : ℝ) / 2) = 1 := by field_simp [ne_of_gt hk_pos]
        rw [hmul, Real.sqrt_one]
      linarith

lemma antidiag_bound (k : ℕ) :
    ∑ r ∈ Finset.Ico 1 k, (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ)))) ≤ 4 := by
  by_cases hk : k < 2
  · have hemp : Finset.Ico 1 k = ∅ := by
      rw [Finset.Ico_eq_empty_iff]
      omega
    rw [hemp]
    norm_num
  · have hk : 2 ≤ k := Nat.le_of_not_lt hk
    have hsplit : Finset.Ico 1 k =
        Finset.Ico 1 (k / 2 + 1) ∪ Finset.Ico (k / 2 + 1) k := by
      symm
      exact Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
    have hdisj : Disjoint (Finset.Ico 1 (k / 2 + 1)) (Finset.Ico (k / 2 + 1) k) :=
      Finset.Ico_disjoint_Ico_consecutive 1 (k / 2 + 1) k
    rw [hsplit, Finset.sum_union hdisj]
    have h1 := half_antidiag_bound k hk
    have h2 : ∑ r ∈ Finset.Ico (k / 2 + 1) k,
        (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ)))) ≤
        ∑ u ∈ Finset.Ico 1 (k / 2 + 1),
          (1 / Real.sqrt ((u : ℝ) * (((k - u : ℕ) : ℝ)))) := by
      have hinj : ∀ r ∈ Finset.Ico (k / 2 + 1) k, k - r ∈ Finset.Ico 1 (k / 2 + 1) := by
        intro r hr
        rw [Finset.mem_Ico] at hr ⊢
        omega
      calc
        ∑ r ∈ Finset.Ico (k / 2 + 1) k, (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ))))
            = ∑ u ∈ (Finset.Ico (k / 2 + 1) k).image (fun r => k - r),
              (1 / Real.sqrt ((u : ℝ) * (((k - u : ℕ) : ℝ)))) := by
          rw [Finset.sum_image]
          · refine Finset.sum_congr rfl fun r hr => ?_
            rw [Finset.mem_Ico] at hr
            have hsub : k - (k - r) = r := by omega
            rw [hsub, mul_comm]
          · intro r₁ hr₁ r₂ hr₂ heq
            simp only [Finset.mem_coe, Finset.mem_Ico] at hr₁ hr₂
            dsimp at heq
            omega
        _ ≤ ∑ u ∈ Finset.Ico 1 (k / 2 + 1),
            (1 / Real.sqrt ((u : ℝ) * (((k - u : ℕ) : ℝ)))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨r, hr, rfl⟩
          exact hinj r hr
    linarith [half_antidiag_bound k hk]

end AuxLemma41

theorem solution (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 m) (e : ℕ → ℂ) :
    specNorm (weightedHankel S e) ^ 2 ≤ frobNorm (weightedHankel S e) ^ 2 ∧
      frobNorm (weightedHankel S e) ^ 2 ≤
        4 * ∑ k ∈ Finset.range (2 * m - 1), ‖e k‖ ^ 2 := by
  refine ⟨AuxLemma41.specNorm_sq_le_frobNorm_sq (weightedHankel S e), ?_⟩
  have hfrob_sq : frobNorm (weightedHankel S e) ^ 2 =
      ∑ r : S, ∑ s : S, ‖weightedHankel S e r s‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hfrob_sq]
  have hentry : ∀ r s : S,
      ‖weightedHankel S e r s‖ ^ 2 =
        ‖e ((r : ℕ) + (s : ℕ))‖ ^ 2 * (1 / Real.sqrt (((r : ℕ) : ℝ) * ((s : ℕ) : ℝ))) := by
    intro r s
    have hr1 : 1 ≤ (r : ℕ) := (Finset.mem_Ico.mp (hS r.2)).1
    have hs1 : 1 ≤ (s : ℕ) := (Finset.mem_Ico.mp (hS s.2)).1
    have hr_pos : (0 : ℝ) < ((r : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hs_pos : (0 : ℝ) < ((s : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hw : weightedHankel S e r s =
        ((((r : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * e ((r : ℕ) + (s : ℕ)) *
          ((((s : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) := by
      simp [weightedHankel, weightDiag, hankelOn, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    rw [hw, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hr_pos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hs_pos.le _)]
    have hmul_pow : ((((r : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) * ‖e ((r : ℕ) + (s : ℕ))‖ *
        ((s : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2) =
        ‖e ((r : ℕ) + (s : ℕ))‖ ^ 2 *
          ((((r : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 * (((s : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2) := by
      ring
    rw [hmul_pow, AuxLemma41.rpow_neg_quarter_sq hr_pos, AuxLemma41.rpow_neg_quarter_sq hs_pos,
      Real.sqrt_mul hr_pos.le]
    ring
  have hsub : (∑ r : S, ∑ s : S, ‖weightedHankel S e r s‖ ^ 2) ≤
      ∑ r ∈ Finset.Ico 1 m, ∑ s ∈ Finset.Ico 1 m,
        ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ))) := by
    have heq : (∑ r : S, ∑ s : S, ‖weightedHankel S e r s‖ ^ 2) =
        ∑ r ∈ S, ∑ s ∈ S, ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ))) := by
      have h1 : (∑ r : S, ∑ s : S, ‖weightedHankel S e r s‖ ^ 2) =
          ∑ r : S, ∑ s : S, ‖e ((r : ℕ) + (s : ℕ))‖ ^ 2 *
            (1 / Real.sqrt (((r : ℕ) : ℝ) * ((s : ℕ) : ℝ))) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => hentry r s
      rw [h1]
      simp only [Finset.univ_eq_attach]
      have h_inner : ∀ r : S,
          (∑ s ∈ S.attach, ‖e ((r : ℕ) + (s : ℕ))‖ ^ 2 *
            (1 / Real.sqrt (((r : ℕ) : ℝ) * ((s : ℕ) : ℝ)))) =
          ∑ s ∈ S, ‖e ((r : ℕ) + s)‖ ^ 2 * (1 / Real.sqrt (((r : ℕ) : ℝ) * (s : ℝ))) :=
        fun r => Finset.sum_attach S (fun s =>
          ‖e ((r : ℕ) + s)‖ ^ 2 * (1 / Real.sqrt (((r : ℕ) : ℝ) * (s : ℝ))))
      simp_rw [h_inner]
      exact Finset.sum_attach S (fun r =>
        ∑ s ∈ S, ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ))))
    rw [heq]
    calc
      ∑ r ∈ S, ∑ s ∈ S, ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ)))
          ≤ ∑ r ∈ S, ∑ s ∈ Finset.Ico 1 m,
            ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ))) := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => by positivity
      _ ≤ ∑ r ∈ Finset.Ico 1 m, ∑ s ∈ Finset.Ico 1 m,
          ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ))) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => by positivity
  have hfiber : (∑ r ∈ Finset.Ico 1 m, ∑ s ∈ Finset.Ico 1 m,
      ‖e (r + s)‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (s : ℝ)))) ≤
      ∑ k ∈ Finset.range (2 * m - 1), ∑ r ∈ Finset.Ico 1 k,
        ‖e k‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ)))) := by
    rw [← Finset.sum_product', Finset.sum_sigma']
    let f : ℕ × ℕ → (Σ _ : ℕ, ℕ) := fun p => ⟨p.1 + p.2, p.1⟩
    calc
      ∑ p ∈ Finset.Ico 1 m ×ˢ Finset.Ico 1 m,
          ‖e (p.1 + p.2)‖ ^ 2 * (1 / Real.sqrt ((p.1 : ℝ) * (p.2 : ℝ)))
          = ∑ q ∈ (Finset.Ico 1 m ×ˢ Finset.Ico 1 m).image f,
            ‖e q.1‖ ^ 2 * (1 / Real.sqrt ((q.2 : ℝ) * (((q.1 - q.2 : ℕ) : ℝ)))) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun p _ => ?_
          simp [f]
        · intro p₁ _ p₂ _ heq
          rcases p₁ with ⟨r₁, s₁⟩
          rcases p₂ with ⟨r₂, s₂⟩
          simp only [f, Sigma.mk.inj_iff, heq_eq_eq] at heq
          rcases heq with ⟨hsum, hr⟩
          subst hr
          ext <;> omega
      _ ≤ ∑ q ∈ (Finset.range (2 * m - 1)).sigma (fun k => Finset.Ico 1 k),
          ‖e q.1‖ ^ 2 * (1 / Real.sqrt ((q.2 : ℝ) * (((q.1 - q.2 : ℕ) : ℝ)))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨⟨r, s⟩, hp, rfl⟩
        simp only [Finset.mem_product, Finset.mem_Ico] at hp
        simp only [f, Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
        omega
  calc
    (∑ r : S, ∑ s : S, ‖weightedHankel S e r s‖ ^ 2)
        ≤ ∑ k ∈ Finset.range (2 * m - 1), ∑ r ∈ Finset.Ico 1 k,
          ‖e k‖ ^ 2 * (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ)))) := le_trans hsub hfiber
    _ = ∑ k ∈ Finset.range (2 * m - 1),
        ‖e k‖ ^ 2 * ∑ r ∈ Finset.Ico 1 k, (1 / Real.sqrt ((r : ℝ) * (((k - r : ℕ) : ℝ)))) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (2 * m - 1), ‖e k‖ ^ 2 * 4 := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_left (AuxLemma41.antidiag_bound k) (sq_nonneg _)
    _ = 4 * ∑ k ∈ Finset.range (2 * m - 1), ‖e k‖ ^ 2 := by
      rw [← Finset.sum_mul, mul_comm]
