-- Prove2me | solution 1 for ErdosDyadic.measure_C_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:34:45.173826+00:00
-- url     : https://prove2.me/submissions/fdb0ad43-e268-4f2d-bee1-f435e41db887

import Mathlib
import Definitions.Def_erdos_dyadic_IsPeriodic1
import Definitions.Def_erdos_dyadic_rho

set_option autoImplicit false

open MeasureTheory Set
open scoped Pointwise

namespace S74DD2
open ErdosDyadic

lemma per_nat (H : Set ℝ) (hH : IsPeriodic1 H) (x : ℝ) (n : ℕ) : x + n ∈ H ↔ x ∈ H := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [← ih, hH (x + k)]; push_cast; ring_nf

lemma ico_k (H : Set ℝ) (hH : IsPeriodic1 H) (k : ℕ) :
    volume (H ∩ Ico (k:ℝ) (k+1)) = volume (H ∩ Ico 0 1) := by
  have : H ∩ Ico (k:ℝ) (k+1) = (fun x => x + (-(k:ℝ))) ⁻¹' (H ∩ Ico 0 1) := by
    ext x
    simp only [mem_inter_iff, mem_Ico, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [← per_nat H hH _ k]; simpa using h1
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [← per_nat H hH _ k] at h1; simpa using h1
  rw [this, measure_preimage_add_right]

lemma ico_n (H : Set ℝ) (hH : IsPeriodic1 H) (hm : MeasurableSet H) (n : ℕ) :
    volume (H ∩ Ico (0:ℝ) n) = n * volume (H ∩ Ico 0 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hu : H ∩ Ico (0:ℝ) ((k+1:ℕ):ℝ) = (H ∩ Ico 0 (k:ℝ)) ∪ (H ∩ Ico (k:ℝ) (k+1)) := by
      rw [← inter_union_distrib_left]; push_cast
      rw [Ico_union_Ico_eq_Ico (Nat.cast_nonneg k) (by linarith)]
    rw [hu, measure_union _ (hm.inter measurableSet_Ico), ih, ico_k H hH k]
    · push_cast; ring
    · exact Disjoint.inter_left' _ (Disjoint.inter_right' _ (Ico_disjoint_Ico_same))



theorem dil (H : Set ℝ) (hH : IsPeriodic1 H) (hm : MeasurableSet H) (j : ℕ) :
    volume (((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H) ∩ Icc 0 1) = rho H := by
  set K : ℝ := ((2 ^ j : ℕ) : ℝ) with hK
  have hKpos : 0 < K := by positivity
  have hc : (2 : ℝ) ^ (-(j : ℤ)) = K⁻¹ := by rw [hK, zpow_neg, zpow_natCast]; push_cast; rfl
  rw [hc]
  have hset : (fun y : ℝ => K⁻¹ * y) '' H ∩ Icc 0 1 = K⁻¹ • (H ∩ Icc 0 K) := by
    ext x
    simp only [mem_inter_iff, mem_image, mem_Icc, mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, h0, h1⟩
      refine ⟨y, ⟨hy, ?_, ?_⟩, rfl⟩
      · by_contra h; replace h := lt_of_not_ge h
        have : K⁻¹ * y < 0 := mul_neg_of_pos_of_neg (inv_pos.2 hKpos) h
        linarith
      · have := (inv_mul_le_iff₀ hKpos).1 h1; linarith
    · rintro ⟨y, ⟨hy, h0, h1⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, by positivity, ?_⟩
      rw [inv_mul_le_iff₀ hKpos]; linarith
  rw [hset, Measure.addHaar_smul]
  have hIcc : volume (H ∩ Icc 0 K) = volume (H ∩ Ico 0 K) := by
    apply measure_congr
    exact (ae_eq_refl H).inter Ico_ae_eq_Icc.symm
  have h1 : rho H = volume (H ∩ Ico 0 1) := by
    unfold rho
    apply measure_congr
    exact (ae_eq_refl H).inter Ico_ae_eq_Icc.symm
  rw [hIcc, h1, hK, ico_n H hH hm (2 ^ j)]
  simp only [Module.finrank_self, pow_one]
  rw [← mul_assoc]
  have : ENNReal.ofReal |((2 ^ j : ℕ) : ℝ)⁻¹| * ((2 ^ j : ℕ) : ENNReal) = 1 := by
    rw [abs_of_pos (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ (by positivity)]
    simp
  rw [this, one_mul]

lemma rho_neg (H : Set ℝ) (hH : ErdosDyadic.IsPeriodic1 H) :
    ErdosDyadic.rho (Neg.neg ⁻¹' H) = ErdosDyadic.rho H := by
  unfold ErdosDyadic.rho
  have : Neg.neg ⁻¹' H ∩ Icc (0:ℝ) 1 = Neg.neg ⁻¹' (H ∩ Icc (-1) 0) := by
    ext x; simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h, a, b⟩; exact ⟨h, by linarith, by linarith⟩
    · rintro ⟨h, a, b⟩; exact ⟨h, by linarith, by linarith⟩
  rw [this, show (Neg.neg ⁻¹' (H ∩ Icc (-1:ℝ) 0)) = -(H ∩ Icc (-1:ℝ) 0) from rfl, Measure.measure_neg]
  have : H ∩ Icc (-1:ℝ) 0 = (fun x => x + 1) ⁻¹' (H ∩ Icc 0 1) := by
    ext x; simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h, a, b⟩; exact ⟨(hH x).1 h, by linarith, by linarith⟩
    · rintro ⟨h, a, b⟩; exact ⟨(hH x).2 h, by linarith, by linarith⟩
  rw [this, measure_preimage_add_right]

lemma per_neg (H : Set ℝ) (hH : ErdosDyadic.IsPeriodic1 H) :
    ErdosDyadic.IsPeriodic1 (Neg.neg ⁻¹' H) := by
  intro x
  simp only [mem_preimage]
  rw [hH (-(x+1))]; ring_nf

lemma tl (η : ℝ) (hη0 : 0 < η) (g : ℕ → ENNReal)
    (hg : g = fun j => if 1 ≤ j then ENNReal.ofReal (η / 2 * (1 / 2) ^ j) else 0) :
    ∑' j, g j = ENNReal.ofReal (η / 2) := by
  have hs : ∀ n : ℕ, g n = ENNReal.ofReal (if 1 ≤ n then η / 2 * (1 / 2) ^ n else 0) := by
    intro n; rw [hg]; by_cases h : 1 ≤ n
    · simp only [if_pos h]
    · simp only [if_neg h, ENNReal.ofReal_zero]
  rw [tsum_congr hs, ← ENNReal.ofReal_tsum_of_nonneg]
  · congr 1
    rw [tsum_eq_zero_add']
    · simp only [if_neg (show ¬ 1 ≤ 0 from by norm_num), zero_add]
      have : ∀ n : ℕ, (if 1 ≤ n + 1 then η / 2 * (1 / 2 : ℝ) ^ (n + 1) else 0) = η / 4 * (1/2)^n := by
        intro n; rw [if_pos (by omega)]; ring
      rw [tsum_congr this, tsum_mul_left, tsum_geometric_two]; ring
    · have : (fun n : ℕ => (if 1 ≤ n + 1 then η / 2 * (1 / 2 : ℝ) ^ (n + 1) else 0)) = fun n => η / 4 * (1/2)^n := by
        funext n; rw [if_pos (by omega)]; ring
      rw [this]; exact summable_geometric_two.mul_left _
  · intro n; split_ifs <;> positivity
  · refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) (summable_geometric_two.mul_left (η / 2))
    split_ifs
    · exact le_refl _
    · positivity

end S74DD2

open ErdosDyadic S74DD2 in
theorem solution (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) 1) (H : ℕ → Set ℝ)
    (hper : ∀ j, IsPeriodic1 (H j)) (hmeas : ∀ j, MeasurableSet (H j))
    (hrho : ∀ j, 1 ≤ j → rho (H j) ≤ ENNReal.ofReal (6 * (η / 24 * (1 / 2) ^ j))) :
    volume ((⋃ j ∈ {j : ℕ | 1 ≤ j},
          (((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j))) ∩ Icc 0 1)
      ≤ ENNReal.ofReal (η / 2) := by
  have hη0 : 0 < η := hη.1
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ENNReal, g = fun j => if 1 ≤ j then ENNReal.ofReal (η / 2 * (1 / 2) ^ j) else 0 := ⟨_, rfl⟩
  have hB : ∀ j : ℕ, ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j) =
      (fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' (Neg.neg ⁻¹' H j) := by
    intro j; ext x; simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨-y, by simpa using hy, by ring⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨-y, hy, by ring⟩
  have hterm : ∀ j, volume (⋃ (_ : j ∈ {j : ℕ | 1 ≤ j}),
      ((((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j)) ∩ Icc 0 1)) ≤ g j := by
    intro j
    by_cases hj : 1 ≤ j
    · have hmem : j ∈ {j : ℕ | 1 ≤ j} := hj
      simp only [mem_ofPred_eq, hj, iUnion_true, hg, if_pos hj]
      rw [union_inter_distrib_right]
      refine (measure_union_le _ _).trans ?_
      rw [dil _ (hper j) (hmeas j), hB, dil _ (per_neg _ (hper j)) (measurableSet_preimage measurable_neg (hmeas j)), rho_neg _ (hper j)]
      have := hrho j hj
      calc rho (H j) + rho (H j) ≤ ENNReal.ofReal (6 * (η / 24 * (1 / 2) ^ j)) + ENNReal.ofReal (6 * (η / 24 * (1 / 2) ^ j)) := add_le_add this this
        _ = ENNReal.ofReal (η / 2 * (1 / 2) ^ j) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    · have hmem : j ∉ {j : ℕ | 1 ≤ j} := hj
      rw [hg]; simp only [if_neg hj]; simp [hmem]
  have hset : (⋃ j ∈ {j : ℕ | 1 ≤ j},
          (((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j))) ∩ Icc 0 1 =
      ⋃ j, ⋃ (_ : j ∈ {j : ℕ | 1 ≤ j}),
      ((((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j)) ∩ Icc 0 1) := by
    rw [iUnion_inter]; congr 1; funext j; rw [iUnion_inter]
  rw [hset]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_))
  exact tl η hη0 g hg
