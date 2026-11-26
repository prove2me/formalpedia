-- Prove2me | solution 1 for ErdosDyadic.dilate_density
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:31:15.809011+00:00
-- url     : https://prove2.me/submissions/2590ef74-0fc7-4a28-872d-f463fea48cdb

import Mathlib
import Definitions.Def_erdos_dyadic_IsPeriodic1
import Definitions.Def_erdos_dyadic_rho

set_option autoImplicit false

open MeasureTheory Set
open scoped Pointwise

namespace S74DD
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

end S74DD

open ErdosDyadic S74DD in
theorem solution (H : Set ℝ) (hH : IsPeriodic1 H) (hm : MeasurableSet H) (j : ℕ) :
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
