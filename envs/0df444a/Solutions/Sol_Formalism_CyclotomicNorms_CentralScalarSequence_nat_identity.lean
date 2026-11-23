-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.nat_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:43.601845+00:00
-- url     : https://prove2.me/submissions/6d67f84f-a75f-4b31-a9cc-35a67af0992c

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_a
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_b
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_c
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_d
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_e
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_f
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_g
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_seq_h
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_abstract
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_sgn_succ
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_sgn_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution (ρ : Representation R G W) (z : G) (hz : ∀ g, z * g = g * z) (n : ℕ)
    (φ : (ℕ → G) → W) (hφ : ∀ u v : ℕ → G, (∀ k < n + 1, u k = v k) → φ u = φ v) (y : ℕ → G)
    (hcoc : ∀ i < n + 2, ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1))) +
      ∑ j ∈ range (n + 2), (-1 : R) ^ (j + 1) • φ (contrN j (insN i z y)) = 0) :
    ρ (y 0) (∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (fun k => y (k + 1)))) +
      ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
        ∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (contrN j y))
      = ρ z (φ y) - φ y := by
  have h0 : (∑ i ∈ range (n + 2), (-1 : R) ^ i • ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1))))
      + ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
          (-1 : R) ^ (i + (j + 1)) • φ (contrN j (insN i z y)) = 0 := by
    rw [← sum_add_distrib]
    refine sum_eq_zero fun i hi => ?_
    have := congrArg (fun w => (-1 : R) ^ i • w) (hcoc i (mem_range.mp hi))
    simp only [smul_add, smul_sum, smul_smul, ← pow_add, smul_zero] at this
    exact this
  have hA : ∑ i ∈ range (n + 2), (-1 : R) ^ i • ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1)))
      = ρ z (φ y) - ρ (y 0) (∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (fun k => y (k + 1)))) := by
    rw [sum_range_succ']
    simp only [seq_d, seq_e, seq_f, seq_g, pow_zero, one_smul, map_sum, map_smul, sgn_succ,
      neg_smul, sum_neg_distrib]
    abel
  have hK := abstract (fun i j => (-1 : R) ^ (i + (j + 1)) • φ (contrN j (insN i z y)))
      (fun i j => (-1 : R) ^ (i + (j + 1)) • φ (insN i z (contrN j y)))
      (fun M j h => by
        rw [seq_a z y M j h, show M + 1 + (j + 1) = M + (j + 1) + 1 by omega, sgn_succ, neg_smul])
      (fun M => by
        rw [seq_b z y hz M, show M + 1 + (M + 1) = M + (M + 1) + 1 by omega, sgn_succ, neg_smul])
      (fun M i h => by
        rw [seq_c z y M i h, show i + (M + 1 + 1) = i + (M + 1) + 1 by omega, sgn_succ, neg_smul])
      (n + 1)
  rw [sgn_diag, neg_one_smul, hφ _ y (seq_h z y n)] at hK
  have hB : ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
        ∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (contrN j y)) =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (-1 : R) ^ (i + (j + 1)) • φ (insN i z (contrN j y)) := by
    simp only [smul_sum, smul_smul, ← pow_add]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [show j + 1 + i = i + (j + 1) by omega]
  rw [hA, eq_sub_of_add_eq hK] at h0
  rw [hB]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h0]
  abel
end Formalism.CyclotomicNorms.CentralScalarSequence
