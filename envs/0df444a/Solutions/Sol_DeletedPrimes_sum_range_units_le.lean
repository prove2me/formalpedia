-- Prove2me | solution 1 for DeletedPrimes.sum_range_units_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:42.285017+00:00
-- url     : https://prove2.me/submissions/cd644381-0d8f-469d-9bf5-73ed3c01f359

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_ne_zero_iff
import Theorems.Thm_DeletedPrimes_abs_muS_real

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (σ : ℝ) (N : ℕ) :
    ∑ d ∈ Finset.range N, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) ≤
      ∏ p ∈ (Finset.range N).filter (· ∈ S), (1 + (p : ℝ) ^ (-σ)) := by
  set P := (Finset.range N).filter (· ∈ S)
  set A := (Finset.range N).filter (fun d => muS S d ≠ 0)
  have h1 : ∑ d ∈ Finset.range N, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) = ∑ d ∈ A, (d : ℝ) ^ (-σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [abs_muS_real]
    split_ifs <;> simp_all
  have h2 : ∑ d ∈ A, (d : ℝ) ^ (-σ) = ∑ d ∈ A, ∏ p ∈ d.primeFactors, (p : ℝ) ^ (-σ) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hsq := (muS_ne_zero_iff.mp (Finset.mem_filter.mp hd).2).1
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
  have hinj : Set.InjOn Nat.primeFactors (A : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (muS_ne_zero_iff.mp (Finset.mem_filter.mp ha).2).1
    have hb' := (muS_ne_zero_iff.mp (Finset.mem_filter.mp hb).2).1
    rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb', hab]
  have h3 : ∑ d ∈ A, ∏ p ∈ d.primeFactors, (p : ℝ) ^ (-σ) =
      ∑ T ∈ A.image Nat.primeFactors, ∏ p ∈ T, (p : ℝ) ^ (-σ) :=
    (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, (p : ℝ) ^ (-σ)) hinj).symm
  have hsub : A.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hdN, hd0⟩ := Finset.mem_filter.mp hd
    have hS' := (muS_ne_zero_iff.mp hd0).2
    rw [Finset.mem_powerset]
    intro p hp
    have hdpos : d ≠ 0 := by
      intro h; apply hd0; rw [h]; simp [muS]
    have hpd : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hdpos) (Nat.dvd_of_mem_primeFactors hp)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hpd (Finset.mem_range.mp hdN)), hS' p hp⟩
  rw [h1, h2, h3, Finset.prod_one_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ =>
    Finset.prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
end DeletedPrimes
