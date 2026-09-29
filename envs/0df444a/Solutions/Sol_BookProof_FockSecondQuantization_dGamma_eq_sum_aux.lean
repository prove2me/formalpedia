-- Prove2me | solution 1 for BookProof.FockSecondQuantization.dGamma_eq_sum_aux
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:46.635703+00:00
-- url     : https://prove2.me/submissions/7c312800-0786-4d6f-a5af-a5e47523f63e

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.dGamma_eq_sum_aux
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_annA_single
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_single
import Theorems.Thm_BookProof_FockSecondQuantization_sum_creVec_annA_subset
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    ∀ K : Finset ℕ, modes u ⊆ K → dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := by

  classical
  induction u using Finsupp.induction_linear with
  | zero => intro K _; simp
  | add f g hf hg =>
    intro K hK
    have hL1 : modes f ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    have hL2 : modes g ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have hKL : K ⊆ K ∪ (modes f ∪ modes g) := Finset.subset_union_left
    rw [map_add, hf _ hL1, hg _ hL2, ← Finset.sum_add_distrib,
      sum_creVec_annA_subset col (f + g) hKL hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]
  | single β c =>
    intro K hK
    have hsingle : (Finsupp.single β c : FockAlg) = c • Finsupp.single β (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hc : c = 0
    · subst hc
      simp
    have hb : β.support ⊆ K := by
      refine fun i hi => hK ?_
      exact Finset.mem_biUnion.mpr ⟨β, Finsupp.mem_support_iff.mpr (by simpa using hc), hi⟩
    have hzero : ∀ k ∈ K, k ∉ β.support →
        creVec (col k) (annA k (Finsupp.single β c)) = 0 := by
      intro k _ hk
      have hβ : β k = 0 := by simpa using hk
      have hz : annA k (Finsupp.single β c) = 0 := by
        rw [annA_single, hβ]
        simp
      rw [hz, map_zero]
    rw [← Finset.sum_subset hb hzero, dGamma_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsingle, map_smul, map_smul]
