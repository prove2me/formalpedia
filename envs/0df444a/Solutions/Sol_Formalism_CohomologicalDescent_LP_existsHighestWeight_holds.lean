-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.existsHighestWeight_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:06:16.233224+00:00
-- url     : https://prove2.me/submissions/d2abf3bf-a65d-4e6f-995f-d5c7a6d58f0b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds
import Theorems.Thm_Formalism_CohomologicalDescent_LP_lpa_joint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
private theorem weighted_sum_add_single_sub_single {K : Type*} [Field K] {q : ℕ} (μ : Fin q → K) (a b : Fin q) :
    ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c =
      ∑ c : Fin q, -((c : ℕ) : K) * μ c + ((b : ℕ) : K) - ((a : ℕ) : K) := by
  have hs : ∀ d : Fin q, ∑ c : Fin q, -((c : ℕ) : K) * (Pi.single d (1 : K) : Fin q → K) c = -((d : ℕ) : K) := by
    intro d
    rw [Finset.sum_eq_single d]
    · simp
    · intro c _ hcd
      rw [Pi.single_eq_of_ne hcd, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ d) h
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
  ring
end Formalism.CohomologicalDescent.LP
end

set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution : ExistsHW := by
  intro K N q _ _ _ _ _ _ T hT hdiag C hC hne
  classical
  have hcomm : ∀ a b, Commute (T a a) (T b b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact Commute.refl _
    · have h := hT a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero] at h
      exact sub_eq_zero.mp h
  obtain ⟨C', hC'C, hC'ne, _, μ0, hμ0⟩ :=
    lpa_joint (fun a => T a a) (fun a b => hcomm a b) hdiag Finset.univ C
      (fun a x hx => hC a a x hx) hne
  obtain ⟨x0, hx0C', hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC'ne
  obtain ⟨W, hW⟩ : ∃ W : Set (Fin q → K), ∀ ν, ν ∈ W ↔ ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v :=
    ⟨{ν | ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v}, fun ν => Iff.rfl⟩
  have hW0 : μ0 ∈ W := (hW μ0).mpr ⟨x0, hC'C hx0C', hx00, fun c => hμ0 c (Finset.mem_univ c) x0 hx0C'⟩
  have hfin : (Set.univ.pi fun c : Fin q => {z : K | (T c c).HasEigenvalue z}).Finite :=
    Set.Finite.pi fun c => Module.End.finite_hasEigenvalue (T c c)
  have hWfin : W.Finite := by
    refine hfin.subset ?_
    intro ν hν
    obtain ⟨v, -, hv0, hv⟩ := (hW ν).mp hν
    rw [Set.mem_univ_pi]
    intro c
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hv c), hv0⟩)
  obtain ⟨μ, hμW, hmax⟩ :=
    Set.exists_max_image W (fun ν => ∑ c : Fin q, -((c : ℕ) : K) * ν c) hWfin ⟨μ0, hW0⟩
  obtain ⟨v, hvC, hv0, hvw⟩ := (hW μ).mp hμW
  refine ⟨v, hvC, hv0, μ, And.intro ?_ hvw⟩
  intro a b hab
  by_contra hw
  have hba : b ≠ a := hab.ne'
  have hwt : ∀ c, T c c (T a b v) = (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c • T a b v := by
    intro c
    have h2 := LinearMap.congr_fun (hT c c a b) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hvw c, map_smul] at h2
    have h3 := sub_eq_iff_eq_add.mp h2
    by_cases hca : c = a
    · rw [hca] at h3 ⊢
      rw [if_pos rfl, if_neg hba, LinearMap.zero_apply, sub_zero] at h3
      rw [h3]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne, sub_zero]
      module
    · by_cases hcb : c = b
      · rw [hcb] at h3 ⊢
        rw [if_neg hba, if_pos rfl, LinearMap.zero_apply, zero_sub] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hba, add_zero]
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm), LinearMap.zero_apply, sub_zero, zero_add] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb,
          add_zero, sub_zero]
  have hνW : (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) ∈ W := (hW _).mpr ⟨T a b v, hC a b v hvC, hw, hwt⟩
  have hle : ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c ≤
      ∑ c : Fin q, -((c : ℕ) : K) * μ c := hmax _ hνW
  rw [weighted_sum_add_single_sub_single] at hle
  have hlt : ((a : ℕ) : K) < ((b : ℕ) : K) := by
    exact Nat.cast_lt.mpr hab
  linarith
end Formalism.CohomologicalDescent.LP
