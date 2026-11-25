-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.iterated_sum_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:41.909944+00:00
-- url     : https://prove2.me/submissions/7d529316-57c7-4b4f-bcc4-8995a753c765

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lOneNorm_sum_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lOneNorm_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.IteratedHighestWeightBound := by
  classical
  intro V P Λ _ _ _ jh Dop wt N1 Ninf lam Gam c0 q0 hGam hN1 hNinf hN10 hNinf0 hstep μ al
  induction al with
  | nil =>
    intro _
    refine ⟨Finsupp.single 0 1, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro ν hν
      have : ν = 0 := by simpa using Finsupp.support_single_subset hν
      subst this
      simp [hN10, hNinf0]
  | cons l al ih =>
    intro hq
    simp only [List.map_cons, List.sum_cons, List.prod_cons, List.length_cons] at hq ⊢
    obtain ⟨a, ha1, ha2, ha3⟩ := ih (by omega)
    have hb : ∀ ν, ∃ b : P →₀ ℂ, ν ∈ a.support →
        (Dop l (jh (μ + ν)) = b.sum (fun ν' c => c • jh (μ + ν + ν')) ∧
        (b.sum fun _ c => ‖c‖) ≤ Gam ^ wt l ∧ ∀ ν' ∈ b.support, N1 ν' ≤ wt l ∧ Ninf ν' ≤ 1) := by
      intro ν
      by_cases hν : ν ∈ a.support
      · have h1 := (ha3 ν hν).1
        have h2 : N1 (μ + ν - lam) ≤ N1 (μ - lam) + N1 ν := by
          have : μ + ν - lam = (μ - lam) + ν := by abel
          rw [this]
          exact hN1 _ _
        obtain ⟨b, hb⟩ := hstep (μ + ν) l (by omega)
        exact ⟨b, fun _ => hb⟩
      · exact ⟨0, fun h => absurd h hν⟩
    choose b hb using hb
    let a' : P →₀ ℂ := ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, Finsupp.single (ν + ν') (a ν * b ν ν')
    refine ⟨a', ?_, ?_, ?_⟩
    · rw [Module.End.mul_apply, ha1]
      have hΨ : a'.sum (fun ν c => c • jh (μ + ν)) =
          Finsupp.linearCombination ℂ (fun ν => jh (μ + ν)) a' :=
        (Finsupp.linearCombination_apply ℂ a').symm
      rw [hΨ]
      simp only [a', map_sum, Finsupp.linearCombination_single]
      rw [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [map_smul, (hb ν hν).1, Finsupp.sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun ν' _ => ?_
      rw [mul_smul, add_assoc]
    · have h1 : lOneNorm a' ≤ ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, ‖a ν‖ * ‖b ν ν'‖ := by
        refine (lOneNorm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        refine (lOneNorm_sum_le _ _).trans (Finset.sum_le_sum fun ν' _ => ?_)
        rw [lOneNorm_single, norm_mul]
      calc (a'.sum fun _ c => ‖c‖) ≤ ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, ‖a ν‖ * ‖b ν ν'‖ := h1
        _ ≤ ∑ ν ∈ a.support, ‖a ν‖ * Gam ^ wt l := by
            refine Finset.sum_le_sum fun ν hν => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hb ν hν).2.1 (norm_nonneg _)
        _ = (a.sum fun _ c => ‖c‖) * Gam ^ wt l := by rw [Finsupp.sum, Finset.sum_mul]
        _ ≤ Gam ^ (al.map wt).sum * Gam ^ wt l := by gcongr
        _ = Gam ^ (wt l + (al.map wt).sum) := by rw [← pow_add, add_comm]
    · intro ν'' h
      have h1 := Finsupp.support_finsetSum h
      rw [Finset.mem_biUnion] at h1
      obtain ⟨ν, hν, h2⟩ := h1
      have h3 := Finsupp.support_finsetSum h2
      rw [Finset.mem_biUnion] at h3
      obtain ⟨ν', hν', h4⟩ := h3
      have h5 : ν'' = ν + ν' := by simpa using Finsupp.support_single_subset h4
      subst h5
      have e1 := hN1 ν ν'
      have e2 := hNinf ν ν'
      have e3 := ha3 ν hν
      have e4 := (hb ν hν).2.2 ν' hν'
      constructor <;> omega
end Formalism.HermitianLatticeCounting.P
