-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.weyl_le_of_stable_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:45.911772+00:00
-- url     : https://prove2.me/submissions/e70785fc-1ef3-4d3a-8a6d-50a1296aaecf

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_diag_weight_vector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_weight_vector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_eq_sum_weighted_components
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_le_of_stable
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (L : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ))
    (h0 : hw ℤ le_rfl ν ∈ L)
    (hs : ∀ a b : Fin r, a ≠ b → ∀ (k : ℕ) (f : MvPolynomial (Fin r × Fin r) ℤ), f ∈ L → rowDiv ℤ a b k f ∈ L) :
    weyl ℤ r r le_rfl ν ≤ L := by
  classical
  let L' : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
    ⨅ μ : Fin r → ℕ, L.comap (weightedHomogeneousComponent (rowW r r) μ)
  have hL' : ∀ x, x ∈ L' ↔ ∀ μ, weightedHomogeneousComponent (rowW r r) μ x ∈ L := by
    intro x
    simp [L', Submodule.mem_iInf]
  have hcomp : ∀ z ∈ L, (∃ μ', IsWeightedHomogeneous (rowW r r) z μ') →
      ∀ μ, weightedHomogeneousComponent (rowW r r) μ z ∈ L := by
    rintro z hz ⟨μ', hμ'⟩ μ
    by_cases h : μ = μ'
    · subst h
      rw [hμ'.weightedHomogeneousComponent_same]
      exact hz
    · rw [hμ'.weightedHomogeneousComponent_ne μ h]
      exact L.zero_mem
  have hle : L' ≤ L := by
    intro x hx
    obtain ⟨S, hS⟩ := eq_sum_weighted_components x
    rw [hS]
    exact L.sum_mem fun μ _ => (hL' x).1 hx μ
  refine (la_weyl_le_of_stable ℤ le_rfl ν L' ?_ ?_).trans hle
  · rw [hL']
    exact hcomp _ h0 ⟨_, hwRowWeight ℤ r r le_rfl ν hν⟩
  · intro a b k f hf
    rw [hL'] at hf ⊢
    intro μ
    obtain ⟨S, hS⟩ := eq_sum_weighted_components f
    have hT : weightedHomogeneousComponent (rowW r r) μ (rowDiv ℤ a b k f) =
        ∑ μ' ∈ S, weightedHomogeneousComponent (rowW r r) μ
          (rowDiv ℤ a b k (weightedHomogeneousComponent (rowW r r) μ' f)) := by
      conv_lhs => rw [hS]
      rw [← rowDivL_apply, map_sum, map_sum]
      rfl
    rw [hT]
    refine L.sum_mem fun μ' _ => ?_
    have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW r r) μ' f
    refine hcomp _ ?_ (divided_power_weight_vector a b k μ' _ hh) μ
    by_cases hab : a = b
    · subst hab
      rw [divided_power_diag_weight_vector a k μ' _ hh]
      exact L.smul_mem _ (hf μ')
    · exact hs a b hab k _ (hf μ')
end Formalism.CohomologicalDescent.LD
