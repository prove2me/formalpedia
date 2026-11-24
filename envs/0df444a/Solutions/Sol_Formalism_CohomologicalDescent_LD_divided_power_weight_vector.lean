-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_weight_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:47.017218+00:00
-- url     : https://prove2.me/submissions/3677d233-fa97-414c-a8ab-82a343daf987

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_weight_wc_eq_degree
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_rowDiv_shift
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
theorem _root_.solution {r : ℕ} (a b : Fin r) (k : ℕ) (μ : Fin r → ℕ) (y : MvPolynomial (Fin r × Fin r) ℤ)
    (hy : IsWeightedHomogeneous (rowW r r) y μ) :
    ∃ μ', IsWeightedHomogeneous (rowW r r) (rowDiv ℤ a b k y) μ' := by
  by_cases h0 : rowDiv ℤ a b k y = 0
  · exact ⟨0, by rw [h0]; exact isWeightedHomogeneous_zero _ _ _⟩
  · obtain ⟨d0, hd0⟩ := MvPolynomial.support_nonempty.mpr h0
    have key : ∀ c : Fin r, ∀ d, coeff d (rowDiv ℤ a b k y) ≠ 0 →
        ((Finsupp.weight (rowW r r) d c : ℕ) : ℤ) =
          (μ c : ℤ) + k * ((if a = c then 1 else 0) - (if b = c then 1 else 0)) := by
      intro c d hd
      have hyc : IsWeightedHomogeneous (columnWeight c) y (μ c : ℤ) := by
        intro d' hd'
        rw [weight_wc_eq_degree, hy hd']
      have hs := lehw_rowDiv_shift ℤ (columnWeight c) ((if a = c then 1 else 0) - (if b = c then 1 else 0)) a b
        (by
          intro s
          simp only [columnWeight, lgraded_wa]
          split_ifs <;> simp) (μ c : ℤ) k y hyc
      rw [← weight_wc_eq_degree]
      exact hs hd
    refine ⟨Finsupp.weight (rowW r r) d0, fun d hd => ?_⟩
    funext c
    have h1 := key c d hd
    have h2 := key c d0 (mem_support_iff.mp hd0)
    rw [← h2] at h1
    exact_mod_cast h1
end Formalism.CohomologicalDescent.LD
