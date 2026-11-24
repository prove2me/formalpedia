-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_initial_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:47.294805+00:00
-- url     : https://prove2.me/submissions/24bf14b6-a1dc-4b45-a89b-befdfb431b53

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_jacobi_complementary_minor
import Theorems.Thm_Formalism_CohomologicalDescent_LD_det_submatrix_eq_or_neg
import Theorems.Thm_Formalism_CohomologicalDescent_LD_injective_extends_to_equiv
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld3Gam_inl
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld3Gam_inr
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_of_variable
import Theorems.Thm_Formalism_GradedWeylDivisibility_algHom_det_of
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem
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
theorem _root_.solution {r s t : ℕ} (h : s + t = r) (I : Fin s → Fin r) (hs : s ≤ r) :
    ∃ g ∈ dualWeyl ℤ r r (initW r t), genericDet ℤ r * cofMap r (initMinor ℤ I hs) = genericDet ℤ r ^ s * g := by
  by_cases hI : Function.Injective I
  · obtain ⟨ρ, hρ⟩ := injective_extends_to_equiv h (fun p => Fin.rev (I p)) (fun p q hpq => hI (Fin.rev_injective hpq))
    have J := jacobi_complementary_minor (genericMatrix' ℤ r) ρ (finSumEquivOfAddEq h)
    have e1 : (Matrix.of fun i j : Fin s =>
        (genericMatrix' ℤ r).adjugate (finSumEquivOfAddEq h (Sum.inl j)) (ρ (Sum.inl i))).det = cofMap r (initMinor ℤ I hs) := by
      unfold initMinor
      rw [algHom_det_of]
      congr 1
      ext i j
      simp only [Matrix.of_apply, cofactor_of_variable, hρ, ld3Gam_inl]
    have e2 : (Matrix.of fun i j : Fin t => genericMatrix' ℤ r (ρ (Sum.inr i)) (finSumEquivOfAddEq h (Sum.inr j))).det =
        initMinor ℤ (fun i => ρ (Sum.inr i)) (by omega : t ≤ r) := by
      unfold initMinor
      refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
      simp only [Matrix.of_apply, ld3Gam_inr, genericMatrix']
    rw [e1, e2, Fintype.card_fin] at J
    change _ = genericDet ℤ r ^ s * _ at J
    rcases det_submatrix_eq_or_neg (genericMatrix' ℤ r) ρ (finSumEquivOfAddEq h) with hd | hd
    · rw [hd] at J
      exact ⟨_, initMinor_mem _ _, J⟩
    · rw [hd] at J
      refine ⟨-_, Submodule.neg_mem _ (initMinor_mem (fun i => ρ (Sum.inr i)) (by omega : t ≤ r)), ?_⟩
      rw [mul_neg, ← J]
      unfold genericDet
      ring
  · simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor ℤ I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero, mul_zero, mul_zero]⟩
end Formalism.CohomologicalDescent.LD
