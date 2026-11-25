-- Prove2me | solution 1 for Formalism.DegreeFormula.flagDegFormula_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:36.25438+00:00
-- url     : https://prove2.me/submissions/277b6046-9876-4b1e-a843-247ca94639d8

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_coeff_pow
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_vandermonde_sum
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_pairs_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open PFlagDeg
namespace Formalism.DegreeFormula
theorem _root_.solution : FlagDegFormula := by
  unfold FlagDegFormula
  intro ι _ _ N lam
  unfold flagDeg degFl weylProd
  simp only [coeff_pow]
  have hV : ∀ τ, ∏ i : Fin N, ∏ k : Fin N,
      (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) =
        (∏ i : Fin N, ∏ k : Fin N, if i < k then lam τ i - lam τ k else 1) / (sfac N : ℝ) := by
    intro τ
    rw [← pairs_nat N, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hsum : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) =
      ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then lam τ i - lam τ k else 1) := by
    rw [Finset.prod_congr rfl (fun τ _ => (vandermonde_sum (lam τ)).symm), Fintype.prod_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
  have hsq : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [hV, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [← hsum, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  linear_combination ((∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
    (((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι)) *
      ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) * hsq
end Formalism.DegreeFormula
