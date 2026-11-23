-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_monomial_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:34.769789+00:00
-- url     : https://prove2.me/submissions/783fe892-d627-4f1e-a8a6-019b269bf548

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (P : MvPolynomial ι' K) (μ : ι' →₀ ℕ) :
    jetPair P ((MvPolynomial.monomial μ (1 : K) : MvPolynomial ι' K) : MvPowerSeries ι' K) =
      MvPolynomial.coeff μ P * ((mfact μ : ℕ) : K) := by
  classical
  rw [jetPair_eq_sum P _ (insert μ P.support) (Finset.subset_insert _ _), Finset.sum_eq_single μ]
  · simp [MvPolynomial.coeff_coe]
  · intro κ _ hκ
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial, if_neg (Ne.symm hκ), mul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self μ _) h
end Formalism.DworkPowerSeriesWeights
