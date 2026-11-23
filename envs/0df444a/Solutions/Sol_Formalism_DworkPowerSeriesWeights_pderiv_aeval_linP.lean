-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pderiv_aeval_linP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:29.668321+00:00
-- url     : https://prove2.me/submissions/16142807-53e4-42a1-b929-e14dcdd96da5

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pderiv_linP

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
theorem _root_.solution (A : ι → ι' → K) (i : ι) (G : MvPolynomial ι' K) :
    MvPolynomial.pderiv i (MvPolynomial.aeval (linP A) G) =
      ∑ j, MvPolynomial.C (A i j) * MvPolynomial.aeval (linP A) (MvPolynomial.pderiv j G) := by
  classical
  induction G using MvPolynomial.induction_on
  · simp
  · rename_i p q hp hq
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  · rename_i p j hp
    have hk : ∀ k : ι', MvPolynomial.aeval (linP A) (MvPolynomial.pderiv k (p * MvPolynomial.X j)) =
        MvPolynomial.aeval (linP A) p * (if j = k then 1 else 0) +
          linP A j * MvPolynomial.aeval (linP A) (MvPolynomial.pderiv k p) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
        map_mul, MvPolynomial.aeval_X, Pi.single_apply]
      split_ifs <;> simp
    simp only [hk, mul_add, Finset.sum_add_distrib]
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, pderiv_linP, hp, smul_eq_mul, smul_eq_mul]
    have h1 : ∑ k : ι', MvPolynomial.C (A i k) *
        (MvPolynomial.aeval (linP A) p * (if j = k then 1 else 0)) =
        MvPolynomial.aeval (linP A) p * MvPolynomial.C (A i j) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [if_neg (Ne.symm hk)]; ring)
        (fun h => absurd (Finset.mem_univ j) h), if_pos rfl]
      ring
    rw [h1, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
end Formalism.DworkPowerSeriesWeights
