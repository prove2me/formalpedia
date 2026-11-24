-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.polynomial_b_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:53.510587+00:00
-- url     : https://prove2.me/submissions/f015d6e0-7a93-4675-923d-83dc44c53139

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_weight_letter
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_mkMon_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_monSet_eq

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : PolBRank := by
  intro n N B
  have hcard : ∀ k : ℕ, ((univ : Finset (Fin n)).finsuppAntidiag k).card = (n + k - 1).choose k := by
    intro k
    rw [show n + k - 1 = Fintype.card (Fin n) + k - 1 by simp, ← Sym.card_sym_eq_choose,
      ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquiv
      ({ toFun := fun f => Finsupp.toMultiset f, invFun := fun s => Multiset.toFinsupp s,
         left_inv := fun f => by simp, right_inv := fun s => by simp } : (Fin n →₀ ℕ) ≃ Multiset (Fin n))
      (fun f => by
      simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Equiv.coe_fn_mk,
        Finsupp.card_toMultiset]
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      rfl) : _ ≃ Sym (Fin n) k)
  have hset := monSet_eq n N B
  refine ⟨?_, ?_, ?_⟩
  · rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ mkMon_inj,
      Fintype.card_piFinset,
      Fin.prod_univ_eq_prod_range (fun i => ((univ : Finset (Fin n)).finsuppAntidiag (B i)).card) N]
    exact Finset.prod_congr rfl fun i _ => hcard (B i)
  · rw [hset]
    exact Finset.finite_toSet _
  · intro R _
    apply le_antisymm
    · intro p hp
      unfold polB at hp
      rw [Submodule.mem_iInf] at hp
      rw [p.as_sum]
      refine Submodule.sum_mem _ fun e he => ?_
      have heS : ∀ i, ∑ a, e (i, a) = if i < N then B i else 0 := by
        intro i
        rw [← weight_letter]
        exact ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (hp i))
          (MvPolynomial.mem_support_iff.mp he)
      rw [show MvPolynomial.monomial e (MvPolynomial.coeff e p) =
          MvPolynomial.coeff e p • MvPolynomial.monomial e (1 : R) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_image_of_mem (fun e => MvPolynomial.monomial e (1 : R)) heS))
    · rw [Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have he' : ∀ i, ∑ a, e (i, a) = if i < N then B i else 0 := he
      unfold polB
      rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro i
      rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [weight_letter]
      exact he' i
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
