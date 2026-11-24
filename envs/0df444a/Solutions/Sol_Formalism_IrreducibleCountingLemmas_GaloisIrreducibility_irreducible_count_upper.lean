-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.irreducible_count_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:36.589316+00:00
-- url     : https://prove2.me/submissions/93f4b57e-d390-493c-9463-5136e2642f63

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : IrredCountUpper := by
  intro K _ _ d hd
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hd0 : d ≠ 0 := by omega
  have hdvd : ∀ f : K[X], Irreducible f → f.natDegree = d → f ∣ X ^ (Fintype.card K ^ d) - X := by
    intro f hf hfd
    haveI := Fact.mk hf
    haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ d := by
      rw [Module.card_fintype (AdjoinRoot.powerBasis hf.ne_zero).basis, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, hfd]
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card,
      sub_self]
  have main : ∀ S : Finset (Fin d → K), (∀ c ∈ S, Irreducible (monicOf c)) →
      d * S.card ≤ Fintype.card K ^ d := by
    intro S hS
    have hcop : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → IsCoprime (monicOf c) (monicOf c') := by
      intro c hc c' hc' hne
      rw [(hS c hc).coprime_iff_not_dvd]
      intro hdv
      apply hne
      apply monicOf_injective
      exact eq_of_monic_of_associated (monicOf_monic c) (monicOf_monic c')
        ((hS c hc).associated_of_dvd (hS c' hc') hdv)
    have hprod : ∏ c ∈ S, monicOf c ∣ X ^ (Fintype.card K ^ d) - X :=
      Finset.prod_dvd_of_coprime (fun c hc c' hc' hne => hcop c hc c' hc' hne)
        (fun c hc => hdvd _ (hS c hc) (monicOf_natDegree c))
    have hdeg : (∏ c ∈ S, monicOf c).natDegree = d * S.card := by
      rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c),
        Finset.sum_congr rfl (fun c _ => monicOf_natDegree c), Finset.sum_const, smul_eq_mul, mul_comm]
    have hle := natDegree_le_of_dvd hprod (FiniteField.X_pow_card_pow_sub_X_ne_zero K hd0 hq1)
    rw [hdeg, FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd0 hq1] at hle
    exact hle
  exact main _ (fun c hc => (Finset.mem_filter.mp hc).2)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
