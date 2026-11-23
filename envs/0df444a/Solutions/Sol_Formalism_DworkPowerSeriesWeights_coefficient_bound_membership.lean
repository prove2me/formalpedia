-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.coefficient_bound_membership
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:31.285591+00:00
-- url     : https://prove2.me/submissions/49634ca6-43fc-41bd-b023-99d24a61eaf6

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_expand
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_exists_monomial_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds
private lemma coeff_sum_mem_lemma {K : Type} [Field K] {σ ι α : Type}
    (M : Submodule K (MvPolynomial σ K)) (S : Finset α) (f : α → MvPolynomial ι (MvPolynomial σ K))
    (hf : ∀ A ∈ S, ∃ e Q, Q ∈ M ∧ f A = MvPolynomial.monomial e Q) (κ : ι →₀ ℕ) :
    MvPolynomial.coeff κ (∑ A ∈ S, f A) ∈ M := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Submodule.sum_mem _ fun A hA => ?_
  obtain ⟨e, Q, hQ, hfA⟩ := hf A hA
  rw [hfA, MvPolynomial.coeff_monomial]
  split_ifs
  · exact hQ
  · exact Submodule.zero_mem _
private lemma jetPairPoly_mem_lemma_2 {K : Type} [Field K] {σ ι : Type}
    (M : Submodule K (MvPolynomial σ K)) (P : MvPolynomial ι (MvPolynomial σ K))
    (Th : MvPowerSeries ι K) (hP : ∀ κ, MvPolynomial.coeff κ P ∈ M) :
    jetPairPoly P Th ∈ M := by
  unfold jetPairPoly
  refine Submodule.sum_mem _ fun κ _ => ?_
  rw [mul_comm (MvPolynomial.coeff κ P), ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hP κ)
private lemma prod_mul_C_lemma_3 {K : Type} [Field K] {σ ι α : Type}
    (M : Submodule K (MvPolynomial σ K)) (s : Finset α) (f : α → MvPolynomial ι (MvPolynomial σ K))
    (Q : MvPolynomial σ K) (hf : ∀ a ∈ s, ∃ e, f a = MvPolynomial.monomial e 1) (hQ : Q ∈ M) :
    ∃ e Q', Q' ∈ M ∧ (∏ a ∈ s, f a) * MvPolynomial.C Q = MvPolynomial.monomial e Q' := by
  obtain ⟨e, he⟩ := exists_monomial_prod s f hf
  exact ⟨e, Q, hQ, by rw [he, mul_comm, MvPolynomial.C_mul_monomial, mul_one]⟩
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : CBMem := by
  unfold CBMem
  intro K _ d N0 N1 _ colN p hp I Th
  unfold frameJet nablaK
  refine jetPairPoly_mem_lemma_2 _ _ _ fun κ => ?_
  simp only [minorProd_expand]
  rw [Finset.prod_univ_sum]
  refine coeff_sum_mem_lemma _ _ _ (fun A _ => ?_) κ
  rw [Finset.prod_mul_distrib, ← map_prod]
  refine prod_mul_C_lemma_3 _ _ _ _ (fun s _ => ?_) ?_
  · exact exists_monomial_prod _ _ fun c _ => exists_monomial_prod _ _ fun r' _ => ⟨_, rfl⟩
  · refine Submodule.subset_span ?_
    simp only [xMinors, Set.mem_setOf_eq]
    exact ⟨A, rfl⟩
end Formalism.DworkPowerSeriesWeights
