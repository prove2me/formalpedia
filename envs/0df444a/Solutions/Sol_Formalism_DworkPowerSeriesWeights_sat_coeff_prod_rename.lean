-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_coeff_prod_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:21.200031+00:00
-- url     : https://prove2.me/submissions/e0b52b38-e432-4580-958d-2375d7c39f01

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_glue_apply
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_prod_monomial
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
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R S τ σ : Type} [CommSemiring R] [Fintype S] [DecidableEq S] (e : S → τ → σ)
    (he : ∀ s t v w, e s v = e t w → s = t ∧ v = w) (f : S → MvPolynomial τ R) (m : S → τ →₀ ℕ) :
    coeff (∑ s, (m s).mapDomain (e s)) (∏ s, rename (e s) (f s)) = ∏ s, coeff (m s) (f s) := by
  classical
  have h1 : ∀ s, rename (e s) (f s) =
      ∑ n ∈ (f s).support, monomial (n.mapDomain (e s)) (coeff n (f s)) := by
    intro s
    conv_lhs => rw [← support_sum_monomial_coeff (f s)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => rename_monomial _ _ _
  simp_rw [h1]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [sat_prod_monomial, coeff_monomial]
  have hinj : ∀ N : S → τ →₀ ℕ, (∑ s, (N s).mapDomain (e s)) = (∑ s, (m s).mapDomain (e s)) ↔ N = m := by
    intro N
    constructor
    · intro h
      funext s
      ext v
      have := congrArg (fun x => x (e s v)) h
      simpa only [sat_glue_apply e he] using this
    · rintro rfl; rfl
  simp_rw [hinj]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [Fintype.mem_piFinset] at hm
    push Not at hm
    obtain ⟨s, hs⟩ := hm
    rw [eq_comm]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simpa using hs)
end Formalism.DworkPowerSeriesWeights
