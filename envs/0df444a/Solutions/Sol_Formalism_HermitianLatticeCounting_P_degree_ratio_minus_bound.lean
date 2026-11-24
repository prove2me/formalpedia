-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.degree_ratio_minus_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:34.518604+00:00
-- url     : https://prove2.me/submissions/864add45-4c4d-451e-86a6-1d3f1f71c40c

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_QuantumDeterminants_fdegRatio


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.DegRatioMinus := by
  intro n μ s hμ hint hinj
  have hadd : (μ - Pi.single s 1) + Pi.single s 1 = μ := sub_add_cancel _ _
  have hint' : ∀ a b, ∃ m : ℤ, (μ - Pi.single s 1 : Fin n → ℝ) a - (μ - Pi.single s 1 : Fin n → ℝ) b = (m : ℝ) := by
    intro a b
    obtain ⟨m, hm⟩ := hint a b
    by_cases ha : a = s <;> by_cases hb : b = s
    · refine ⟨m, ?_⟩; subst ha; subst hb; simp only [Pi.sub_apply]; linarith
    · refine ⟨m - 1, ?_⟩
      rw [ha] at hm
      simp only [Pi.sub_apply, Pi.single_apply, ha, hb, if_true, if_false]; push_cast; linarith
    · refine ⟨m + 1, ?_⟩
      rw [hb] at hm
      simp only [Pi.sub_apply, Pi.single_apply, ha, hb, if_true, if_false]; push_cast; linarith
    · refine ⟨m, ?_⟩
      simp only [Pi.sub_apply, Pi.single_apply, ha, hb, if_false]; linarith
  have h := Formalism.QuantumDeterminants.fdegRatio n (μ - Pi.single s 1) s hinj hint' (by rw [hadd]; exact hμ)
  rw [hadd] at h
  rw [← inv_div, h, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro s' hs'
  have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
  rw [inv_div]
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hne, if_false]
  congr 1 <;> ring
end Formalism.HermitianLatticeCounting.P
