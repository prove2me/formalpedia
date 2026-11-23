-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_OutsideOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:56.205073+00:00
-- url     : https://prove2.me/submissions/37741259-5c3b-4570-8474-ea64e14fcb11

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_ones_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_zero_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : OutsideOk := by
  intro E α _ L F
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t t' h
    have : t ∈ L ↔ t' ∈ L := by
      constructor
      · intro ht; have := L.sub_mem ht h; simpa using this
      · intro ht; have := L.add_mem h ht; simpa using this
    simp [this]
  · intro t
    by_cases h : t ∈ L
    · simpa [h] using ones_psd F
    · simpa [h] using zero_psd F
  · intro R hR
    have hcard : (R.filter (fun t => t ∈ L)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact hR a ha.1 b hb.1 (L.sub_mem ha.2 hb.2)
    have hsum : (∑ t ∈ R, if t ∈ L then (1 : ℂ) else 0) = ((R.filter (fun t => t ∈ L)).card : ℂ) := by
      rw [Finset.sum_ite]; simp
    rw [hsum]
    interval_cases hc : (R.filter (fun t => t ∈ L)).card
    · simpa using ones_psd F
    · simpa using zero_psd F
end Formalism.FourierDecayAlt.P.Jx8
