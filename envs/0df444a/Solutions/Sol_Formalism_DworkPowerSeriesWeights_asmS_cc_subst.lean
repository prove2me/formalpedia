-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmS_cc_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:22.461628+00:00
-- url     : https://prove2.me/submissions/3a0ddfc1-2eba-44ec-aea9-00c49e954409

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero

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
open Formalism.IncomingBounds MvPowerSeries
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) (a : ZMod d → MvPowerSeries (V2 d) K)
    (ha : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a be) = 0 := by
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [constantCoeff_subst ha']
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [coeff_zero_eq_constantCoeff_apply, hbe0, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hp : constantCoeff (n.prod fun s e => a s ^ e) = 0 := by
      simp only [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      rw [map_pow, ha s, zero_pow hs]
    rw [hp, smul_zero]
end Formalism.DworkPowerSeriesWeights
