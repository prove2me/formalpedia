-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.exists_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:05.682036+00:00
-- url     : https://prove2.me/submissions/37aaae94-3048-4c5b-a1ee-5ebbb9c41dd7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_compL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ≠ 0) :
    ∃ β : Fin r → ℤ, cw p K β x ≠ 0 ∧ (∀ γ, phiW β < phiW γ → cw p K γ x = 0) ∧ ∃ m ∈ x.support, wp K m = β := by
  classical
  obtain ⟨β, hβ, hmax⟩ := Finset.exists_max_image (x.support.image (wp K)) phiW
    ((support_nonempty.mpr hx).image _)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hβ
  refine ⟨wp K m, ?_, ?_, m, hm, rfl⟩
  · intro h0
    have := congrArg (coeff m) h0
    rw [cw, coeff_compL, if_pos rfl, coeff_zero] at this
    exact (mem_support_iff.mp hm) this
  · intro γ hγ
    ext m'
    rw [cw, coeff_compL, coeff_zero]
    split_ifs with h
    · by_contra hc
      have := hmax γ (Finset.mem_image.mpr ⟨m', mem_support_iff.mpr hc, h⟩)
      omega
    · rfl
end Formalism.InvariantFactorPaths.L4
