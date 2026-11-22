-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.intPol_iff_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:37.289641+00:00
-- url     : https://prove2.me/submissions/8a236d44-eb7f-4f58-aa75-b8c216d1979d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul

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
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  classical
  have hrange : x ∈ IntPol p σ ↔ x ∈ Set.range (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])) := by
    rw [IntPol, LinearMap.mem_range, Set.mem_range]
    rfl
  rw [hrange, MvPolynomial.mem_range_map_iff_coeffs_subset]
  constructor
  · intro h m
    by_cases hm : x.coeff m = 0
    · rw [hm, norm_zero]
      exact zero_le_one
    · obtain ⟨c, hc⟩ := h (MvPolynomial.coeff_mem_coeffs m hm)
      rw [← hc]
      exact c.2
  · intro h c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact ⟨⟨x.coeff m, h m⟩, rfl⟩
end Formalism.InvariantFactorPaths.L4
