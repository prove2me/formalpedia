-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.X_mul_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:03.30978+00:00
-- url     : https://prove2.me/submissions/e5f257df-9f5e-418b-a7a0-95d3cc3c7e5e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_intPol_iff_norm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (a : MvPolynomial σ ℚ_[p]) : X v * a ∈ IntPol p σ ↔ a ∈ IntPol p σ := by
  classical
  rw [intPol_iff_norm, intPol_iff_norm]
  constructor
  · intro h m
    have h1 := h (m + Finsupp.single v 1)
    rwa [MvPolynomial.coeff_X_mul', if_pos (by simp), add_tsub_cancel_right] at h1
  · intro h m
    rw [MvPolynomial.coeff_X_mul']
    split_ifs
    · exact h _
    · rw [norm_zero]
      exact zero_le_one
end Formalism.InvariantFactorPaths.L4
