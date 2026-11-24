-- Prove2me | solution 1 for Formalism.HN.HeightGram.factor_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:17.030222+00:00
-- url     : https://prove2.me/submissions/fb2c69fe-e51d-4799-88be-84ee96cf5c31

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
namespace Formalism.HN.HeightGram
theorem _root_.solution (f j : ℕ) {D : ℝ} (hD : 0 < D) :
    (2 : ℝ) ^ (f * j) * D ^ (-(j : ℝ) / 2) * (((2 : ℝ)⁻¹) ^ f * √D) ^ j = 1 := by
  have h1 : (√D) ^ j = D ^ ((j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    ring
  have h2 : D ^ (-(j : ℝ) / 2) * D ^ ((j : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hD, neg_div, neg_add_cancel, Real.rpow_zero]
  rw [mul_pow, h1, ← pow_mul, inv_pow]
  have h3 : (2 : ℝ) ^ (f * j) ≠ 0 := by positivity
  calc _ = ((2 : ℝ) ^ (f * j) * ((2 : ℝ) ^ (f * j))⁻¹) * (D ^ (-(j : ℝ) / 2) * D ^ ((j : ℝ) / 2)) := by
        ring
    _ = 1 := by rw [mul_inv_cancel₀ h3, h2, one_mul]
end Formalism.HN.HeightGram
