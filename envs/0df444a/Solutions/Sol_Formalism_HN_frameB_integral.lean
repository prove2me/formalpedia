-- Prove2me | solution 1 for Formalism.HN.frameB_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:24.076935+00:00
-- url     : https://prove2.me/submissions/f02927a4-f28c-441e-a2dd-0e9e9df10c2b

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrame
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (u HH : ℝ) (hu : 0 < u) (hH : 0 ≤ HH) :
    ∫ τ in (0:ℝ)..HH, 4 * (u / (u + τ)) = 4 * u * Real.log (1 + HH / u) := by
  have h1 : ∫ τ in (0:ℝ)..HH, (u + τ)⁻¹ = Real.log ((u + HH) / u) := by
    have := intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a := 0) (b := HH) u
    rw [this, integral_inv_of_pos (by linarith) (by linarith)]
    simp
  have h2 : (1 + HH / u) = (u + HH) / u := by field_simp
  rw [h2, ← h1, ← intervalIntegral.integral_const_mul]
  congr 1; ext τ; ring
end Formalism.HN
