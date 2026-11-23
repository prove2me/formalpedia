-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.integral_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:49.635805+00:00
-- url     : https://prove2.me/submissions/2f87d7f5-8577-4e18-8f56-0067d66329ab

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_fixed_unique
import Theorems.Thm_Formalism_ELL_wSeriesExistsUnique_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsParam
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) : IntegralPS w := by
  let W' : WeierstrassCurve (unitBall K) :=
    ⟨⟨W.a₁, hW.1⟩, ⟨W.a₂, hW.2.1⟩, ⟨W.a₃, hW.2.2.1⟩, ⟨W.a₄, hW.2.2.2.1⟩, ⟨W.a₆, hW.2.2.2.2⟩⟩
  obtain ⟨v, hv, -⟩ := wSeriesExistsUnique_holds.{u} (unitBall K) W'
  have hmap : WFixed W (PowerSeries.map (unitBall K).subtype v) := by
    refine ⟨?_, ?_⟩
    · have h := hv.1
      have : constantCoeff (PowerSeries.map (unitBall K).subtype v)
          = (unitBall K).subtype (constantCoeff v) := by
        rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
      rw [this, h, map_zero]
    · have h := congrArg (PowerSeries.map (unitBall K).subtype) hv.2
      simp only [map_add, map_mul, map_pow, map_X, map_C] at h
      exact h
  have he : w = PowerSeries.map (unitBall K).subtype v := WeierstrassSeriesLimit.fixed_unique W hw hmap
  intro n
  rw [he, coeff_map]
  exact (coeff n v).2
end Formalism.ELL.FormalGroupPointsParam
