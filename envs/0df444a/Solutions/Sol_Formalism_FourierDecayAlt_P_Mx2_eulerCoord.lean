-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.eulerCoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:11.211524+00:00
-- url     : https://prove2.me/submissions/71d3d18d-dd5f-4e6e-bb27-8ffcee662013

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution : EulerCoord := by
  intro r v w z
  constructor
  · ext γ
    simp only [euler, coord, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases h : γ = toLex (Pi.single w (1 : ℤ))
    · subst h
      by_cases hv : v = w
      · subst hv; simp
      · simp [hv, Pi.single_apply]
    · split_ifs <;> simp [HahnSeries.coeff_single_of_ne h]
  · ext γ
    simp only [euler, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.algebraMap_apply]
    by_cases h : γ = 0
    · subst h; simp; left; rfl
    · simp [HahnSeries.coeff_single_of_ne h]
end Formalism.FourierDecayAlt.P.Mx2
