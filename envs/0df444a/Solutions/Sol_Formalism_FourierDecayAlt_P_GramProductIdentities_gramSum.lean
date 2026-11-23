-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.gramSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:25.046028+00:00
-- url     : https://prove2.me/submissions/c7835483-b5d0-4cf6-b272-995fd25099c9

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : GramSum := by
  intro M _ _ R ι _ d io X X'
  symm
  calc ∑ k, R (∑ h, io h k • X h) (∑ h, io h k • X' h)
      = ∑ k, ∑ h, ∑ h', io h k * starRingEnd ℂ (io h' k) * R (X h) (X' h') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have e1 : ∀ (u : M), R (∑ h, io h k • X h) u = ∑ h, io h k * R (X h) u := by
          intro u; rw [map_sum R, LinearMap.sum_apply]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        have e2 : ∀ (u : M), R u (∑ h', io h' k • X' h') =
            ∑ h', starRingEnd ℂ (io h' k) * R u (X' h') := by
          intro u; rw [map_sum (R u)]; simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
        rw [e1]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [e2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h' _ => ?_
        ring
    _ = ∑ h, ∑ k, ∑ h', io h k * starRingEnd ℂ (io h' k) * R (X h) (X' h') := Finset.sum_comm
    _ = ∑ h, ∑ h', ∑ k, io h k * starRingEnd ℂ (io h' k) * R (X h) (X' h') :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul]
end Formalism.FourierDecayAlt.P.GramProductIdentities
