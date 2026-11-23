-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.gramRealise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:06.069815+00:00
-- url     : https://prove2.me/submissions/060b553e-bed4-4104-afeb-e1010f1da5cc

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
theorem _root_.solution : GramRealise := by
  intro ι _ _ kap hk
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hk.nonneg
  refine ⟨Fintype.card ι, fun h k => star (B ((Fintype.equivFin ι).symm k) h), fun h h' => ?_⟩
  rw [hB, Matrix.mul_apply]
  refine Fintype.sum_equiv (Fintype.equivFin ι) _ _ fun i => ?_
  show star B h i * B i h' = star (B ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i)) h) *
    starRingEnd ℂ (star (B ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i)) h'))
  rw [Equiv.symm_apply_apply, Matrix.star_apply, starRingEnd_apply, star_star]
end Formalism.FourierDecayAlt.P.GramProductIdentities
