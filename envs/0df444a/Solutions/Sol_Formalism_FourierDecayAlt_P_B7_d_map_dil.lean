-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_map_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:33:10.262921+00:00
-- url     : https://prove2.me/submissions/7fd1692c-7486-4497-863b-842d9ca5c964

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_sf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hJ : DilJac D) (t : ℝ × ℝ) (h1 : 0 < t.1) (h2 : 0 < t.2) :
    D.μSS.map (d_dilE t h1.ne' h2.ne') =
      (ENNReal.ofReal ((t.1 ^ kap k r)⁻¹) * ENNReal.ofReal ((t.2 ^ kap k r)⁻¹)) • D.μSS := by
  have := d_sf D.haarW
  have := d_sf D.haarW'
  have := d_sf D.haarN
  have e : ⇑(d_dilE (k := k) (r := r) t h1.ne' h2.ne') =
      Prod.map (Prod.map id (conjM (aDil k r t.1))) (Prod.map id (conjM (aDil k r t.2))) := rfl
  have m1 : Measurable (conjM (aDil k r t.1)) := (BesselUnitaryEquiv.continuous_conjM _).measurable
  have m2 : Measurable (conjM (aDil k r t.2)) := (BesselUnitaryEquiv.continuous_conjM _).measurable
  rw [e]
  unfold RealPlaceData.μSS
  rw [← Measure.map_prod_map _ _ (measurable_id.prodMap m1) (measurable_id.prodMap m2),
    ← Measure.map_prod_map _ _ measurable_id m1, ← Measure.map_prod_map _ _ measurable_id m2,
    hJ t.1 h1, hJ t.2 h2, Measure.map_id, Measure.map_id, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, smul_smul,
    mul_comm (ENNReal.ofReal ((t.2 ^ kap k r)⁻¹))]
end Formalism.FourierDecayAlt.P.B7
