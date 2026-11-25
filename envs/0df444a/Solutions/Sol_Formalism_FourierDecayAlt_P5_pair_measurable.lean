-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pair_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:03.677406+00:00
-- url     : https://prove2.me/submissions/e5dd377e-ede6-41a0-83fb-6183e7215186

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableOfContinuousOnZero
import Theorems.Thm_Formalism_FourierDecayAlt_P5_measurable_of_continuousOn_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P5_radSp_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P5_radSp_zero_off
import Theorems.Thm_Formalism_FourierDecayAlt_P5_glueMap_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P5_measurableSet_glueMap_DomR
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_inner_basis_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r 0 × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMap (k := k) c) (glueMap (k := k) c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMap_continuous c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMap_continuous c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMap_DomR c)
    ((P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, P.B6.hilbert_schmidt_inner_basis_sum]
  simp
end Formalism.FourierDecayAlt.P5
