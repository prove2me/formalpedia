-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Kset_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:02:04.869748+00:00
-- url     : https://prove2.me/submissions/5b6ba887-c1dc-4ed5-8b2e-63c209ec6413

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_of_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_measurableSet_posDef
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (ρ : ℝ) : MeasurableSet (Kset P Q ρ) := by
  simp only [Kset, Set.setOf_and]
  have htr : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (Matrix.trace (Matrix.of p.1)).re) :=
    (Complex.continuous_re.comp ((of_cont.comp continuous_fst).matrix_trace)).measurable
  exact (measurable_fst measurableSet_posDef).inter
    ((measurableSet_le htr measurable_const).inter (measurableSet_le qf_meas measurable_const))
end Formalism.FourierDecayAlt.P.HermitianFormFactor
