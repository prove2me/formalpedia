-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.continuous_heis0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:33:21.240826+00:00
-- url     : https://prove2.me/submissions/30b4fe54-e567-45d0-abc0-b433dcb2e5fe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_hb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) : Continuous (heis0 k r') := by
  have hl : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (continuous_lift k r').comp continuous_fst
  have hh : ∀ j, Continuous fun x : HPar k r' => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' x.1) :=
    fun j => (continuous_herm _).comp (continuous_const.prodMk hl)
  have hl' : ∀ p, Continuous fun x : HPar k r' => liftVec k 1 r' x.1 p := fun p => (continuous_apply p).comp hl
  have hb' := continuous_hb k r'
  unfold heis0 heisG
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec, of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
end Formalism.FourierDecayAlt.P.B2x5
