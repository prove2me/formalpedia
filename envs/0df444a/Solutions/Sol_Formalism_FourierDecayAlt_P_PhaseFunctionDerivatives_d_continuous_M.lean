-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_continuous_M
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:08.479167+00:00
-- url     : https://prove2.me/submissions/0314ed35-2660-4124-b1cc-067dad09ecc4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_d_continuous_red
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_strictUpper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (m : ℕ) (t : ℂ) (x : Fin (m + 1) → ℂ) : Continuous (d_M m t x) := by
  have hred : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) => redOf m (x, q.2)) :=
    (d_continuous_red m x).comp continuous_snd
  have hX : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) => strictUpper (redOf m (x, q.2)).2.2.1) :=
    (G7.continuous_strictUpper _).comp
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hred)))
  have hB : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) => (redOf m (x, q.2)).2.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hred))
  have hρ : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) =>
      (Fin.cons q.1 (redOf m (x, q.2)).2.1 : Fin (m + 1) → ℂ)) := by
    refine continuous_pi fun k => ?_
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using continuous_fst
    · simp only [Fin.cons_succ]
      exact (continuous_apply k).comp (continuous_fst.comp (continuous_snd.comp hred))
  unfold d_M Mcoord
  exact G7.continuous_blk (continuous_const.matrix_mul (continuous_const.add hX))
    (Continuous.matrix_mulVec continuous_const hB) hρ (continuous_fst.comp hred)
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
