-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:21:21.8412+00:00
-- url     : https://prove2.me/submissions/e1ba129c-8db1-4637-a94c-134012d618f7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hasDerivAt_of_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ Φ' : Mat k r → E} {U : Set (Mat k r)} {m : ℕ∞} (hm : 1 ≤ m) (hU : IsOpen U)
    {g X : Mat k r} (hgU : g ∈ U) (hgG : g ∈ GV k r) (hc : ContDiffOn ℝ (m : WithTop ℕ∞) Φ' U)
    (he : ∀ x ∈ U, x ∈ GV k r → Φ x = Φ' x) (hX : inLie k r X) :
    RdV X Φ g = fderiv ℝ Φ' g (g * X) := by
  have hd : DifferentiableAt ℝ Φ' g :=
    (hc.differentiableOn (by
      have : m ≠ 0 := by rintro rfl; simp at hm
      exact_mod_cast this)).differentiableAt (hU.mem_nhds hgU)
  exact (hasDerivAt_of_ext hU hgU hgG hX hd he).deriv
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
