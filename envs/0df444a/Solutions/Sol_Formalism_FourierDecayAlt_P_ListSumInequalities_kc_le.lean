-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.kc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:57:56.038348+00:00
-- url     : https://prove2.me/submissions/06fbe216-8a56-4673-9716-b25df245a28a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution {X : Mat k r} (hX : unitLie k r X) (i : J k r) : |kc i X| ≤ Kc k r := by
  have hco : |co X i| ≤ 1 := by
    unfold co
    split_ifs
    · exact (Complex.abs_im_le_norm _).trans (hX.2 _ _)
    · exact (Complex.abs_re_le_norm _).trans (hX.2 _ _)
  rw [kc, abs_mul, abs_norm]
  calc |co X i| * ‖prj (Eb i)‖ ≤ 1 * ‖prj (Eb i)‖ := mul_le_mul_of_nonneg_right hco (norm_nonneg _)
    _ = ‖prj (Eb i)‖ := one_mul _
    _ ≤ ∑ j : J k r, ‖prj (Eb j)‖ :=
        Finset.single_le_sum (f := fun j => ‖prj (Eb j)‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ Kc k r := le_add_of_nonneg_left zero_le_one
end Formalism.FourierDecayAlt.P.ListSumInequalities
