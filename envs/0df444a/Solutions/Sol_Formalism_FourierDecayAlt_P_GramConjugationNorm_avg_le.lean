-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramConjugationNorm.avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:31.146828+00:00
-- url     : https://prove2.me/submissions/c75c8461-0709-4588-a083-20d643055245

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_prob_le_wsup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {W : Type} [Fintype W]
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
theorem _root_.solution {ι : Type} (R : Finset ι) (len : W → ℕ) (B : ℕ) (th : W → ℝ)
    (hth : IsProb len B th) (g : ι → W → ℝ) (S : W → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ w', ∑ t0 ∈ R, g t0 w' ≤ c * S w') :
    ∑ t0 ∈ R, ∑ w', th w' * g t0 w' ≤ c * wsup len B S := by
  calc ∑ t0 ∈ R, ∑ w', th w' * g t0 w' = ∑ w', th w' * ∑ t0 ∈ R, g t0 w' := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w' _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ w', th w' * (c * S w') :=
        Finset.sum_le_sum fun w' _ => mul_le_mul_of_nonneg_left (hdom w') (hth.1 w')
    _ = c * ∑ w', th w' * S w' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w' _ => by ring
    _ ≤ c * wsup len B S := mul_le_mul_of_nonneg_left (prob_le_wsup len B th hth S) hc
end Formalism.FourierDecayAlt.P.GramConjugationNorm
