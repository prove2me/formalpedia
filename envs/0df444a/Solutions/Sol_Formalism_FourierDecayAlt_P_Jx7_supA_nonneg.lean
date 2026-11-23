-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.supA_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:26.656882+00:00
-- url     : https://prove2.me/submissions/79f1e328-5c7c-4f76-94b3-f5db18c7eff3

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_sp_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supA_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution (hg : 0 < G.g) (hka : 0 < G.ka) (p : Prop) [Decidable p] (w : ι) :
    0 ≤ supA G de de' T T' l (decide p) w := by
  have h := sp_nonneg G de de' T T' l hg.le hka.le p w
  rw [← supA_mul G de de' T T' l hg hka p w] at h
  have hc : 0 < G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹ := by positivity
  rw [← mul_assoc] at h
  exact nonneg_of_mul_nonneg_right h hc
end Formalism.FourierDecayAlt.P.Jx7
