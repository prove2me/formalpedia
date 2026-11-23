-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.thrS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:20.525448+00:00
-- url     : https://prove2.me/submissions/9c6847c0-11a2-46a7-b4a1-44839ac2ab3b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supA_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_N_nonneg

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
theorem _root_.solution (hg : 0 < G.g) (hka : 0 < G.ka) (hC : 0 ≤ C) (hI : 0 < G.lenI) (b s : ℕ) (w : ι) :
    0 ≤ thrS G C de de' T T' l b s w := by
  unfold thrS Sz.lamThreshold
  have h1 := supA_nonneg G de de' T T' l hg hka (b = 1 ∧ s = 1) w
  have h2 := N_nonneg G
  have := Real.pi_pos
  positivity
end Formalism.FourierDecayAlt.P.Jx7
