-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx9.far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:45.926264+00:00
-- url     : https://prove2.me/submissions/9df7839e-48ca-48a1-b4e2-d516e69dee71

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9
namespace Formalism.FourierDecayAlt.P.Mx9
theorem _root_.solution {z z' : ℂ} (h : 2 < |z.re - z'.re|) (n : ℤ) (hn : |n| ≤ 2) : z - z' ≠ (n : ℂ) := by
  intro heq
  have h1 := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.intCast_re] at h1
  rw [h1] at h
  have h2 : ((|n| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hn
  rw [Int.cast_abs] at h2
  linarith
end Formalism.FourierDecayAlt.P.Mx9
