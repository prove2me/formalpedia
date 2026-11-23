-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.partial_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:03.544104+00:00
-- url     : https://prove2.me/submissions/896d84fe-7aa2-44aa-9f6b-3d2fb330a824

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (M : ℕ) (hM : 3 ≤ M) (n : ℕ) :
    ∑ i ∈ range (n + 1), 1 / ((i : ℝ) + 1) ^ M ≤
      1 + 2 / 2 ^ M - 4 / 2 ^ M * (1 / (((n : ℝ) + 1) * (n + 2))) := by
  induction n with
  | zero =>
    simp
    have : (0 : ℝ) < 2 ^ M := by positivity
    apply le_of_eq
    field_simp
    ring
  | succ n ih =>
    rw [sum_range_succ]
    have h := term_le M (n + 1) hM (by omega)
    push_cast at h ⊢
    have e1 : (n : ℝ) + 1 + 1 + 1 = n + 1 + 2 := by ring
    have e2 : (n : ℝ) + 1 + 1 = n + 2 := by ring
    rw [e2] at h ⊢
    have e3 : (n : ℝ) + 1 + 2 = n + 2 + 1 := by ring
    rw [e3] at h ⊢
    rw [mul_sub] at h
    linarith
end Formalism.FourierDecayAlt.P.Sz2
