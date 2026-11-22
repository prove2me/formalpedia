-- Prove2me | solution 1 for Formalism.REAL.rdSmooth_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:05.500766+00:00
-- url     : https://prove2.me/submissions/a996512e-a417-43b7-a0f8-da573379e16c

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (h : RdExt) : RdSmooth := by
  intro n ε f X hf hX g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkJ
    exact h n ε f F U k X hU hk hkJ hF hfF hX
end Formalism.REAL
