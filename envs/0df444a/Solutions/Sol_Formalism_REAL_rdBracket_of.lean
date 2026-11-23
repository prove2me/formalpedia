-- Prove2me | solution 1 for Formalism.REAL.rdBracket_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:09.973384+00:00
-- url     : https://prove2.me/submissions/e0ff0a0c-22f8-458b-bacb-dc731fb82847

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty
import Theorems.Thm_Formalism_REAL_lie_algebra_bracket_mem

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
theorem _root_.solution (h : RdExt) (hs : RdSmooth) : RdBracket := by
  intro n ε f X Y g hf hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → Rd Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => h n ε f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : Rd X (Rd Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    h n ε (Rd Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : Rd Y (Rd X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    h n ε (Rd X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g := hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _
end Formalism.REAL
