-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.rd_ld_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:38.260735+00:00
-- url     : https://prove2.me/submissions/a7d7da01-2c76-49f9-af28-d0edf0878850

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_l_hasDeriv_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hasDeriv_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {f : Mx k r → E} (hf : SmoothLev k r i D f) {X Y g : Mx k r} (hX : inLieLev k r i X)
    (hY : inLieLev k r i Y) (hg : g ∈ Glev k r i ∩ D) :
    RdV Y (LdV X f) g = LdV X (RdV Y f) g := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  have hdF : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have h1 := hF.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) g := (h1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have eL : ∀ x ∈ U, x ∈ Glev k r i → LdV X f x = fderiv ℝ F x (mulL X x) := fun x hx hxG =>
    (l_hasDeriv_ext hU hx hxG hX (hdF x hx) he).deriv
  have eR : ∀ x ∈ U, x ∈ Glev k r i → RdV Y f x = fderiv ℝ F x (mulRightRealCLM Y x) := fun x hx hxG =>
    (Qx2.hasDeriv_ext hU hx hxG hY (hdF x hx) he).deriv
  have HL := hd.hasFDerivAt.clm_apply (mulL X).hasFDerivAt
  have HR := hd.hasFDerivAt.clm_apply (mulRightRealCLM Y).hasFDerivAt
  have a1 : RdV Y (LdV X f) g = fderiv ℝ (fun x => fderiv ℝ F x (mulL X x)) g (g * Y) :=
    (Qx2.hasDeriv_ext hU hgU hg.1 hY HL.differentiableAt eL).deriv
  have a2 : LdV X (RdV Y f) g = fderiv ℝ (fun x => fderiv ℝ F x (mulRightRealCLM Y x)) g (X * g) :=
    (l_hasDeriv_ext hU hgU hg.1 hX HR.differentiableAt eR).deriv
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    (hF.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have b1 := DFunLike.congr_fun HL.fderiv (g * Y)
  have b2 := DFunLike.congr_fun HR.fderiv (X * g)
  refine a1.trans (b1.trans (Eq.trans ?_ (a2.trans b2).symm))
  have h3 := hsym (g * Y) (X * g)
  show fderiv ℝ F g (X * (g * Y)) + fderiv ℝ (fderiv ℝ F) g (g * Y) (X * g) =
    fderiv ℝ F g (X * g * Y) + fderiv ℝ (fderiv ℝ F) g (X * g) (g * Y)
  rw [Matrix.mul_assoc]
  exact congrArg (fun e => fderiv ℝ F g (X * (g * Y)) + e) h3
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
