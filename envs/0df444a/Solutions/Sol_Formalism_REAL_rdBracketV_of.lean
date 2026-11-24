-- Prove2me | solution 1 for Formalism.REAL.rdBracketV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:09.075674+00:00
-- url     : https://prove2.me/submissions/73fbbd15-6ad4-40a4-b9bc-9cc478c1591b

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma inG_commutator' {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X * Y - Y * X) := by
  unfold inG at *
  have key : (X * Y - Y * X)ᴴ * Jm e + Jm e * (X * Y - Y * X) =
      Yᴴ * (Xᴴ * Jm e + Jm e * X) - (Yᴴ * Jm e + Jm e * Y) * X - Xᴴ * (Yᴴ * Jm e + Jm e * Y) +
        (Xᴴ * Jm e + Jm e * X) * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [key, hX, hY]
  simp
section EabGl
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end EabGl
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (h : RdExtV) (_hs : RdSmoothV) : RdBracketV := by
  intro n ε E _ _ f X Y g hf hX hY hg
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hF1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  let LX : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
  let LY : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ Y)
  have hGX : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y (y * X)) U :=
    hF1.clm_apply (LX.contDiff.contDiffOn)
  have hGY : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y (y * Y)) U :=
    hF1.clm_apply (LY.contDiff.contDiffOn)
  have eY : RdV X (RdV Y f) g = fderiv ℝ (fun y => fderiv ℝ F y (y * Y)) g (g * X) :=
    h n ε E (RdV Y f) (fun y => fderiv ℝ F y (y * Y)) U g X hU hgU hg hGY
      (fun x hx hxJ => h n ε E f F U x Y hU hx hxJ hF hfF hY) hX
  have eX : RdV Y (RdV X f) g = fderiv ℝ (fun y => fderiv ℝ F y (y * X)) g (g * Y) :=
    h n ε E (RdV X f) (fun y => fderiv ℝ F y (y * X)) U g Y hU hgU hg hGX
      (fun x hx hxJ => h n ε E f F U x X hU hx hxJ hF hfF hX) hY
  have eXY : RdV (X * Y - Y * X) f g = fderiv ℝ F g (g * (X * Y - Y * X)) :=
    h n ε E f F U g _ hU hgU hg hF hfF (inG_commutator' hX hY)
  have hFd2 : DifferentiableAt ℝ (fun y => fderiv ℝ F y) g :=
    (hF1.differentiableOn (by simp) g hgU).differentiableAt (hU.mem_nhds hgU)
  have hev : ∀ᶠ y in 𝓝 g, HasFDerivAt F (fderiv ℝ F y) y :=
    Filter.eventually_of_mem (hU.mem_nhds hgU) fun y hy =>
      ((hF.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hsymm := second_derivative_symmetric_of_eventually hev hFd2.hasFDerivAt (g * X) (g * Y)
  have hhY : HasFDerivAt (fun y => fderiv ℝ F y (y * Y)) _ g :=
    hFd2.hasFDerivAt.clm_apply LY.hasFDerivAt
  have hhX : HasFDerivAt (fun y => fderiv ℝ F y (y * X)) _ g :=
    hFd2.hasFDerivAt.clm_apply LX.hasFDerivAt
  have dY : fderiv ℝ (fun y => fderiv ℝ F y (y * Y)) g (g * X) =
      fderiv ℝ F g (g * X * Y) + fderiv ℝ (fun y => fderiv ℝ F y) g (g * X) (g * Y) := by
    rw [hhY.fderiv]
    rfl
  have dX : fderiv ℝ (fun y => fderiv ℝ F y (y * X)) g (g * Y) =
      fderiv ℝ F g (g * Y * X) + fderiv ℝ (fun y => fderiv ℝ F y) g (g * Y) (g * X) := by
    rw [hhX.fderiv]
    rfl
  have hsymm' : fderiv ℝ (fun y => fderiv ℝ F y) g (g * X) (g * Y) =
      fderiv ℝ (fun y => fderiv ℝ F y) g (g * Y) (g * X) := hsymm
  rw [eY, eX, eXY, dY, dX, hsymm', Matrix.mul_sub, map_sub, Matrix.mul_assoc g X Y,
    Matrix.mul_assoc g Y X]
  abel
end Formalism.REAL
