-- Prove2me | solution 1 for Bl.HermitianSesquilinear.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:07.12936+00:00
-- url     : https://prove2.me/submissions/06593f62-4801-4f6e-b0af-3a9ec7b0eb29

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.HermitianSesquilinear
private theorem conj_eq_of_nonneg_real {M : Type} [AddCommGroup M] [Module ℂ M] (Ξ : Formalism.FourierDecayAlt.F7.Sesq M)
    (h : ∀ m : M, 0 ≤ (Ξ m m).re ∧ (Ξ m m).im = 0) (x y : M) :
    starRingEnd ℂ (Ξ x y) = Ξ y x := by
  have h1 := (h (x + y)).2
  have h2 := (h (x + Complex.I • y)).2
  have hx := (h x).2
  have hy := (h y).2
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_I, Complex.neg_re,
    Complex.neg_im, RingHom.id_apply] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
end Bl.HermitianSesquilinear
end

set_option autoImplicit false
open Bl Bl.HermitianSesquilinear
namespace Bl.HermitianSesquilinear
theorem _root_.solution :
  ∀ {M : Type} [inst : AddCommGroup.{0} M] [inst_1 : Module.{0, 0} Complex M] (Ξ : Formalism.FourierDecayAlt.F7.Sesq M),
  (∀ (m : M),
      And (LE.le.{0} 0 (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ m) m).re)
        (Eq.{1} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ m) m).im 0)) →
    ∀ (x y : M),
      LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ x) y)) 2)
        (HMul.hMul.{0, 0, 0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ x) x).re
          (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ y) y).re) := by
  intro M _ _ Ξ h x y
  let c : PreInnerProductSpace.Core ℂ M :=
    { inner := fun a b => Ξ b a
      conj_inner_symm := fun a b => conj_eq_of_nonneg_real Ξ h a b
      re_inner_nonneg := fun a => (h a).1
      add_left := fun a b z => map_add (Ξ z) a b
      smul_left := fun a b r => (map_smulₛₗ (Ξ b) r a).trans (smul_eq_mul _ _) }
  have key := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (F := M) y x
  change ‖Ξ x y‖ * ‖Ξ y x‖ ≤ (Ξ y y).re * (Ξ x x).re at key
  rw [← conj_eq_of_nonneg_real Ξ h x y, RCLike.norm_conj] at key
  rw [sq, mul_comm (Ξ x x).re]
  exact key
end Bl.HermitianSesquilinear
