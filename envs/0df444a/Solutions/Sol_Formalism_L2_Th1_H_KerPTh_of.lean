-- Prove2me | solution 1 for Formalism.L2.Th1.H.KerPTh_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:05.983174+00:00
-- url     : https://prove2.me/submissions/17fed9c3-3fe5-4766-9d98-cafed32191ae

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_term_eq
import Theorems.Thm_Formalism_L2_Th1_H_kernel_summable_bound
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergMul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (hE : ExpSeriesEntire) (hS : LatGaussSummable) (hN : FormNorm) : KerPTh := by
  unfold KerPTh
  intro V _ _ _ H Λ α hH hP hL hα w
  refine ⟨fun z => ?_, ?_⟩
  · have hb := kernel_summable_bound hS hN H Λ α hH hP hL hα w ‖z‖
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hb)
    rw [term_eq, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    calc (kL H w x z).re ≤ ‖kL H w x z‖ := Complex.re_le_norm _
      _ ≤ ‖kL H w x‖ * ‖z‖ := (kL H w x).le_opNorm z
      _ = ‖z‖ * ‖kL H w x‖ := mul_comm _ _
  show AnalyticOnNhd ℂ (fun z => kerP H α Λ z w) Set.univ ∧ (fun z => kerP H α Λ z w) ∈ fixedBy H α Λ
  refine ⟨?_, ?_⟩
  · have hfun : (fun z => kerP H α Λ z w) = fun z => ∑' x : Λ, kC H α w x * Complex.exp (kL H w x z) :=
      funext fun z => tsum_congr fun x => term_eq H α w x z
    rw [hfun]
    exact hE V Λ (fun x => kC H α w x) (fun x => kL H w x) (kernel_summable_bound hS hN H Λ α hH hP hL hα w)
  · intro y hy z
    have hmul := heisenbergMul V H hH
    show α y * (kerP H α Λ (z + y) w *
      Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) = kerP H α Λ z w
    unfold kerP
    rw [← tsum_mul_right, ← tsum_mul_left]
    have key : ∀ x : Λ, α y * (α x * opU H x (kerK H w) (z + y) *
        Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) =
        α ((x : V) + y) * opU H ((x : V) + y) (kerK H w) z := by
      intro x
      have h1 : opU H x (kerK H w) (z + y) * Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2) =
          opU H y (opU H x (kerK H w)) z := rfl
      have h2 := hmul y x (kerK H w) z
      have h3 := hα.2 x x.2 y hy
      have h4 : altE H y x = -altE H x y := by
        unfold altE
        rw [hH x y, Complex.conj_im]
      have h5 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((altE H y x : ℝ) : ℂ)) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x y : ℝ) : ℂ)) := by
        rw [h4]
        congr 1
        push_cast
        ring
      rw [mul_assoc (α x), h1, h2, h5, h3, add_comm y (x : V)]
      ring
    rw [tsum_congr key]
    exact (Equiv.addRight (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α (x : V) * opU H (x : V) (kerK H w) z)
end Formalism.L2.Th1.H
