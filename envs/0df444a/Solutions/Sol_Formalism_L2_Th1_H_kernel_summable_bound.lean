-- Prove2me | solution 1 for Formalism.L2.Th1.H.kernel_summable_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:43.225387+00:00
-- url     : https://prove2.me/submissions/c6390361-6cf1-4ee9-b01d-56d41818ee7e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_exists_form_bound
import Theorems.Thm_Formalism_L2_Th1_H_quad_bound

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (hS : LatGaussSummable) (hN : FormNorm) (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (w : V) (r : ℝ) :
    Summable fun x : Λ => ‖kC H α w x‖ * Real.exp (r * ‖kL H w x‖) := by
  obtain ⟨c0, C0, hc0, hC0, hn⟩ := hN V H hH hP
  obtain ⟨K, hK0, hK⟩ := exists_form_bound H
  have ha0 : 0 < Real.pi * c0 / 2 := by positivity
  obtain ⟨u, hu, hub⟩ := hS V Λ hL (Real.pi * c0 / 2 / 2) 0 (by positivity)
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
    (hu.mul_left (Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
      |r| * Real.pi * K * ‖w‖)))
  have hux := hub x 0 (by simp)
  simp only [sub_zero] at hux
  have hαx : ‖α x‖ = 1 := by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have hxw : ‖H x w‖ ≤ K * ‖w‖ * ‖(x : V)‖ := by
    have h1 : H x w = LinearMap.toContinuousLinearMap (H.flip w) x := rfl
    rw [h1]
    exact ((LinearMap.toContinuousLinearMap (H.flip w)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hK w) (norm_nonneg _))
  have hxx : c0 * ‖(x : V)‖ ^ 2 ≤ (H x x).re := (hn x).1
  have hkL : ‖kL H w x‖ ≤ Real.pi * (K * (‖w‖ + ‖(x : V)‖)) := by
    rw [kL, norm_smul]
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
    rw [hpi]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact (hK (w - x)).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hK0)
  have hre : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re ≤
      Real.pi * (K * ‖w‖ * ‖(x : V)‖) - Real.pi * (c0 * ‖(x : V)‖ ^ 2) / 2 := by
    have e : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re =
        Real.pi * (H x w).re - Real.pi * (H x x).re / 2 := by simp
    rw [e]
    have h1 : (H x w).re ≤ K * ‖w‖ * ‖(x : V)‖ := (Complex.re_le_norm _).trans hxw
    have h2 := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    have h3 := mul_le_mul_of_nonneg_left hxx Real.pi_pos.le
    linarith
  have hkC : ‖kC H α w x‖ = Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re) := by
    rw [kC, norm_mul, hαx, Complex.norm_exp, one_mul]
  have hr : r * ‖kL H w x‖ ≤ |r| * (Real.pi * (K * (‖w‖ + ‖(x : V)‖))) :=
    (mul_le_mul_of_nonneg_right (le_abs_self r) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hkL (abs_nonneg r))
  have hq := quad_bound (Real.pi * c0 / 2 / 2) (Real.pi * K * ‖w‖ + |r| * Real.pi * K) ‖(x : V)‖ (by positivity)
  rw [hkC, ← Real.exp_add]
  calc Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re + r * ‖kL H w x‖)
      ≤ Real.exp (((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
          |r| * Real.pi * K * ‖w‖) + (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2)) := by
        apply Real.exp_le_exp.2
        nlinarith [hre, hr, hq]
    _ = Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
          |r| * Real.pi * K * ‖w‖) * Real.exp (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hux (Real.exp_pos _).le
end Formalism.L2.Th1.H
