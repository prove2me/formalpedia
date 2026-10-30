-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_moving_frame_winding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:07:02.052264+00:00
-- url     : https://prove2.me/submissions/baf0b321-7dfc-4e3a-b34f-3cc1b67ff695

import Theorems.Thm_BirkhoffGlobalSection_moving_frame_graph_angle_transport
import Theorems.Thm_BirkhoffGlobalSection_polar_endpoint_winding_bound
import Theorems.Thm_HryniewiczCriterion_positive_path_graph_angle_bound
import Mathlib.Tactic

open HryniewiczCriterion Matrix
namespace HryniewiczCriterion
lemma omegaMat_mul_self : omegaMat * omegaMat = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
lemma blockOne_one : blockOne 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blockOne]
lemma sp_inv_mul_self {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g⁻¹ * g = 1 := by
  have h1 : (-(omegaMat * g.transpose * omegaMat)) * g = 1 := by
    have : (-(omegaMat * g.transpose * omegaMat)) * g =
        -(omegaMat * (g.transpose * omegaMat * g)) := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, h, omegaMat_mul_self, neg_neg]
  rw [Matrix.inv_eq_left_inv h1, h1]


end HryniewiczCriterion

theorem solution
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℝ) (hTpos : 0 < T)
    (hFsp : ∀ t, (F t).transpose * omegaMat * F t = omegaMat)
    (hFpos : ∀ t, 0 < (Complex.I * cdet (F t)).re)
    (hFc : ∀ i j, Continuous fun t => F t i j) (hFT : F T = F 0)
    (hφc : ∀ i j, ContinuousOn (fun t => φ t i j) (Set.Icc 0 1))
    (hφdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (hφ0 : φ 0 = 1)
    (S : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hSc : ∀ i j : Fin 4, Continuous fun t => S t i j)
    (hSpos : ∀ t, (S t).PosDef)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4,
      HasDerivAt (fun s => ((F 0)⁻¹ * F s * blockOne (φ (s / T))) i j)
        ((symplJ4 * S t * ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) i j) t) :
    ∀ d ∈ windingInterval φ, 1 < d := by
  let Y : ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
    fun t => (F 0)⁻¹ * F t * blockOne (φ (t / T))
  have h0 : Y 0 = 1 := by
    dsimp [Y]
    rw [zero_div, hφ0, blockOne_one, Matrix.mul_one]
    exact sp_inv_mul_self (hFsp 0)
  have hend : Y T = blockOne (φ 1) := by
    dsimp [Y]
    rw [div_self hTpos.ne', hFT, sp_inv_mul_self (hFsp 0), Matrix.one_mul]
  obtain ⟨θ, α, hθ, hα, heq⟩ := BirkhoffGlobalSection.moving_frame_graph_angle_transport
    F φ T hTpos hFsp hFpos hFc hFT hφc hφdet hφ0
  have hbound := positive_path_graph_angle_bound Y S T hTpos hSc hSpos h0 hd _ hend θ hθ
  exact BirkhoffGlobalSection.polar_endpoint_winding_bound φ hφdet α hα (by linarith)

