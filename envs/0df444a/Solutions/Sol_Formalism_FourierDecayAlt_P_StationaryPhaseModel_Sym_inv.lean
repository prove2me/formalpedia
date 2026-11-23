-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:02.197735+00:00
-- url     : https://prove2.me/submissions/8e85a151-0c42-40d5-bb91-79cbf6de5294

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_A_fderiv_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Sym
theorem _root_.solution (N : ℕ) (K c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Set E) (w : E → ℝ) (f : E → ℝ),
    (∀ x ∈ A, 0 < w x) → Sym A w 2 N K f → (∀ x, 0 < f x) → (∀ x ∈ A, c * w x ^ 2 ≤ f x) →
    Sym A w (-2) N C (fun x => (f x)⁻¹) := by
  have hzero : ∀ (A : Set E) (w : E → ℝ) (f : E → ℝ), (∀ x ∈ A, 0 < w x) → (∀ x, 0 < f x) →
      (∀ x ∈ A, c * w x ^ 2 ≤ f x) → ∀ x ∈ A, ‖(f x)⁻¹‖ ≤ c⁻¹ * w x ^ (-2 : ℤ) := by
    intro A w f hw hpos hlow x hx
    have hwx := hw x hx
    rw [Real.norm_of_nonneg (inv_pos.2 (hpos x)).le]
    have h1 : (f x)⁻¹ ≤ (c * w x ^ 2)⁻¹ := inv_anti₀ (by positivity) (hlow x hx)
    refine h1.trans (le_of_eq ?_)
    rw [mul_inv, zpow_neg]
    norm_cast
  induction N with
  | zero =>
    refine ⟨c⁻¹, (inv_pos.2 hc).le, fun A w f hw hf hpos hlow => ?_⟩
    refine ⟨hf.1.inv fun x => (hpos x).ne', fun x hx i hi => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [norm_iteratedFDeriv_zero]
    simpa using hzero A w f hw hpos hlow x hx
  | succ N ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨max c⁻¹ (2 ^ N * (2 ^ N * C * C) * K), le_max_of_le_left (inv_pos.2 hc).le,
      fun A w f hw hf hpos hlow => ?_⟩
    refine ⟨hf.1.inv fun x => (hpos x).ne', fun x hx i hi => ?_⟩
    have hwx := hw x hx
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDeriv_zero]
      refine (hzero A w f hw hpos hlow x hx).trans ?_
      simpa using mul_le_mul_of_nonneg_right (le_max_left c⁻¹ (2 ^ N * (2 ^ N * C * C) * K))
        (zpow_pos hwx (-2 : ℤ)).le
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j ≤ N := Nat.succ_le_succ_iff.1 hi
      have hg := ih A w f hw (hf.mono hw (Nat.le_succ N) le_rfl) hpos hlow
      have hd : Differentiable ℝ f := hf.1.differentiable (by norm_cast)
      have hS := ((hg.mul hw hg).smul hw hf.fderiv).neg
      rw [← norm_iteratedFDeriv_fderiv, A_fderiv_inv hd hpos]
      have h := hS.2 x hx j hj
      have e : (-2 + -2 + (2 - 1) - (j : ℤ)) = -2 - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_pos hwx _).le)
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
