-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_reduce
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:57.381662+00:00
-- url     : https://prove2.me/submissions/e756e62e-0a72-4687-9425-f9093d8bcbd8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_step

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
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (ι : Type) [Fintype ι] (n : ℕ) (Γ c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v : ι → E), (∀ l, ‖v l‖ = 1) → ∀ (A : Set E) (w : E → ℝ) (φ : E → ℝ) (τ : ℝ), 0 < τ →
      (∀ x ∈ A, 0 < w x) → (∀ x ∈ A, τ ≤ w x ^ 2) → ContDiff ℝ 1 φ → Sym A w 1 n Γ (fderiv ℝ φ) →
      (∀ x ∈ A, c₀ * w x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (v l)) ^ 2 + τ) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (b : E → V) (m : ℤ) (K : ℝ),
        HasCompactSupport b → tsupport b ⊆ A → Sym A w m n K b →
        ∃ b' : E → V, HasCompactSupport b' ∧ tsupport b' ⊆ A ∧ Sym A w (m - 2 * (n : ℤ)) 0 (C * τ ^ n * K) b' ∧
          ∫ x, osc φ τ x • b x ∂μ = ∫ x, osc φ τ x • b' x ∂μ := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro v _ A w φ τ _ _ _ _ _ _ V _ _ b m K hbs hbA hb
    exact ⟨b, hbs, hbA, B_cast hb (by simp) (by simp), rfl⟩
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨C₁, hC₁0, hC₁⟩ := B_step (E := E) (μ := μ) ι n Γ c₀ hc₀
    refine ⟨C * C₁, mul_nonneg hC0 hC₁0, ?_⟩
    intro v hv A w φ τ hτ hw hτw hφ hφS hD V _ _ b m K hbs hbA hb
    obtain ⟨b₁, hb₁s, hb₁A, hb₁S, hEq₁⟩ := hC₁ v hv A w φ τ hτ hw hτw hφ hφS hD V b m K hbs hbA hb
    obtain ⟨b₂, hb₂s, hb₂A, hb₂S, hEq₂⟩ := hC v hv A w φ τ hτ hw hτw hφ
      (hφS.mono hw (Nat.le_succ n) le_rfl) hD V b₁ (m - 2) (C₁ * τ * K) hb₁s hb₁A hb₁S
    refine ⟨b₂, hb₂s, hb₂A, B_cast hb₂S (by push_cast; ring) (by ring), hEq₁.trans hEq₂⟩
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
