-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.abConvex_expectation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:49:42.819665+00:00
-- url     : https://prove2.me/submissions/9e572db6-a542-4720-9a8c-95ded102b375

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem aux_abce_main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (a b : ℝ)
    (f : ℝ → (Fin n → ℝ) → ℝ) (hf : ∀ y, ABConvex a b (fun x => f x y))
    (D : Ω → ℝ) (Y : Ω → (Fin n → ℝ))
    (hint : ∀ x, Integrable (fun ω => f (x - D ω) (Y ω)) P) :
    ABConvex a b (fun x => ∫ ω, f (x - D ω) (Y ω) ∂P) := by
  intro x₁ x₂ hx θ hθ0 hθ1
  simp only
  have hpt : ∀ ω, f ((θ * x₁ + (1 - θ) * x₂) - D ω) (Y ω) ≤
      θ * (a + f (x₁ - D ω) (Y ω)) + (1 - θ) * (b + f (x₂ - D ω) (Y ω)) := by
    intro ω
    have h := hf (Y ω) (x₁ - D ω) (x₂ - D ω) (by linarith) θ hθ0 hθ1
    have heq : θ * (x₁ - D ω) + (1 - θ) * (x₂ - D ω) = (θ * x₁ + (1 - θ) * x₂) - D ω := by ring
    simp only [heq] at h
    exact h
  have h1 := hint x₁
  have h2 := hint x₂
  have hR : Integrable (fun ω => θ * (a + f (x₁ - D ω) (Y ω)) + (1 - θ) * (b + f (x₂ - D ω) (Y ω))) P := by
    exact (((integrable_const a).add h1).const_mul θ).add (((integrable_const b).add h2).const_mul (1 - θ))
  calc ∫ ω, f ((θ * x₁ + (1 - θ) * x₂) - D ω) (Y ω) ∂P
      ≤ ∫ ω, (θ * (a + f (x₁ - D ω) (Y ω)) + (1 - θ) * (b + f (x₂ - D ω) (Y ω))) ∂P :=
        integral_mono (hint _) hR hpt
    _ = θ * (a + ∫ ω, f (x₁ - D ω) (Y ω) ∂P) + (1 - θ) * (b + ∫ ω, f (x₂ - D ω) (Y ω) ∂P) := by
        have hA : Integrable (fun ω => θ * (a + f (x₁ - D ω) (Y ω))) P :=
          ((integrable_const a).add h1).const_mul θ
        have hB : Integrable (fun ω => (1 - θ) * (b + f (x₂ - D ω) (Y ω))) P :=
          ((integrable_const b).add h2).const_mul (1 - θ)
        rw [integral_add hA hB, integral_const_mul, integral_const_mul,
          integral_add (integrable_const a) h1, integral_add (integrable_const b) h2]
        simp

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f : ℝ → (Fin n → ℝ) → ℝ) (hf : ∀ y, ABConvex a b (fun x => f x y))
    (D : Ω → ℝ) (Y : Ω → (Fin n → ℝ))
    (hint : ∀ x, Integrable (fun ω => f (x - D ω) (Y ω)) P) :
    ABConvex a b (fun x => ∫ ω, f (x - D ω) (Y ω) ∂P) :=
  aux_abce_main P a b f hf D Y hint
