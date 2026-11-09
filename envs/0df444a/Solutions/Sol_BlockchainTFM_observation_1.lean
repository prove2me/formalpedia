-- Prove2me | solution 1 for BlockchainTFM.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:17:58.486715+00:00
-- url     : https://prove2.me/submissions/b8f30d1a-fa47-4822-b10b-ae9c279f2b15

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Properties

open MeasureTheory

open BlockchainTFM in
theorem solution {n : ℕ} (V₀ : Measure ℝ) [IsProbabilityMeasure V₀]
    (hV₀ : V₀ (Set.Icc 0 1) = 1) (M Mt : TFM n) (θ : (Fin n → ℝ) → Fin n → ℝ)
    (halloc : Mt.alloc = M.alloc)
    (hθ : ∀ b i, θ b i = M.alloc b i * (Mt.pay b i - M.pay b i))
    (hM : IsUBNIC V₀ M)
    (hθint : ∀ i : Fin n, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun b => θ (Function.update b i x) i) (Measure.pi fun _ : Fin n => V₀))
    (hθzero : ∀ i : Fin n, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∫ b, θ (Function.update b i x) i ∂(Measure.pi fun _ : Fin n => V₀) = 0) :
    IsUBNIC V₀ Mt := by
  have hu : ∀ i b v, utility Mt i b v = utility M i b v - θ b i := by
    intro i b v
    unfold utility
    rw [hθ, halloc]
    ring
  have hI : ∀ i x v, x ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 →
      interimUtility V₀ Mt i x v = interimUtility V₀ M i x v := by
    intro i x v hx hv
    unfold interimUtility
    simp only [hu]
    rw [integral_sub (hM i v hv x hx).1 (hθint i x hx), hθzero i x hx, sub_zero]
  intro i v hv x hx
  refine ⟨?_, ?_⟩
  · simp only [hu]
    exact (hM i v hv x hx).1.sub (hθint i x hx)
  · rw [hI i x v hx hv, hI i v v hv hv]
    exact (hM i v hv x hx).2
