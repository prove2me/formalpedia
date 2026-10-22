-- Prove2me | solution 1 for ChanceDetEquiv.EModel.footnote_30
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:46:35.117411+00:00
-- url     : https://prove2.me/submissions/a5ebb382-b031-4e76-a437-9cdc1ba90537

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open ChanceDetEquiv.EModel

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) :
    sigmaSq P A b D i - (muRow P A b D i) ^ 2 = centeredSecondMoment P A b D i := by
  set w : Fin m → ℝ := (A * D) i with hw
  have hlin : ∀ v : Fin m → ℝ, (A *ᵥ (D *ᵥ v)) i = ∑ k, w k * v k := by
    intro v
    rw [Matrix.mulVec_mulVec]
    rfl
  set X : Ω → ℝ := fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i with hX
  have hXform : X = fun ω => ∑ k, w k * b ω k - b ω i := by
    funext ω; simp only [hX, hlin]
  have hXL2 : MemLp X 2 P := by
    rw [hXform]
    refine MemLp.sub ?_ (hb i)
    exact memLp_finsetSum (Finset.univ : Finset (Fin m)) (fun k _ => (hb k).const_mul (w k))
  have hbint : ∀ k, Integrable (fun ω => b ω k) P := fun k => (hb k).integrable (by norm_num)
  have hEX : ∫ ω, X ω ∂P = (A *ᵥ (D *ᵥ meanVec P b)) i - meanVec P b i := by
    rw [hXform]
    simp only
    rw [integral_sub (integrable_finsetSum _ (fun k _ => (hbint k).const_mul (w k))) (hbint i),
      integral_finsetSum _ (fun k _ => (hbint k).const_mul (w k))]
    simp only [integral_const_mul]
    rw [hlin]
    rfl
  have h1 : sigmaSq P A b D i = ∫ ω, X ω ^ 2 ∂P := rfl
  have h2 : muRow P A b D i = -(∫ ω, X ω ∂P) := by
    rw [hEX]; unfold muRow; ring
  have h3 : centeredSecondMoment P A b D i = ∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P := by
    unfold centeredSecondMoment
    congr 1
    funext ω
    rw [hEX]
    have : (A *ᵥ (D *ᵥ (b ω - meanVec P b))) i = (A *ᵥ (D *ᵥ b ω)) i - (A *ᵥ (D *ᵥ meanVec P b)) i := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub]; rfl
    rw [this]
    simp only [hX]
    ring
  have hvar := variance_eq_integral hXL2.aemeasurable
  have hvar2 := variance_eq_sub hXL2
  rw [h1, h2, h3, neg_sq]
  have : (∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P) = variance X P := by
    rw [hvar]
  rw [this, hvar2]
  rfl
