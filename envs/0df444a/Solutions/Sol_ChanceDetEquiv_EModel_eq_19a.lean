-- Prove2me | solution 1 for ChanceDetEquiv.EModel.eq_19a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:46:33.79808+00:00
-- url     : https://prove2.me/submissions/90aaaea2-ceb1-4610-a70b-968bb5e73488

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open ChanceDetEquiv.EModel

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ)
    (hb : ∀ k, Integrable (fun ω => b ω k) P)
    (hc : ∀ j, Integrable (fun ω => c ω j) P)
    (hcb : ∀ j k, Integrable (fun ω => c ω j * b ω k) P)
    (huncorr : ∀ j k, ∫ ω, c ω j * b ω k ∂P = (∫ ω, c ω j ∂P) * (∫ ω, b ω k ∂P))
    (D : Matrix (Fin n) (Fin m) ℝ) :
    expectedObjective P b c D = detObjective P b c D := by
  unfold expectedObjective detObjective meanVec
  have e1 : ∀ ω, c ω ⬝ᵥ (D *ᵥ b ω) = ∑ j, ∑ k, D j k * (c ω j * b ω k) := by
    intro ω
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
  simp_rw [e1]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => (hcb j k).const_mul (D j k)))]
  have e2 : ∀ j, ∫ ω, ∑ k, D j k * (c ω j * b ω k) ∂P = ∑ k, D j k * ((∫ ω, c ω j ∂P) * (∫ ω, b ω k ∂P)) := by
    intro j
    rw [integral_finset_sum _ (fun k _ => (hcb j k).const_mul (D j k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul, huncorr]
  simp_rw [e2]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)
