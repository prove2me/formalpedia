-- Prove2me | solution 1 for EndoRefLA.PartialPPE.V_self_eq_Ex
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:32:42.352485+00:00
-- url     : https://prove2.me/submissions/973a76e4-3d75-43e7-8f00-46a016be373b

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

open MeasureTheory Filter Topology

open EndoRefLA.PartialPPE in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    ∀ X : Ω → ℝ, V P α u u0 lam X X = Ex P (fun ω => uE u u0 (X ω)) := by
  intro X
  by_cases hA : ∀ᵐ ω ∂P, uE u u0 (X ω) ≠ ⊥
  · have hae : (fun ω => gl lam (uE u u0 (X ω) - uE u u0 (X ω))) =ᵐ[P] 0 := by
      filter_upwards [hA] with ω h
      have htop : uE u u0 (X ω) ≠ ⊤ := by
        unfold uE
        split_ifs
        · exact EReal.coe_ne_top _
        · exact hu.u0_ne_top
      rw [EReal.sub_self htop h]
      simp only [gl, le_refl, if_true, Pi.zero_apply]
    have hae2 : (fun ω => (gl lam (uE u u0 (X ω) - uE u u0 (X ω))).toReal) =ᵐ[P] 0 :=
      hae.mono fun ω h => by simp only [h, Pi.zero_apply, EReal.toReal_zero]
    have hcond : (∀ᵐ ω ∂P, gl lam (uE u u0 (X ω) - uE u u0 (X ω)) ≠ ⊥ ∧
        gl lam (uE u u0 (X ω) - uE u u0 (X ω)) ≠ ⊤) ∧
        Integrable (fun ω => (gl lam (uE u u0 (X ω) - uE u u0 (X ω))).toReal) P := by
      refine ⟨?_, (integrable_zero Ω ℝ P).congr hae2.symm⟩
      filter_upwards [hae] with ω h
      rw [h]
      exact ⟨EReal.zero_ne_bot, EReal.zero_ne_top⟩
    have hgl : Ex P (fun ω => gl lam (uE u u0 (X ω) - uE u u0 (X ω))) = 0 := by
      unfold Ex
      rw [if_pos hcond, integral_congr_ae hae2]
      simp
    unfold V
    rw [hgl, mul_zero, add_zero]
  · have hbot : Ex P (fun ω => uE u u0 (X ω)) = ⊥ := by
      unfold Ex
      rw [if_neg]
      rintro ⟨h1, _⟩
      apply hA
      filter_upwards [h1] with ω h
      exact h.1
    unfold V
    rw [hbot, EReal.bot_add]
