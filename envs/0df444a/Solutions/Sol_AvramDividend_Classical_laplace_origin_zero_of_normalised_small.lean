-- Prove2me | solution 1 for AvramDividend.Classical.laplace_origin_zero_of_normalised_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:30:37.155839+00:00
-- url     : https://prove2.me/submissions/32973c6b-7bcb-4d05-94fb-d572104c3fdb

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Topology

/-- An increasing, nonnegative function with a sufficiently small
normalised positive Laplace transform must vanish at the origin. -/
theorem solution
    (W ψ : ℝ → ℝ) (q β₀ : ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Ici (0 : ℝ)))
    (hLap : ∀ θ : ℝ, β₀ ≤ θ → 0 < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * W x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * W x) =
        (ψ θ - q)⁻¹)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ θ : ℝ, β₀ ≤ θ ∧ 0 < θ ∧ θ * (ψ θ - q)⁻¹ < ε) :
    W 0 = 0 := by
  have hw0 : 0 ≤ W 0 := hW 0 le_rfl
  rcases eq_or_lt_of_le hw0 with hz | hpos
  · exact hz.symm
  obtain ⟨θ, hθb, hθ, hε⟩ := hsmall (W 0) hpos
  obtain ⟨hInt, hLapEq⟩ := hLap θ hθb hθ
  have hExpInt :
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x)) (Ioi 0) := by
    exact integrableOn_exp_mul_Ioi (a := -θ) (by linarith) 0
  have hConstInt :
      IntegrableOn (fun x : ℝ => W 0 * Real.exp (-θ * x)) (Ioi 0) :=
    hExpInt.const_mul _
  have hPoint :
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        W 0 * Real.exp (-θ * x) ≤
          Real.exp (-θ * x) * W x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hle : W 0 ≤ W x :=
      hmono (by simp) (by simpa only [mem_Ici] using le_of_lt hx)
        (le_of_lt hx)
    calc
      W 0 * Real.exp (-θ * x) =
        Real.exp (-θ * x) * W 0 := mul_comm _ _
      _ ≤ Real.exp (-θ * x) * W x :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
  have hIntBound :
      (∫ x in Ioi (0 : ℝ), W 0 * Real.exp (-θ * x)) ≤
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * W x) :=
    integral_mono_ae hConstInt hInt hPoint
  have hExpVal :
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x)) = θ⁻¹ := by
    have hh := integral_exp_mul_Ioi (a := -θ) (by linarith) (0 : ℝ)
    simpa [div_eq_mul_inv] using hh
  have hBound : W 0 / θ ≤ (ψ θ - q)⁻¹ := by
    calc
      W 0 / θ = W 0 * (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x)) := by
        rw [hExpVal]
        ring
      _ = ∫ x in Ioi (0 : ℝ), W 0 * Real.exp (-θ * x) := by
        rw [integral_const_mul]
      _ ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * W x :=
        hIntBound
      _ = (ψ θ - q)⁻¹ := hLapEq
  have hθBound : W 0 ≤ θ * (ψ θ - q)⁻¹ := by
    have hh := (div_le_iff₀ hθ).mp hBound
    simpa [mul_comm] using hh
  exact False.elim ((not_lt_of_ge hθBound) hε)
