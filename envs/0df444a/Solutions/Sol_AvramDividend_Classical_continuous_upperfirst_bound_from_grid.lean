-- Prove2me | solution 1 for AvramDividend.Classical.continuous_upperfirst_bound_from_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:14:14.940989+00:00
-- url     : https://prove2.me/submissions/e6610648-6a7c-4945-af91-db7d705ad4aa

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_grid_exit_fatou_uniform_bound
import Theorems.Thm_AvramDividend_Classical_grid_upperfirst_liminf_of_strict_order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Continuous upper-first rewards inherit a grid integral bound when clock ties occur only at infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (q : ℝ)
    (up down : Ω → ENNReal)
    (upGrid downGrid : ℕ → Ω → ENNReal)
    (hu : ∀ ω, Tendsto (fun n => upGrid n ω) atTop (nhds (up ω)))
    (hd : ∀ ω, Tendsto (fun n => downGrid n ω) atTop (nhds (down ω)))
    (hSep : ∀ ω, up ω < down ω ∨ down ω < up ω ∨
      (up ω = ⊤ ∧ down ω = ⊤))
    (hMeas : ∀ n : ℕ, Measurable
      (fun ω => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0))
    (B : ENNReal)
    (hGrid : ∀ n : ℕ,
      (∫⁻ ω, (if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) ∂P) ≤ B) :
    (∫⁻ ω, (if up ω < down ω then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
      else 0) ∂P) ≤ B := by
  have hpath : ∀ ω : Ω,
      (if up ω < down ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
        else 0) ≤
      liminf (fun n => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) atTop := by
    intro ω
    rcases hSep ω with hUpper | hLower | ⟨hUpInf, hDownInf⟩
    · exact le_of_eq
        (AvramDividend.Classical.grid_upperfirst_liminf_of_strict_order
          q (up ω) (down ω)
          (fun n => upGrid n ω) (fun n => downGrid n ω)
          (hu ω) (hd ω) (Or.inl hUpper))
    · exact le_of_eq
        (AvramDividend.Classical.grid_upperfirst_liminf_of_strict_order
          q (up ω) (down ω)
          (fun n => upGrid n ω) (fun n => downGrid n ω)
          (hu ω) (hd ω) (Or.inr hLower))
    · have hnot : ¬ up ω < down ω := by
        rw [hUpInf, hDownInf]
        exact lt_irrefl _
      simpa only [if_neg hnot, ENNReal.bot_eq_zero] using
        (bot_le : (⊥ : ENNReal) ≤
          liminf (fun n => if upGrid n ω < downGrid n ω then
            ENNReal.ofReal (Real.exp
              (-(q * ENNReal.toReal (upGrid n ω))))
            else 0) atTop)
  exact AvramDividend.Classical.grid_exit_fatou_uniform_bound P
    (fun ω => if up ω < down ω then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω)))) else 0)
    (fun n ω => if upGrid n ω < downGrid n ω then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
      else 0)
    hMeas hpath B hGrid
