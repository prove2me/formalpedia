-- Prove2me | solution 1 for FCP.BatemanHorn.bateman_horn_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-12T03:23:37.482337+00:00
-- url     : https://prove2.me/submissions/fbd7dc6c-9ffc-4c9f-8034-f30edb958d4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FCP_BatemanHorn_partialProduct_tendsto_pos
import Theorems.Thm_FCP_BatemanHorn_integral_counting_conjecture
import Theorems.Thm_AsymptoticNumberTheory_logarithmicIntegral_isEquivalent

open Polynomial Filter Topology Asymptotics FCP.BatemanHorn

-- This is a reduction to three independently tracked obligations.
-- In particular, integral_counting_conjecture remains conjectural.
theorem solution (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) ∧
      (fun x : ℝ => (countSimultaneousPrimes polys x : ℝ)) ~[atTop]
        (fun x : ℝ => C / degreesProduct polys * x / (Real.log x) ^ polys.card) := by
  obtain ⟨C, hC, h_limit⟩ :=
    partialProduct_tendsto_pos polys h_nonempty h_bunyakovsky h_schinzel
  refine ⟨C, hC, h_limit, ?_⟩
  have h_count := integral_counting_conjecture
    polys h_nonempty h_bunyakovsky h_schinzel C hC h_limit
  have h_integral := AsymptoticNumberTheory.logarithmicIntegral_isEquivalent
    polys.card (Finset.card_pos.mpr h_nonempty)
  have h_const : (fun _ : ℝ => C / (degreesProduct polys : ℝ)) ~[atTop]
      (fun _ : ℝ => C / (degreesProduct polys : ℝ)) := IsEquivalent.refl
  have h_scaled :
      (fun x : ℝ => C / degreesProduct polys *
        ∫ t in (2 : ℝ)..x, (1 : ℝ) / (Real.log t) ^ polys.card) ~[atTop]
      (fun x : ℝ => C / degreesProduct polys * (x / (Real.log x) ^ polys.card)) :=
    h_const.mul h_integral
  exact h_count.trans (by simpa only [mul_div_assoc] using h_scaled)
