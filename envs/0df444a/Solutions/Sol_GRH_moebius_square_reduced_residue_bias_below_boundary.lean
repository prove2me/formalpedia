-- Prove2me | solution 1 for GRH.moebius_square_reduced_residue_bias_below_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:07:39.752564+00:00
-- url     : https://prove2.me/submissions/7df087e2-7f9e-4cfd-966e-c21b2a089cc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_moebius_residue_bias_of_primitive_zero_free_band
import Theorems.Thm_GRH_primitive_nonprincipal_LFunction_nonzero_below_record
import Definitions.Def_GRH_MoebiusBilinear
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false in
theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (hmany : 1 < q.totient) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hrecord : σ ≤ (0.8749570698 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) - (∑ k ∈ Finset.range (u ^ 2 + 1),
          if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) / (q.totient : ℝ)| ≤ D * ((u : ℝ) ^ 2 + 1) ^ σ := by
  let α : ℝ := (1/2 + σ)/2
  have hα : (1/2:ℝ) ≤ α := by dsimp [α]; linarith
  have hσ : α < σ := by dsimp [α]; linarith
  obtain ⟨C, hC, h⟩ := GRH.moebius_residue_bias_of_primitive_zero_free_band q α σ hα
    (hσ.le.trans hrecord) hσ
    (fun d _ _ ψ hp hψ s hs hr =>
      GRH.primitive_nonprincipal_LFunction_nonzero_below_record d ψ hp hψ s (hα.trans_lt hs) hr) a ha
  refine ⟨C, hC, ?_⟩
  intro u
  have e : ((u^2 : ℕ) : ℝ) = (u:ℝ)^2 := by norm_cast
  rw [← e]
  exact h (u^2)
