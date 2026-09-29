-- Prove2me | solution 1 for DiazModulus.diaz_locus_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T10:13:35.002966+00:00
-- url     : https://prove2.me/submissions/8338c3f3-1e4f-47ad-9b29-e40b3cde15d4

import Definitions.Def_DiazModulus
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_normal_form

open Complex ComplexConjugate

/-- Algebraicity over `ℚ` is unchanged by the embedding `ℝ ↪ ℂ`. -/
private theorem dzb_alg_ofReal {x : ℝ} : IsAlgebraic ℚ ((x : ℂ)) ↔ IsAlgebraic ℚ x :=
  isAlgebraic_algebraMap_iff (A := ℂ) (S := ℝ) (R := ℚ) Complex.ofReal_injective

theorem solution :
    DiazModulus.Qbar = Diaz.Qbar ∧
      ∀ u : ℂ, DiazModulus.IsCandidate u ↔
        (u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp u) ∧ IsAlgebraic ℚ (u * conj u)) := by
  refine ⟨rfl, fun u => ⟨?_, ?_⟩⟩
  · rintro ⟨hu0, hmod, hexp⟩
    exact ⟨hu0, hexp, (Diaz.normal_form hu0).1.mp (dzb_alg_ofReal.mp hmod)⟩
  · rintro ⟨hu0, hexp, hrho⟩
    exact ⟨hu0, dzb_alg_ofReal.mpr ((Diaz.normal_form hu0).1.mpr hrho), hexp⟩
