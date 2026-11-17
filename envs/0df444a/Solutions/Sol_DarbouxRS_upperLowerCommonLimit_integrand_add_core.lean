-- Prove2me | solution 1 for DarbouxRS.upperLowerCommonLimit_integrand_add_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:55:39.2142+00:00
-- url     : https://prove2.me/submissions/8408b111-4bba-4d18-b880-458d338bcd94

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_lowerSum_le_upperSum_core
import Theorems.Thm_DarbouxRS_upperSum_integrand_add_le_core
import Theorems.Thm_DarbouxRS_lowerSum_integrand_add_le_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

private theorem source_upperLowerCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P hmesh
  have hPf := Hf P (lt_of_lt_of_le hmesh (min_le_left δf δg))
  have hPg := Hg P (lt_of_lt_of_le hmesh (min_le_right δf δg))
  have hsumUpper :
      upperSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    upperSum_integrand_add_le_core P hsf hsg
  have hsumLower :
      lowerSum P f alpha + lowerSum P g alpha ≤
        lowerSum P (fun x => f x + g x) alpha :=
    lowerSum_integrand_add_le_core P hsf hsg
  have hlowerUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    lowerSum_le_upperSum_core P (sourceHypotheses_integrand_add hsf hsg)
  have hfu := abs_lt.mp hPf.1
  have hfl := abs_lt.mp hPf.2
  have hgu := abs_lt.mp hPg.1
  have hgl := abs_lt.mp hPg.2
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith

/-- The exact published additivity theorem, assembled from the source argument. -/
theorem solution {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  exact source_upperLowerCommonLimit_integrand_add hf hg
