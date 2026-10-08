-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_attained_of_interior_gap_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:02:16.108914+00:00
-- url     : https://prove2.me/submissions/50e9ecbb-c218-4b80-a073-b42454ad4f32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_minimizer_exists_of_deriv_below_boundary_and_tail
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_continuous_deriv_strict_boundary_gap
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer

open AvramDividend.Classical Filter Set
open scoped ENNReal

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : 0 < a) (hgap : deriv W a < deriv W 0)
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W a ≤ deriv W x) :
    cstar W < ⊤ ∧ (cstar W).toReal ∈ cstarSet W := by
  obtain ⟨b, hb⟩ :=
    cstar_minimizer_exists_of_deriv_below_boundary_and_tail
      W hcont a ha hgap htail
  have hbgap : deriv W b < deriv W 0 :=
    (hb.2 a ha).trans_lt hgap
  exact ⟨cstar_lt_top_of_minimizer W ⟨b, hb⟩,
    cstar_attained_of_continuous_deriv_strict_boundary_gap W hcont b hb hbgap⟩
