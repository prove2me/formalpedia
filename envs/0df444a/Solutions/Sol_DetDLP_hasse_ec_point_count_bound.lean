-- Prove2me | solution 1 for DetDLP.hasse_ec_point_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:20.943843+00:00
-- url     : https://prove2.me/submissions/75b15e84-f870-4084-a333-ea256193bed2

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_hasse_quadratic_form_and_elementary_point_bound
import Theorems.Thm_DetDLP_frobenius_isogeny_degree_quadratic_nonneg

set_option autoImplicit false

open DetDLP

theorem solution :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        |(Fintype.card E.toAffine.Point : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro p _ hp3 E _
  let _ := ecPointFintype E
  have hQ := DetDLP.frobenius_isogeny_degree_quadratic_nonneg p hp3 E
  exact (DetDLP.hasse_quadratic_form_and_elementary_point_bound.2
    p (Fintype.card E.toAffine.Point) (by omega) hQ).2
