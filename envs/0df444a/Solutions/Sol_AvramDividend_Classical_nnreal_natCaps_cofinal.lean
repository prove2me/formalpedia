-- Prove2me | solution 1 for AvramDividend.Classical.nnreal_natCaps_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:16:09.822311+00:00
-- url     : https://prove2.me/submissions/e270269a-da88-4761-8894-4cf71e2f2f8a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

theorem solution :
    ∀ t : ℝ≥0, ∃ n : ℕ, t < (n : ℝ≥0) := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  refine ⟨n, ?_⟩
  exact_mod_cast hn
