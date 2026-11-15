-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a247_Gaussian_HJB_scalar_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:40:37.068835+00:00
-- url     : https://prove2.me/submissions/5be9ffcb-ef15-4e3d-b988-f1f83a8cf1e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (sigma c q lambdaPlus lambdaMinus w1 w2 w0 : ℝ)
    (hSum : lambdaPlus + lambdaMinus = -2*c/sigma^2)
    (hProd : lambdaPlus * lambdaMinus = -2*q/sigma^2)
    (hSigma : 0 < sigma) :
    (sigma^2/2) * (w2-(lambdaPlus+lambdaMinus)*w1+
      lambdaPlus*lambdaMinus*w0) =
    (sigma^2/2)*w2+c*w1-q*w0 := by
  have hn : sigma^2 ≠ 0 := pow_ne_zero _ (ne_of_gt hSigma)
  rw [hSum,hProd]
  field_simp [hn]
  ring
