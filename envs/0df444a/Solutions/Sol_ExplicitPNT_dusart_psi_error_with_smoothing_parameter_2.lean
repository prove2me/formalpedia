-- Prove2me | solution 2 for ExplicitPNT.dusart_psi_error_with_smoothing_parameter
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-14T12:20:12.802157+00:00
-- url     : https://prove2.me/submissions/6049e273-0f2b-493d-9894-0cb972d753be

import Definitions.Def_dusart_psi_433_20261014_FinalPsi

theorem solution
    (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < Real.sqrt (Real.log x / R)) :
    let X := Real.sqrt (Real.log x / R)
    ∃ ν : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧
      |Chebyshev.psi x - x| <
        x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
          (Real.sqrt (Real.sqrt
            (ν ^ 6 / (2 * ν ^ 2 - 1) *
              (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
              (1 - Real.log (2 * Real.pi) / (X * ν)))) *
            Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X))) := by
  simpa only [DusartSmoothing.X, DusartSmoothing.U] using
    DusartSmoothing.dusart_psi_smoothing_bound R hR hzero x hx hX

