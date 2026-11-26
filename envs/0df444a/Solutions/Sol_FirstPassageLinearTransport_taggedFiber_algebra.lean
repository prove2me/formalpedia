-- Prove2me | solution 1 for FirstPassageLinearTransport.taggedFiber_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:22.689085+00:00
-- url     : https://prove2.me/submissions/d5e111f8-23cf-455b-8745-ef9fb0d3f03b

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y h : ℕ}
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3) :
    ((h : ℚ) / (2 * (Y : ℚ))) *
          ((2 : ℚ) ^ (M + 1) /
            (1 - (h : ℚ) / (2 * (Y : ℚ)))) =
      2 * (h : ℚ) * (2 : ℚ) ^ M /
        (2 * (Y : ℚ) - (h : ℚ)) := by
  have hYQ : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
  have hden : (0 : ℚ) < 2 * (Y : ℚ) - (h : ℚ) := by
    have hscaled := (div_le_iff₀ hYQ).mp hsmall
    have : (h : ℚ) ≤ (2 * (Y : ℚ)) / 3 := by
      nlinarith
    nlinarith
  field_simp
  rw [pow_succ]
  ring
end FirstPassageLinearTransport
