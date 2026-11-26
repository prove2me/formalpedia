-- Prove2me | solution 1 for FD1D.node_harmonic_drift_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:21.11714+00:00
-- url     : https://prove2.me/submissions/bbf49bef-9a5d-4449-a415-376785afb4ca

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (a N p q : ℝ) (hNa : N + a ≠ 0) (hNa1 : N + a + 1 ≠ 0) :
    p * (1 - q) / (N + a + 1) - q * (1 - p) / (N + a) =
      (p - q) / (N + a) -
        p * (1 - q) / ((N + a) * (N + a + 1)) := by
  field_simp
  ring
end FD1D
