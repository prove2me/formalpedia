-- Prove2me | solution 1 for DerivativeChainPrivate.real_root_defect_derivative
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:46:45.135982+00:00
-- url     : https://prove2.me/submissions/901b487c-a392-43d9-9d5b-76a65e5132cc

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

set_option autoImplicit false

theorem solution (p : Polynomial ℝ) :
    p.derivative.natDegree - p.derivative.roots.card ≤
      p.natDegree - p.roots.card := by
  have hR := p.card_roots_le_derivative
  have hD := Polynomial.natDegree_derivative p
  have hRle := Polynomial.card_roots' p
  omega
