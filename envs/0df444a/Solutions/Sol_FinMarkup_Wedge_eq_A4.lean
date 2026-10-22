-- Prove2me | solution 1 for FinMarkup.Wedge.eq_A4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:27:11.938921+00:00
-- url     : https://prove2.me/submissions/6568945c-806e-40d0-9034-bb058a51f314

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model
set_option autoImplicit false
open FinMarkup.Wedge

theorem solution (m : Params) (hS : m.Standing) (Pt M W p : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hp : 0 < p) :
    HasDerivAt (fun q => driftW m Pt M W q)
      ((p ^ (-m.eta) * Pt ^ (m.eta - m.eps) -
        (p - m.R / m.A) * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps)) * M) p := by
  have hr : HasDerivAt (fun q : ℝ => q ^ (-m.eta)) ((-m.eta) * p ^ (-m.eta - 1)) p :=
    Real.hasDerivAt_rpow_const (Or.inl hp.ne')
  have h1 := (((hasDerivAt_id p).sub_const (m.R / m.A)).mul hr)
  have h2 := ((h1.mul_const (Pt ^ (m.eta - m.eps))).mul_const M).add_const ((m.r - m.lam) * W)
  unfold driftW
  exact h2.congr_deriv (by first | (simp only [id_eq]; ring) | ring)
