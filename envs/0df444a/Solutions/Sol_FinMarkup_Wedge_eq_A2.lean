-- Prove2me | solution 1 for FinMarkup.Wedge.eq_A2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:51:12.452616+00:00
-- url     : https://prove2.me/submissions/24614da5-232b-4cf3-bd12-dc81929f9252

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

open FinMarkup.Wedge in
theorem solution (m : Params) (hS : m.Standing) (Pt M p : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hp : 0 < p) :
    HasDerivAt (fun q => driftM m Pt M q)
      (-(m.beta * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps) * M)) p := by
  have h1 : HasDerivAt (fun q : ℝ => q / Pt) (1 / Pt) p := (hasDerivAt_id' p).div_const Pt
  have h2 := h1.rpow_const (p := -m.eta) (Or.inl (div_pos hp hPt).ne')
  have h3 := (((h2.const_mul M).mul_const (Pt ^ (-m.eps))).const_mul m.beta).sub_const
    (m.rho * M)
  unfold driftM demand
  refine h3.congr_deriv ?_
  have e : Pt ^ (m.eta - m.eps) = Pt ^ (-m.eps) / Pt ^ (-m.eta - 1) / Pt := by
    rw [← Real.rpow_sub hPt, ← Real.rpow_sub_one hPt.ne']
    congr 1
    ring
  have hA : 0 < Pt ^ (-m.eta - 1) := Real.rpow_pos_of_pos hPt _
  have hB : 0 < Pt ^ (-m.eps) := Real.rpow_pos_of_pos hPt _
  rw [e, Real.div_rpow hp.le hPt.le]
  field_simp <;> ring_nf
