-- Prove2me | solution 1 for FinMarkup.Wedge.eq_A8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:32:35.440367+00:00
-- url     : https://prove2.me/submissions/d08c3918-54db-448f-8b6f-5766e4b318cc

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

open FinMarkup.Wedge in
theorem solution (m : Params) (hS : m.Standing) (mu nu : ℝ)
    (hmu : 0 ≤ mu) (hnu : 0 < nu) :
    markup m (m.eta / (m.eta - 1) * (m.R / m.A) -
      m.beta * m.eta / (m.eta - 1) * (mu / nu)) =
      m.eta / (m.eta - 1) * (1 - wedge m mu nu) := by
  obtain ⟨h1, h2, _, hA, hR⟩ := hS
  have he : m.eta - 1 ≠ 0 := by linarith
  unfold markup wedge
  field_simp <;> ring_nf

