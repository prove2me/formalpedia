-- Prove2me | solution 1 for FinMarkup.Wedge.eq_A5_A6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:41:16.225056+00:00
-- url     : https://prove2.me/submissions/c88179f5-80e1-4e02-bdbb-318e7e1260da

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model
set_option autoImplicit false

open FinMarkup.Wedge

theorem solution (m : Params) (hS : m.Standing) (Pt M mu nu p : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hmu : 0 ≤ mu) (hnu : 0 < nu) (hp : 0 < p) :
    mu * (-(m.beta * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps) * M)) +
      nu * ((p ^ (-m.eta) * Pt ^ (m.eta - m.eps) -
        (p - m.R / m.A) * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps)) * M) = 0 ↔
    p = m.eta / (m.eta - 1) * (m.R / m.A) -
      m.beta * m.eta / (m.eta - 1) * (mu / nu) := by
  obtain ⟨h1, h2, -, -, -⟩ := hS
  have hη : 0 < m.eta - 1 := by linarith
  have e : p ^ (-m.eta) = p ^ (-m.eta - 1) * p := by
    rw [← Real.rpow_add_one hp.ne']; ring_nf
  set a := p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps) * M with ha
  have hapos : 0 < a := by positivity
  have key : mu * (-(m.beta * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps) * M)) +
      nu * ((p ^ (-m.eta) * Pt ^ (m.eta - m.eps) -
        (p - m.R / m.A) * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps)) * M)
      = a * (-(mu * m.beta * m.eta) + nu * (p - (p - m.R / m.A) * m.eta)) := by
    rw [e, ha]; ring
  rw [key, mul_eq_zero]
  simp only [hapos.ne', false_or]
  constructor
  · intro h
    field_simp
    linear_combination (-1 : ℝ) * h
  · intro h
    rw [h]
    field_simp
    ring
