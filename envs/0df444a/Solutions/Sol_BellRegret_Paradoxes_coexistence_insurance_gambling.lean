-- Prove2me | solution 1 for BellRegret.Paradoxes.coexistence_insurance_gambling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:54:38.843988+00:00
-- url     : https://prove2.me/submissions/85f6fa19-e7d0-4903-bf68-7763d865b28b

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

open BellRegret.Paradoxes in
theorem bell_key (f : ℝ → ℝ) (hf : DecreasinglyConcave f) :
    StrictConvexOn ℝ (Set.Ici (0:ℝ)) (fun r => f r - f (-r)) := by
  obtain ⟨h1, h2, h3⟩ := hf
  have hd : ∀ r, HasDerivAt (fun r => f r - f (-r)) (deriv f r + deriv f (-r)) r := by
    intro r
    have a := (h1 r).hasDerivAt
    have b : HasDerivAt (fun r => f (-r)) (deriv f (-r) * (-1)) r :=
      HasDerivAt.comp r (h1 (-r)).hasDerivAt (hasDerivAt_neg r)
    exact (a.sub b).congr_deriv (by ring)
  have hdd : ∀ r, HasDerivAt (fun r => deriv f r + deriv f (-r))
      (deriv (deriv f) r - deriv (deriv f) (-r)) r := by
    intro r
    have a := (h2 r).hasDerivAt
    have b : HasDerivAt (fun r => deriv f (-r)) (deriv (deriv f) (-r) * (-1)) r :=
      HasDerivAt.comp r (h2 (-r)).hasDerivAt (hasDerivAt_neg r)
    exact (a.add b).congr_deriv (by ring)
  have hder : deriv (fun r => f r - f (-r)) = fun r => deriv f r + deriv f (-r) := by
    funext r; exact (hd r).deriv
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0)
  · exact fun r _ => (hd r).continuousAt.continuousWithinAt
  · rw [hder, interior_Ici]
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun r _ => (hdd r).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Ioi] at hr
      rw [(hdd r).deriv]
      have : -r < r := by simp at hr; linarith
      have := h3 this
      linarith

open BellRegret.Paradoxes in
theorem bell_ineq (f : ℝ → ℝ) (hf : DecreasinglyConcave f) (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    p * f (p - 1) + (1 - p) * f p < p * f (1 - p) + (1 - p) * f (-p) := by
  have hc := bell_key f hf
  have hq : 0 < 1 - p := by linarith
  have hpq : p < 1 - p := by linarith
  -- p = (p/q) q + (1 - p/q) 0
  have ha : 0 < p / (1 - p) := div_pos hp0 hq
  have hb : 0 < 1 - p / (1 - p) := by
    have : p / (1 - p) < 1 := (div_lt_one hq).2 hpq
    linarith
  have key := hc.2 (x := 1 - p) (y := 0) (Set.mem_Ici.2 hq.le) (Set.mem_Ici.2 le_rfl)
    (by intro h; linarith) ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, neg_zero] at key
  have e : p / (1 - p) * (1 - p) = p := by field_simp
  rw [e] at key
  have key2 : (1 - p) * (f p - f (-p)) < p * (f (1 - p) - f (-(1 - p))) := by
    have := mul_lt_mul_of_pos_left key hq
    have e2 : (1 - p) * (p / (1 - p) * (f (1 - p) - f (-(1 - p)))) = p * (f (1 - p) - f (-(1 - p))) := by
      field_simp
    linarith
  have e3 : -(1 - p) = p - 1 := by ring
  rw [e3] at key2
  nlinarith [key2]

open BellRegret.Paradoxes in
theorem solution (f : ℝ → ℝ) (hf : DecreasinglyConcave f)
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    Prefers f (prob2 p) (horseBet p) horseNoBet ∧
      Prefers f (prob2 p) (carInsure p) carNoInsure := by
  have h := bell_ineq f hf p hp0 hp
  constructor <;>
  · simp [Prefers, selectU, regretU, prob2, horseBet, horseNoBet, carInsure, carNoInsure, Fin.sum_univ_two]
    have e1 : -p + 1 = 1 - p := by ring
    have e2 : -1 + p = p - 1 := by ring
    try rw [e1]
    try rw [e2]
    nlinarith [h]
