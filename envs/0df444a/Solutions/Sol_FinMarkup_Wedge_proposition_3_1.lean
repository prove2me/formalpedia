-- Prove2me | solution 1 for FinMarkup.Wedge.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:20:33.091179+00:00
-- url     : https://prove2.me/submissions/5372c680-49ad-4e85-9472-4123e17c4bb8

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

open FinMarkup.Wedge

namespace FinMarkupProp31Sol

/-- Bernoulli-type key inequality: for `η > 1`, `t > 0`, `t ≠ 1`,
`η t^(1-η) - (η-1) t^(-η) < 1`. -/
lemma key_ineq {η t : ℝ} (hη : 1 < η) (ht : 0 < t) (ht1 : t ≠ 1) :
    η * t ^ (1 - η) - (η - 1) * t ^ (-η) < 1 := by
  have hη1 : 0 < η - 1 := by linarith
  set x := t ^ (1 - η) with hx
  have hq : 1 < η / (η - 1) := by rw [lt_div_iff₀ hη1]; linarith
  have htx : t ^ (-η) = x ^ (η / (η - 1)) := by
    rw [hx, ← Real.rpow_mul ht.le]; congr 1; field_simp; ring
  have hx1 : x ≠ 1 := by
    intro h
    apply ht1
    have := Real.rpow_rpow_inv ht.le (show (1 - η) ≠ 0 by linarith)
    rw [← hx, h, Real.one_rpow] at this
    exact this.symm
  have hxpos : 0 < x := Real.rpow_pos_of_pos ht _
  have hb := one_add_mul_self_lt_rpow_one_add (s := x - 1) (by linarith)
    (sub_ne_zero.mpr hx1) hq
  rw [show (1:ℝ) + (x - 1) = x by ring] at hb
  rw [htx]
  have hid : (η - 1) * (1 + η / (η - 1) * (x - 1)) = η * x - 1 := by
    field_simp; ring
  have := mul_lt_mul_of_pos_left hb hη1
  linarith

/-- The reduced objective `(p - d) p^(-η)` is uniquely maximized at `a = η d/(η-1)`. -/
lemma obj_lt {η d p : ℝ} (hη : 1 < η) (hd : 0 < d) (hp : 0 < p)
    (hne : p ≠ η * d / (η - 1)) :
    (p - d) * p ^ (-η) < (η * d / (η - 1) - d) * (η * d / (η - 1)) ^ (-η) := by
  have hη1 : 0 < η - 1 := by linarith
  set a := η * d / (η - 1) with ha_def
  have ha : 0 < a := div_pos (mul_pos (by linarith) hd) hη1
  have hda : d = a * (η - 1) / η := by rw [ha_def]; field_simp
  set t := p / a with ht_def
  have ht : 0 < t := div_pos hp ha
  have ht1 : t ≠ 1 := by
    intro h; apply hne; rw [ht_def, div_eq_one_iff_eq ha.ne'] at h; exact h
  have hpt : p = a * t := by rw [ht_def]; field_simp
  have hkey := key_ineq hη ht ht1
  have hA : 0 < a ^ (-η) := Real.rpow_pos_of_pos ha _
  have htt : t * t ^ (-η) = t ^ (1 - η) := by
    rw [show (1:ℝ) - η = 1 + -η by ring, Real.rpow_add ht, Real.rpow_one]
  have hLHS : (p - d) * p ^ (-η) = a ^ (-η) * (a * t ^ (1 - η) - d * t ^ (-η)) := by
    rw [hpt, Real.mul_rpow ha.le ht.le, ← htt]; ring
  rw [hLHS]
  have hη0 : 0 < η := by linarith
  have h2 : a * t ^ (1 - η) - d * t ^ (-η) < a - d := by
    rw [hda]
    have h3 : a * t ^ (1 - η) - a * (η - 1) / η * t ^ (-η)
        = (a / η) * (η * t ^ (1 - η) - (η - 1) * t ^ (-η)) := by field_simp
    have h4 : a - a * (η - 1) / η = (a / η) * 1 := by field_simp; ring
    rw [h3, h4]
    exact mul_lt_mul_of_pos_left hkey (div_pos ha hη0)
  have := mul_lt_mul_of_pos_left h2 hA
  linarith

end FinMarkupProp31Sol

open FinMarkupProp31Sol in
theorem solution (m : Params) (hS : m.Standing) (Pt M W mu nu : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hmu : 0 ≤ mu) (hnu : 0 < nu)
    (hΩ : wedge m mu nu < 1) :
    0 ≤ wedge m mu nu ∧
    ∀ p : ℝ, 0 < p →
      (IsOptimalPrice m Pt M W mu nu p ↔
        markup m p = m.eta / (m.eta - 1) * (1 - wedge m mu nu)) := by
  obtain ⟨heps1, hepseta, hbeta, hA, hR⟩ := hS
  have hη : 1 < m.eta := by linarith
  have hη1 : 0 < m.eta - 1 := by linarith
  have hcpos : 0 < m.R / m.A := div_pos hR hA
  have hΩnn : 0 ≤ wedge m mu nu := by
    unfold wedge
    exact mul_nonneg (div_nonneg (mul_nonneg hbeta hA.le) hR.le) (div_nonneg hmu hnu.le)
  refine ⟨hΩnn, ?_⟩
  set c := m.R / m.A with hc
  set Ω := wedge m mu nu with hΩdef
  set d := c * (1 - Ω) with hd_def
  have hd : 0 < d := mul_pos hcpos (by linarith)
  set a := m.eta * d / (m.eta - 1) with ha_def
  have ha : 0 < a := div_pos (mul_pos (by linarith) hd) hη1
  set K := Pt ^ (m.eta - m.eps) * M with hK_def
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos hPt _) hM
  set C := -(mu * m.rho * M) + nu * ((m.r - m.lam) * W) with hC_def
  have hmu_d : mu * m.beta = nu * (c - d) := by
    rw [hd_def, hΩdef, hc]; unfold wedge
    field_simp
    ring
  have hH : ∀ q, 0 < q →
      hamiltonian m Pt M W mu nu q = K * nu * ((q - d) * q ^ (-m.eta)) + C := by
    intro q hq
    have h1 : (q / Pt) ^ (-m.eta) * Pt ^ (-m.eps) = q ^ (-m.eta) * Pt ^ (m.eta - m.eps) := by
      rw [Real.div_rpow hq.le hPt.le, show m.eta - m.eps = -m.eps - (-m.eta) by ring,
        Real.rpow_sub hPt]
      ring
    simp only [hamiltonian, driftM, driftW, demand, hK_def, hC_def]
    rw [← hc]
    linear_combination (mu * m.beta * M) * h1 +
      (M * q ^ (-m.eta) * Pt ^ (m.eta - m.eps)) * hmu_d
  have hstrict : ∀ q, 0 < q → q ≠ a →
      hamiltonian m Pt M W mu nu q < hamiltonian m Pt M W mu nu a := by
    intro q hq hqa
    rw [hH q hq, hH a ha]
    have := mul_lt_mul_of_pos_left (obj_lt hη hd hq hqa) (mul_pos hK hnu)
    linarith
  have hac : a / c = m.eta / (m.eta - 1) * (1 - Ω) := by
    rw [ha_def, hd_def]; field_simp
  intro p hp
  have hmk : markup m p = m.eta / (m.eta - 1) * (1 - Ω) ↔ p = a := by
    unfold markup
    rw [← hc, ← hac]
    exact div_left_inj' hcpos.ne'
  rw [hmk]
  constructor
  · rintro ⟨_, hopt⟩
    by_contra hne
    have h1 := hopt a ha
    have h2 := hstrict p hp hne
    linarith
  · intro h
    rw [h]
    refine ⟨ha, fun q hq => ?_⟩
    rcases eq_or_ne q a with hqa | hqa
    · rw [hqa]
    · exact (hstrict q hq hqa).le
