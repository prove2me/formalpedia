-- Prove2me | solution 1 for CompOpacity.Disclosure.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:10:19.787206+00:00
-- url     : https://prove2.me/submissions/3e07d304-5149-406a-9b9a-d57a9b399235

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model


namespace CompOpacity.Disclosure

/-- coefficient equations of a linear equilibrium (general a b) -/
theorem linEq_coeff_eqs (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (H : IsLinEq a b q n thetaBar m s) (i : Fin 2) :
    let d := m i + n + q
    let d' := m i.rev + n + q
    let K := 1 + a * s.beta i + a * b ^ 2 * s.lam i.rev
    let K' := 1 + a * s.lam i + a * s.beta i.rev
    s.beta i = K * n / d ∧ b * s.lam i = b * K' * n / d' ∧
    s.gamma i = K * m i / d + a * s.gamma i + a * b ^ 2 * s.omega i.rev ∧
    b * s.omega i = b * K' * m i.rev / d' + a * b * s.omega i + a * b * s.gamma i.rev ∧
    s.h i = K * q * thetaBar / d - b * K' * q * thetaBar / d' + a * s.h i - a * b * s.h i.rev := by
  intro d d' K K'
  have r0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have r1 : Fin.rev (1 : Fin 2) = 0 := rfl
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have c0 := H ![0,0] ![0,0] 0
    have c1 := H ![0,0] ![1,0] 0
    have c2 := H ![0,0] ![0,1] 0
    have c3 := H ![1,0] ![0,0] 0
    have c4 := H ![0,1] ![0,0] 0
    simp [invest, expK, postMean, r0, r1] at c0 c1 c2 c3 c4
    simp only [d, d', K, K', r0, r1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination c1 - c0
    · linear_combination c0 - c2
    · linear_combination c3 - c0
    · linear_combination c0 - c4
    · linear_combination c0
  · have c0 := H ![0,0] ![0,0] 1
    have c1 := H ![0,0] ![0,1] 1
    have c2 := H ![0,0] ![1,0] 1
    have c3 := H ![0,1] ![0,0] 1
    have c4 := H ![1,0] ![0,0] 1
    simp [invest, expK, postMean, r0, r1] at c0 c1 c2 c3 c4
    simp only [d, d', K, K', r0, r1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination c1 - c0
    · linear_combination c0 - c2
    · linear_combination c3 - c0
    · linear_combination c0 - c4
    · linear_combination c0

theorem linEq_of_coeff_eqs (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (H : ∀ i : Fin 2,
    s.beta i = (1 + a * s.beta i + a * b ^ 2 * s.lam i.rev) * n / (m i + n + q) ∧
    b * s.lam i = b * (1 + a * s.lam i + a * s.beta i.rev) * n / (m i.rev + n + q) ∧
    s.gamma i = (1 + a * s.beta i + a * b ^ 2 * s.lam i.rev) * m i / (m i + n + q)
      + a * s.gamma i + a * b ^ 2 * s.omega i.rev ∧
    b * s.omega i = b * (1 + a * s.lam i + a * s.beta i.rev) * m i.rev / (m i.rev + n + q)
      + a * b * s.omega i + a * b * s.gamma i.rev ∧
    s.h i = (1 + a * s.beta i + a * b ^ 2 * s.lam i.rev) * q * thetaBar / (m i + n + q)
      - b * (1 + a * s.lam i + a * s.beta i.rev) * q * thetaBar / (m i.rev + n + q)
      + a * s.h i - a * b * s.h i.rev) :
    IsLinEq a b q n thetaBar m s := by
  intro z x i
  obtain ⟨e1, e2, e3, e4, e5⟩ := H i
  simp only [invest, expK, postMean]
  have r0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have r1 : Fin.rev (1 : Fin 2) = 0 := rfl
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · simp only [r0, r1] at *
    linear_combination (x 0) * e1 - (x 1) * e2 + (z 0) * e3 - (z 1) * e4 + e5
  · simp only [r0, r1] at *
    linear_combination (x 1) * e1 - (x 0) * e2 + (z 1) * e3 - (z 0) * e4 + e5

theorem linEq1_unique (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j)
    (H : IsLinEq a 1 q n thetaBar m s) (i : Fin 2) :
    s.beta i = n / (q + m i + (1 - 2 * a) * n) ∧
    s.lam i.rev = n / (q + m i + (1 - 2 * a) * n) ∧
    s.gamma i = m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n)) ∧
    s.omega i.rev = m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n)) ∧
    s.h i = q * thetaBar / (1 - 2 * a) *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n)) := by
  have A := linEq_coeff_eqs a 1 q n thetaBar m s H i
  have B := linEq_coeff_eqs a 1 q n thetaBar m s H i.rev
  simp only [Fin.rev_rev, one_pow, mul_one, one_mul] at A B
  obtain ⟨a1, a2, a3, a4, a5⟩ := A
  obtain ⟨b1, b2, b3, b4, b5⟩ := B
  have hd : 0 < m i + n + q := by linarith [hm i]
  have hd' : 0 < m i.rev + n + q := by linarith [hm i.rev]
  have hw : 0 < 1 - 2 * a := by linarith
  have hE : 0 < q + m i + (1 - 2 * a) * n := by nlinarith [hm i]
  have hE' : 0 < q + m i.rev + (1 - 2 * a) * n := by nlinarith [hm i.rev]
  have hE0 : q + m i + (1 - 2 * a) * n ≠ 0 := hE.ne'
  have hE0' : q + m i.rev + (1 - 2 * a) * n ≠ 0 := hE'.ne'
  have hd0 : m i + n + q ≠ 0 := hd.ne'
  have hd0' : m i.rev + n + q ≠ 0 := hd'.ne'
  have kk : ∀ t : ℝ, 0 ≤ t → (1 + 2 * a * (n / (q + t + (1 - 2 * a) * n))) / (t + n + q)
        = 1 / (q + t + (1 - 2 * a) * n) := by
    intro t ht
    have h1 : q + t + (1 - 2 * a) * n ≠ 0 := by nlinarith
    have h2 : t + n + q ≠ 0 := by linarith
    field_simp; ring
  -- beta / lambda
  have hbl : s.beta i = s.lam i.rev := by linear_combination a1 - b2
  have hbl' : s.beta i.rev = s.lam i := by linear_combination b1 - a2
  have hβ : s.beta i = n / (q + m i + (1 - 2 * a) * n) := by
    rw [eq_div_iff hE.ne']
    rw [← hbl] at a1
    field_simp at a1
    linear_combination a1
  have hβ' : s.beta i.rev = n / (q + m i.rev + (1 - 2 * a) * n) := by
    rw [eq_div_iff hE'.ne']
    rw [← hbl'] at b1
    field_simp at b1
    linear_combination b1
  -- gamma / omega
  have hgo : s.gamma i = s.omega i.rev := by
    rw [← hbl] at a3 b4
    linear_combination a3 - b4
  have hγ : s.gamma i = m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n)) := by
    have k1 : s.gamma i * (1 - 2 * a) = (1 + 2 * a * s.beta i) * m i / (m i + n + q) := by
      rw [← hbl, ← hgo] at a3; linear_combination a3
    rw [hβ] at k1
    have k2 := kk (m i) (hm i)
    rw [mul_div_right_comm, k2] at k1
    rw [eq_div_iff (by positivity)]
    field_simp at k1
    linear_combination k1
  have hgo' : s.gamma i.rev = s.omega i := by
    rw [← hbl'] at b3 a4
    linear_combination b3 - a4
  have hγ' : s.gamma i.rev = m i.rev / ((1 - 2 * a) * (q + m i.rev + (1 - 2 * a) * n)) := by
    have k1 : s.gamma i.rev * (1 - 2 * a) = (1 + 2 * a * s.beta i.rev) * m i.rev / (m i.rev + n + q) := by
      rw [← hbl', ← hgo'] at b3; linear_combination b3
    rw [hβ'] at k1
    have k2 := kk (m i.rev) (hm i.rev)
    rw [mul_div_right_comm, k2] at k1
    rw [eq_div_iff (by positivity)]
    field_simp at k1
    linear_combination k1
  refine ⟨hβ, hbl ▸ hβ, hγ, hgo ▸ hγ, ?_⟩
  have a5' : s.h i * (1 - a) + a * s.h i.rev = q * thetaBar *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n)) := by
    rw [← hbl, ← hbl', hβ, hβ'] at a5
    rw [← kk (m i) (hm i), ← kk (m i.rev) (hm i.rev)]
    linear_combination a5
  have b5' : s.h i.rev * (1 - a) + a * s.h i = q * thetaBar *
      (1 / (q + m i.rev + (1 - 2 * a) * n) - 1 / (q + m i + (1 - 2 * a) * n)) := by
    rw [← hbl, ← hbl', hβ, hβ'] at b5
    rw [← kk (m i) (hm i), ← kk (m i.rev) (hm i.rev)]
    linear_combination b5
  have hw0 : 1 - 2 * a ≠ 0 := hw.ne'
  have : s.h i * (1 - 2 * a) = q * thetaBar *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n)) := by
    linear_combination (1 - a) * a5' - a * b5'
  rw [div_mul_eq_mul_div, ← this]; field_simp

/-- explicit equilibrium at b = 1 -/
noncomputable def sS (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => n / (q + m i + (1 - 2 * a) * n)
  lam := fun i => n / (q + m i.rev + (1 - 2 * a) * n)
  gamma := fun i => m i / ((1 - 2 * a) * (q + m i + (1 - 2 * a) * n))
  omega := fun i => m i.rev / ((1 - 2 * a) * (q + m i.rev + (1 - 2 * a) * n))
  h := fun i => q * thetaBar / (1 - 2 * a) *
      (1 / (q + m i + (1 - 2 * a) * n) - 1 / (q + m i.rev + (1 - 2 * a) * n))

theorem sS_isLinEq (a q n thetaBar : ℝ) (m : Fin 2 → ℝ)
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    IsLinEq a 1 q n thetaBar m (sS a q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hw : 0 < 1 - 2 * a := by linarith
  have hE : q + m i + (1 - 2 * a) * n ≠ 0 := by nlinarith [hm i]
  have hE' : q + m i.rev + (1 - 2 * a) * n ≠ 0 := by nlinarith [hm i.rev]
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hd0' : m i.rev + n + q ≠ 0 := by linarith [hm i.rev]
  have hw0 : 1 - 2 * a ≠ 0 := hw.ne'
  have x1 : m i + n - n * a * 2 + q ≠ 0 := by contrapose! hE; linear_combination hE
  have x2 : m i.rev + n - n * a * 2 + q ≠ 0 := by contrapose! hE'; linear_combination hE'
  simp only [sS, Fin.rev_rev, one_pow, mul_one, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring_nf <;> field_simp <;> ring

/-- explicit equilibrium at b = 0 -/
noncomputable def sNC (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => n / (q + m i + (1 - a) * n)
  lam := fun _ => 0
  gamma := fun i => m i / ((1 - a) * (q + m i + (1 - a) * n))
  omega := fun _ => 0
  h := fun i => q * thetaBar / ((1 - a) * (q + m i + (1 - a) * n))

theorem sNC_isLinEq (a q n thetaBar : ℝ) (m : Fin 2 → ℝ)
    (ha0 : 0 ≤ a) (ha : a < 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    IsLinEq a 0 q n thetaBar m (sNC a q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hw : 0 < 1 - a := by linarith
  have hE : q + m i + (1 - a) * n ≠ 0 := by nlinarith [hm i]
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hw0 : 1 - a ≠ 0 := hw.ne'
  have x1 : m i + n - n * a + q ≠ 0 := by contrapose! hE; linear_combination hE
  simp only [sNC]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring_nf <;> field_simp <;> ring

theorem linEq0_unique (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (ha0 : 0 ≤ a) (ha : a < 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j)
    (H : IsLinEq a 0 q n thetaBar m s) (i : Fin 2) :
    s.beta i = n / (q + m i + (1 - a) * n) ∧
    s.gamma i = m i / ((1 - a) * (q + m i + (1 - a) * n)) ∧
    s.h i = q * thetaBar / ((1 - a) * (q + m i + (1 - a) * n)) := by
  obtain ⟨a1, -, a3, -, a5⟩ := linEq_coeff_eqs a 0 q n thetaBar m s H i
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_pow two_ne_zero, zero_div] at a1 a3 a5
  have hw : 0 < 1 - a := by linarith
  have hE : q + m i + (1 - a) * n ≠ 0 := by nlinarith [hm i]
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hw0 : 1 - a ≠ 0 := hw.ne'
  have x1 : m i + n - n * a + q ≠ 0 := by contrapose! hE; linear_combination hE
  have hβ : s.beta i = n / (q + m i + (1 - a) * n) := by
    rw [eq_div_iff hE]; field_simp at a1; linear_combination a1
  have kk : (1 + a * s.beta i) / (m i + n + q) = 1 / (q + m i + (1 - a) * n) := by
    rw [hβ, div_eq_div_iff hd0 hE, add_mul, mul_assoc, div_mul_cancel₀ _ hE]; ring
  refine ⟨hβ, ?_, ?_⟩
  · have : s.gamma i * (1 - a) = (1 + a * s.beta i) / (m i + n + q) * m i := by
      linear_combination a3
    rw [kk] at this
    rw [eq_div_iff (by positivity)]; field_simp at this; linear_combination this
  · have : s.h i * (1 - a) = (1 + a * s.beta i) / (m i + n + q) * (q * thetaBar) := by
      linear_combination a5
    rw [kk] at this
    rw [eq_div_iff (by positivity)]; field_simp at this; linear_combination this

/-- explicit equilibrium at a = 0 -/
noncomputable def sZ (b q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => n / (m i + n + q)
  lam := fun i => n / (m i.rev + n + q)
  gamma := fun i => m i / (m i + n + q)
  omega := fun i => m i.rev / (m i.rev + n + q)
  h := fun i => q * thetaBar / (m i + n + q) - b * (q * thetaBar / (m i.rev + n + q))

theorem sZ_isLinEq (b q n thetaBar : ℝ) (m : Fin 2 → ℝ)
    (hq : 0 < q) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    IsLinEq 0 b q n thetaBar m (sZ b q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hd0 : m i + n + q ≠ 0 := by linarith [hm i]
  have hd0' : m i.rev + n + q ≠ 0 := by linarith [hm i.rev]
  simp only [sZ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem linEqZ_unique (b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat)
    (hb : 0 < b) (H : IsLinEq 0 b q n thetaBar m s) (i : Fin 2) :
    s.beta i = n / (m i + n + q) ∧ s.lam i = n / (m i.rev + n + q) ∧
    s.gamma i = m i / (m i + n + q) ∧ s.omega i = m i.rev / (m i.rev + n + q) ∧
    s.h i = q * thetaBar / (m i + n + q) - b * (q * thetaBar / (m i.rev + n + q)) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := linEq_coeff_eqs 0 b q n thetaBar m s H i
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_add, mul_one] at a1 a2 a3 a4 a5
  refine ⟨by rw [a1]; ring, ?_, by rw [a3]; ring, ?_, by rw [a5]; ring⟩
  · have := a2; rw [mul_div_assoc] at this
    exact mul_left_cancel₀ hb.ne' this
  · have := a4; rw [mul_div_assoc] at this
    exact mul_left_cancel₀ hb.ne' this

end CompOpacity.Disclosure


namespace CompOpacity.Disclosure

lemma blk_id (a b c : ℝ) (hdet : (1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2 ≠ 0) :
    1 + a * c * ((1 - a * c + a * b ^ 2 * c) / ((1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2))
      + a * b ^ 2 * c * (1 / ((1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2))
      = (1 - a * c + a * b ^ 2 * c) / ((1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2) ∧
    1 + a * c * (1 / ((1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2))
      + a * c * ((1 - a * c + a * b ^ 2 * c) / ((1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2))
      = 1 / ((1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2) := by
  generalize hd : (1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2 = D at hdet ⊢
  constructor <;> field_simp <;> rw [← hd] <;> ring

lemma zblk_id (a b K K' e : ℝ) (hD : (1 - a) ^ 2 - a ^ 2 * b ^ 2 ≠ 0) :
    e * ((1 - a) * K + a * b ^ 2 * K') / ((1 - a) ^ 2 - a ^ 2 * b ^ 2)
      = K * e + a * (e * ((1 - a) * K + a * b ^ 2 * K') / ((1 - a) ^ 2 - a ^ 2 * b ^ 2))
        + a * b ^ 2 * (e * ((1 - a) * K' + a * K) / ((1 - a) ^ 2 - a ^ 2 * b ^ 2)) ∧
    e * ((1 - a) * K' + a * K) / ((1 - a) ^ 2 - a ^ 2 * b ^ 2)
      = K' * e + a * (e * ((1 - a) * K' + a * K) / ((1 - a) ^ 2 - a ^ 2 * b ^ 2))
        + a * (e * ((1 - a) * K + a * b ^ 2 * K') / ((1 - a) ^ 2 - a ^ 2 * b ^ 2)) := by
  generalize hd : (1 - a) ^ 2 - a ^ 2 * b ^ 2 = D at hD ⊢
  constructor <;> field_simp <;> rw [← hd] <;> ring

noncomputable def ccP (q n : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) : ℝ := n / (m i + n + q)
noncomputable def eeP (q n : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) : ℝ := m i / (m i + n + q)
noncomputable def dtP (a b c : ℝ) : ℝ := (1 - a * c) ^ 2 - a ^ 2 * b ^ 2 * c ^ 2
noncomputable def KKP (a b c : ℝ) : ℝ := (1 - a * c + a * b ^ 2 * c) / dtP a b c
noncomputable def KPP (a b c : ℝ) : ℝ := 1 / dtP a b c
noncomputable def D2P (a b : ℝ) : ℝ := (1 - a) ^ 2 - a ^ 2 * b ^ 2

noncomputable def gP (a b c : ℝ) : ℝ := ((1 - a) * KKP a b c + a * b ^ 2 * KPP a b c) / D2P a b
noncomputable def oP (a b c : ℝ) : ℝ := ((1 - a) * KPP a b c + a * KKP a b c) / D2P a b

noncomputable def sP (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) : LinStrat where
  beta := fun i => ccP q n m i * KKP a b (ccP q n m i)
  lam := fun i => ccP q n m i.rev * KPP a b (ccP q n m i.rev)
  gamma := fun i => eeP q n m i * gP a b (ccP q n m i)
  omega := fun i => eeP q n m i.rev * oP a b (ccP q n m i.rev)
  h := fun i => (gP a b (ccP q n m i) / (m i + n + q)
      - b * oP a b (ccP q n m i.rev) / (m i.rev + n + q)) * q * thetaBar

lemma ccP_bounds (q n : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) (hq : 0 < q) (hn : 0 < n) (hm : 0 ≤ m i) :
    0 < ccP q n m i ∧ ccP q n m i < 1 := by
  unfold ccP
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

lemma dtP_pos (a b c : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b ≤ 1)
    (hc0 : 0 < c) (hc : c < 1) : 0 < dtP a b c := by
  unfold dtP
  have h1 : a * b * c ≤ a * c := by
    have : 0 ≤ a * c := by positivity
    nlinarith
  have h2 : a * c < 1 / 2 := by nlinarith
  have h3 : 0 ≤ a * b * c := by positivity
  nlinarith

lemma D2P_pos (a b : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b ≤ 1) :
    0 < D2P a b := by
  unfold D2P
  have : a * b ≤ a := by nlinarith
  have : 0 ≤ a * b := by positivity
  nlinarith

lemma blk_def (a b c : ℝ) (h : dtP a b c ≠ 0) :
    1 + a * c * KKP a b c + a * b ^ 2 * c * KPP a b c = KKP a b c ∧
    1 + a * c * KPP a b c + a * c * KKP a b c = KPP a b c := by
  unfold KKP KPP; unfold dtP at *; exact blk_id a b c h

lemma zblk_def (a b K K' e : ℝ) (hD : D2P a b ≠ 0) :
    e * ((1 - a) * K + a * b ^ 2 * K') / D2P a b
      = K * e + a * (e * ((1 - a) * K + a * b ^ 2 * K') / D2P a b)
        + a * b ^ 2 * (e * ((1 - a) * K' + a * K) / D2P a b) ∧
    e * ((1 - a) * K' + a * K) / D2P a b
      = K' * e + a * (e * ((1 - a) * K' + a * K) / D2P a b)
        + a * (e * ((1 - a) * K + a * b ^ 2 * K') / D2P a b) := by
  unfold D2P at *; exact zblk_id a b K K' e hD

lemma zblk_g (a b c : ℝ) (hD : D2P a b ≠ 0) :
    gP a b c = KKP a b c + a * gP a b c + a * b ^ 2 * oP a b c ∧
    oP a b c = KPP a b c + a * oP a b c + a * gP a b c := by
  have := zblk_def a b (KKP a b c) (KPP a b c) 1 hD
  simp only [one_mul, mul_one] at this
  exact this

theorem sP_isLinEq (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ i, 0 < m i) :
    IsLinEq a b q n thetaBar m (sP a b q n thetaBar m) := by
  apply linEq_of_coeff_eqs
  intro i
  have hdt : ∀ k, dtP a b (ccP q n m k) ≠ 0 := fun k => by
    obtain ⟨h1, h2⟩ := ccP_bounds q n m k hq hn (hm k).le
    exact (dtP_pos a b _ ha0 ha hb0 hb h1 h2).ne'
  have hD2 : D2P a b ≠ 0 := (D2P_pos a b ha0 ha hb0 hb).ne'
  have B := fun k => blk_def a b (ccP q n m k) (hdt k)
  have Z := fun k => zblk_g a b (ccP q n m k) hD2
  have hcc : ∀ k, n / (m k + n + q) = ccP q n m k := fun k => rfl
  have hee : ∀ k, m k / (m k + n + q) = eeP q n m k := fun k => rfl
  obtain ⟨B1, B2⟩ := B i
  obtain ⟨B1', B2'⟩ := B i.rev
  obtain ⟨Z1, Z2⟩ := Z i
  obtain ⟨Z1', Z2'⟩ := Z i.rev
  simp only [sP, Fin.rev_rev, mul_div_assoc, hcc, hee]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-(ccP q n m i)) * B1
  · linear_combination (-(b * ccP q n m i.rev)) * B2'
  · linear_combination (eeP q n m i) * Z1 - (eeP q n m i) * B1
  · linear_combination (b * eeP q n m i.rev) * Z2' - (b * eeP q n m i.rev) * B2'
  · linear_combination (q * thetaBar / (m i + n + q)) * (Z1 - B1)
      - (b * q * thetaBar / (m i.rev + n + q)) * (Z2' - B2')

theorem LinStrat_ext {s t : LinStrat} (h1 : s.beta = t.beta) (h2 : s.gamma = t.gamma)
    (h3 : s.lam = t.lam) (h4 : s.omega = t.omega) (h5 : s.h = t.h) : s = t := by
  cases s; cases t; simp_all

theorem sP_unique (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1) (hq : 0 < q) (hn : 0 < n) (hm : ∀ i, 0 < m i)
    (s : LinStrat) (H : IsLinEq a b q n thetaBar m s) : s = sP a b q n thetaBar m := by
  have hdt : ∀ k, 0 < dtP a b (ccP q n m k) := fun k => by
    obtain ⟨h1, h2⟩ := ccP_bounds q n m k hq hn (hm k).le
    exact dtP_pos a b _ ha0 ha hb0 hb h1 h2
  have hD2 : 0 < D2P a b := D2P_pos a b ha0 ha hb0 hb
  have hcc : ∀ k, n / (m k + n + q) = ccP q n m k := fun k => rfl
  have hee : ∀ k, m k / (m k + n + q) = eeP q n m k := fun k => rfl
  have hb' : b ≠ 0 := hb0.ne'
  -- block equations
  have blkE : ∀ i : Fin 2, s.beta i = ccP q n m i * KKP a b (ccP q n m i) ∧
      s.lam i.rev = ccP q n m i * KPP a b (ccP q n m i) := by
    intro i
    obtain ⟨A1, -, -, -, -⟩ := linEq_coeff_eqs a b q n thetaBar m s H i
    obtain ⟨-, B2, -, -, -⟩ := linEq_coeff_eqs a b q n thetaBar m s H i.rev
    simp only [Fin.rev_rev] at B2
    rw [mul_div_assoc, hcc] at A1
    rw [mul_div_assoc, hcc, mul_assoc] at B2
    have B2' := mul_left_cancel₀ hb' B2
    set c := ccP q n m i
    have hd := (hdt i).ne'
    unfold KKP KPP
    constructor
    · rw [mul_div_assoc', eq_div_iff hd]
      unfold dtP
      linear_combination (1 - a * c) * A1 + a * b ^ 2 * c * B2'
    · rw [mul_div_assoc', eq_div_iff hd]
      unfold dtP
      linear_combination a * c * A1 + (1 - a * c) * B2'
  have hbeta : ∀ i, s.beta i = ccP q n m i * KKP a b (ccP q n m i) := fun i => (blkE i).1
  have hlam : ∀ i, s.lam i = ccP q n m i.rev * KPP a b (ccP q n m i.rev) := by
    intro i; have := (blkE i.rev).2; rwa [Fin.rev_rev] at this
  have zE : ∀ i : Fin 2, s.gamma i = eeP q n m i * gP a b (ccP q n m i) ∧
      s.omega i.rev = eeP q n m i * oP a b (ccP q n m i) := by
    intro i
    obtain ⟨-, -, A3, -, -⟩ := linEq_coeff_eqs a b q n thetaBar m s H i
    obtain ⟨-, -, -, B4, -⟩ := linEq_coeff_eqs a b q n thetaBar m s H i.rev
    simp only [Fin.rev_rev] at B4
    obtain ⟨K1, K2⟩ := blk_def a b (ccP q n m i) (hdt i).ne'
    rw [hbeta i, hlam i.rev, Fin.rev_rev, mul_div_assoc, hee] at A3
    rw [hbeta i, hlam i.rev, Fin.rev_rev, mul_div_assoc, hee] at B4
    have B4' : s.omega i.rev = (1 + a * (ccP q n m i * KPP a b (ccP q n m i))
        + a * (ccP q n m i * KKP a b (ccP q n m i))) * eeP q n m i + a * s.omega i.rev
        + a * s.gamma i := by
      apply mul_left_cancel₀ hb'; linear_combination B4
    set c := ccP q n m i
    set e := eeP q n m i
    have hd := hD2.ne'
    unfold gP oP
    constructor
    · rw [mul_div_assoc', eq_div_iff hd]
      unfold D2P
      linear_combination (1 - a) * A3 + a * b ^ 2 * B4' + ((1 - a) * e) * K1 + ((a * b ^ 2) * e) * K2
    · rw [mul_div_assoc', eq_div_iff hd]
      unfold D2P
      linear_combination a * A3 + (1 - a) * B4' + (a * e) * K1 + ((1 - a) * e) * K2
  have hgam : ∀ i, s.gamma i = eeP q n m i * gP a b (ccP q n m i) := fun i => (zE i).1
  have homg : ∀ i, s.omega i = eeP q n m i.rev * oP a b (ccP q n m i.rev) := by
    intro i; have := (zE i.rev).2; rwa [Fin.rev_rev] at this
  -- h
  have sPL := sP_isLinEq a b q n thetaBar m ha0 ha hb0 hb hq hn hm
  have hh : ∀ i, s.h i = (sP a b q n thetaBar m).h i := by
    intro i
    obtain ⟨-, -, -, -, A5⟩ := linEq_coeff_eqs a b q n thetaBar m s H i
    obtain ⟨-, -, -, -, B5⟩ := linEq_coeff_eqs a b q n thetaBar m s H i.rev
    obtain ⟨-, -, -, -, P5⟩ := linEq_coeff_eqs a b q n thetaBar m _ sPL i
    obtain ⟨-, -, -, -, Q5⟩ := linEq_coeff_eqs a b q n thetaBar m _ sPL i.rev
    simp only [Fin.rev_rev] at B5 Q5
    have e1 : s.beta i = (sP a b q n thetaBar m).beta i := hbeta i
    have e2 : s.beta i.rev = (sP a b q n thetaBar m).beta i.rev := hbeta i.rev
    have e3 : s.lam i = (sP a b q n thetaBar m).lam i := hlam i
    have e4 : s.lam i.rev = (sP a b q n thetaBar m).lam i.rev := hlam i.rev
    rw [e1, e2, e3, e4] at A5 B5
    have hδ : (s.h i - (sP a b q n thetaBar m).h i) * D2P a b = 0 := by
      unfold D2P
      linear_combination (1 - a) * (A5 - P5) - a * b * (B5 - Q5)
    rcases mul_eq_zero.1 hδ with h | h
    · linarith
    · exact absurd h hD2.ne'
  apply LinStrat_ext
  · funext i; rw [hbeta i]; rfl
  · funext i; rw [hgam i]; rfl
  · funext i; rw [hlam i]; rfl
  · funext i; rw [homg i]; rfl
  · funext i; exact hh i

section mult
variable (a b c : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b ≤ 1)
  (hc0 : 0 < c) (hc : c < 1)
include ha0 ha hb0 hb hc0 hc

lemma L_kappa : 1 < KKP a b c * (1 - a * c) := by
  have hdt := dtP_pos a b c ha0 ha hb0 hb hc0 hc
  unfold KKP
  rw [div_mul_eq_mul_div, one_lt_div hdt]
  unfold dtP
  have h1 : 0 < 1 - a * c := by nlinarith
  have h2 : 0 < a * b ^ 2 * c := by positivity
  nlinarith [mul_pos h1 h2, mul_pos (mul_pos ha0 hc0) h2]

lemma L_mu : 1 < KPP a b c * (1 - a * c) := by
  have hdt := dtP_pos a b c ha0 ha hb0 hb hc0 hc
  unfold KPP
  rw [div_mul_eq_mul_div, one_mul, one_lt_div hdt]
  unfold dtP
  have h1 : 0 < 1 - a * c := by nlinarith
  have h2 : 0 < a * c := by positivity
  nlinarith [mul_pos h1 h2, sq_nonneg (a * b * c)]

lemma KKP_pos : 0 < KKP a b c := by
  have := L_kappa a b c ha0 ha hb0 hb hc0 hc
  have h1 : 0 < 1 - a * c := by nlinarith
  by_contra h; push_neg at h; nlinarith

lemma KPP_pos : 0 < KPP a b c := by
  have := L_mu a b c ha0 ha hb0 hb hc0 hc
  have h1 : 0 < 1 - a * c := by nlinarith
  by_contra h; push_neg at h; nlinarith

lemma L_nu : 1 < gP a b c * ((1 - a) * (1 - a * c)) := by
  have hD := D2P_pos a b ha0 ha hb0 hb
  have hk := L_kappa a b c ha0 ha hb0 hb hc0 hc
  have hp := KPP_pos a b c ha0 ha hb0 hb hc0 hc
  have h1 : 0 < 1 - a * c := by nlinarith
  have hv : 0 < 1 - a := by linarith
  unfold gP
  rw [div_mul_eq_mul_div, one_lt_div hD]
  unfold D2P
  have e : ((1 - a) * KKP a b c + a * b ^ 2 * KPP a b c) * ((1 - a) * (1 - a * c))
      = (1 - a) ^ 2 * (KKP a b c * (1 - a * c)) + (1 - a) * (1 - a * c) * (a * b ^ 2 * KPP a b c) := by
    ring
  rw [e]
  have : 0 < (1 - a) * (1 - a * c) * (a * b ^ 2 * KPP a b c) := by positivity
  have : (1 - a) ^ 2 < (1 - a) ^ 2 * (KKP a b c * (1 - a * c)) := by
    have : 0 < (1 - a) ^ 2 := by positivity
    nlinarith
  nlinarith [sq_nonneg (a * b)]

lemma L_chi : 1 < oP a b c * ((1 - a) * (1 - a * c)) := by
  have hD := D2P_pos a b ha0 ha hb0 hb
  have hk := L_mu a b c ha0 ha hb0 hb hc0 hc
  have hp := KKP_pos a b c ha0 ha hb0 hb hc0 hc
  have h1 : 0 < 1 - a * c := by nlinarith
  have hv : 0 < 1 - a := by linarith
  unfold oP
  rw [div_mul_eq_mul_div, one_lt_div hD]
  unfold D2P
  have e : ((1 - a) * KPP a b c + a * KKP a b c) * ((1 - a) * (1 - a * c))
      = (1 - a) ^ 2 * (KPP a b c * (1 - a * c)) + (1 - a) * (1 - a * c) * (a * KKP a b c) := by
    ring
  rw [e]
  have : 0 < (1 - a) * (1 - a * c) * (a * KKP a b c) := by positivity
  have : (1 - a) ^ 2 < (1 - a) ^ 2 * (KPP a b c * (1 - a * c)) := by
    have : 0 < (1 - a) ^ 2 := by positivity
    nlinarith
  nlinarith [sq_nonneg (a * b)]

end mult

lemma betaNC_eq (a q n t : ℝ) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (ht : 0 ≤ t) :
    n / (q + t + (1 - a) * n) = (n / (t + n + q)) / (1 - a * (n / (t + n + q))) := by
  have h1 : t + n + q ≠ 0 := by linarith
  have h2 : q + t + (1 - a) * n ≠ 0 := by nlinarith
  have h : 1 - a * (n / (t + n + q)) = (q + t + (1 - a) * n) / (t + n + q) := by
    field_simp; ring
  rw [h, div_div_div_cancel_right₀ h1]

lemma gammaNC_eq (a q n t : ℝ) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (ht : 0 ≤ t) :
    t / ((1 - a) * (q + t + (1 - a) * n))
      = (t / (t + n + q)) / ((1 - a) * (1 - a * (n / (t + n + q)))) := by
  have h1 : t + n + q ≠ 0 := by linarith
  have h : 1 - a * (n / (t + n + q)) = (q + t + (1 - a) * n) / (t + n + q) := by
    field_simp; ring
  rw [h, mul_div_assoc', div_div_div_cancel_right₀ h1]

theorem proposition_3_proof (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b ≤ 1) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hm : ∀ i, 0 < m i) : (∃! s : LinStrat, IsLinEq a b q n thetaBar m s) ∧ ∀ s : LinStrat, IsLinEq a b q n thetaBar m s → ∀ i : Fin 2, 1 < s.beta i / (n / (q + m i + (1 - a) * n)) ∧ 1 < s.gamma i / (m i / ((1 - a) * (q + m i + (1 - a) * n))) ∧ 1 < s.lam i / (n / (q + m i.rev + (1 - a) * n)) ∧ 1 < s.omega i / (m i.rev / ((1 - a) * (q + m i.rev + (1 - a) * n))) ∧ s.h i = (s.gamma i / m i - b * s.omega i / m i.rev) * q * thetaBar := by
  refine ⟨⟨sP a b q n thetaBar m, sP_isLinEq a b q n thetaBar m ha0 ha hb0 hb hq hn hm,
    fun s hs => sP_unique a b q n thetaBar m ha0 ha hb0 hb hq hn hm s hs⟩, ?_⟩
  intro s hs i
  rw [sP_unique a b q n thetaBar m ha0 ha hb0 hb hq hn hm s hs]
  have hc := fun k => ccP_bounds q n m k hq hn (hm k).le
  have hne : ∀ k, (1 - a * ccP q n m k) ≠ 0 := fun k => by
    have := hc k; nlinarith
  have hcne : ∀ k, ccP q n m k ≠ 0 := fun k => (hc k).1.ne'
  have hee : ∀ k, eeP q n m k ≠ 0 := fun k => by unfold eeP; have := hm k; positivity
  have hv : (1 - a) ≠ 0 := by intro h; linarith
  have hB : ∀ k, n / (q + m k + (1 - a) * n) = ccP q n m k / (1 - a * ccP q n m k) :=
    fun k => betaNC_eq a q n (m k) ha hq hn (hm k).le
  have hG : ∀ k, m k / ((1 - a) * (q + m k + (1 - a) * n))
      = eeP q n m k / ((1 - a) * (1 - a * ccP q n m k)) :=
    fun k => gammaNC_eq a q n (m k) ha hq hn (hm k).le
  simp only [sP]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hB, div_div_eq_mul_div, mul_comm (ccP q n m i), mul_assoc,
      mul_div_assoc, mul_div_cancel_left₀ _ (hcne i)]
    exact L_kappa a b _ ha0 ha hb0 hb (hc i).1 (hc i).2
  · rw [hG, div_div_eq_mul_div, mul_comm (eeP q n m i), mul_assoc,
      mul_div_assoc, mul_div_cancel_left₀ _ (hee i)]
    exact L_nu a b _ ha0 ha hb0 hb (hc i).1 (hc i).2
  · rw [hB, div_div_eq_mul_div, mul_comm (ccP q n m i.rev), mul_assoc,
      mul_div_assoc, mul_div_cancel_left₀ _ (hcne i.rev)]
    exact L_mu a b _ ha0 ha hb0 hb (hc i.rev).1 (hc i.rev).2
  · rw [hG, div_div_eq_mul_div, mul_comm (eeP q n m i.rev), mul_assoc,
      mul_div_assoc, mul_div_cancel_left₀ _ (hee i.rev)]
    exact L_chi a b _ ha0 ha hb0 hb (hc i.rev).1 (hc i.rev).2
  · have h1 : eeP q n m i * gP a b (ccP q n m i) / m i = gP a b (ccP q n m i) / (m i + n + q) := by
      unfold eeP; have := (hm i).ne'; field_simp
    have h2 : b * (eeP q n m i.rev * oP a b (ccP q n m i.rev)) / m i.rev
        = b * oP a b (ccP q n m i.rev) / (m i.rev + n + q) := by
      unfold eeP; have := (hm i.rev).ne'; field_simp
    rw [h1, h2]

end CompOpacity.Disclosure

open CompOpacity.Disclosure in
theorem solution (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b ≤ 1) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hm : ∀ i, 0 < m i) : (∃! s : LinStrat, IsLinEq a b q n thetaBar m s) ∧ ∀ s : LinStrat, IsLinEq a b q n thetaBar m s → ∀ i : Fin 2, 1 < s.beta i / (n / (q + m i + (1 - a) * n)) ∧ 1 < s.gamma i / (m i / ((1 - a) * (q + m i + (1 - a) * n))) ∧ 1 < s.lam i / (n / (q + m i.rev + (1 - a) * n)) ∧ 1 < s.omega i / (m i.rev / ((1 - a) * (q + m i.rev + (1 - a) * n))) ∧ s.h i = (s.gamma i / m i - b * s.omega i / m i.rev) * q * thetaBar :=
  proposition_3_proof a b q n thetaBar m ha0 ha hb0 hb hq hn hθ hm
