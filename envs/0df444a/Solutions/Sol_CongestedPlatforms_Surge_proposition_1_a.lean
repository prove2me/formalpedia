-- Prove2me | solution 1 for CongestedPlatforms.Surge.proposition_1_a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:02:09.054615+00:00
-- url     : https://prove2.me/submissions/6bb2a25c-c90a-47ac-a192-3705193fb8b4

import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

noncomputable def dPs (lam γ m y : ℝ) : ℝ := lam * y * (m - y) / (y + lam * γ)
noncomputable def dFs (lam γ t y : ℝ) : ℝ :=
  lam * t * (lam * γ + y * (1 - t + y)) / (2 * t * y + lam * γ * (t + y))
noncomputable def sPs (lam γ m y : ℝ) : ℝ := y * Real.sqrt (lam * (m - y) / (y + lam * γ))
noncomputable def sFs (lam γ t y : ℝ) : ℝ :=
  t * Real.sqrt (lam * (lam * γ + y * (1 - t + y)) / (2 * t * y + lam * γ * (t + y)))

theorem dP_shift (lam γ c y : ℝ) : dP lam γ 1 c (c + y) = dPs lam γ (1 - c) y := by
  unfold dP dPs
  congr 1 <;> ring

theorem sP_shift (lam γ c y : ℝ) : sP lam γ 1 c (c + y) = sPs lam γ (1 - c) y := by
  unfold sP sPs
  have h1 : (1:ℝ) * (c + y) - c = y := by ring
  have h2 : (1:ℝ) - (c + y) = 1 - c - y := by ring
  rw [h1, h2]

theorem dF_shift (lam γ c t y : ℝ) : dF lam γ 1 c (c + t) (c + y) = dFs lam γ t y := by
  unfold dF dFs
  congr 1 <;> ring

theorem sF_shift (lam γ c t y : ℝ) : sF lam γ 1 c (c + t) (c + y) = sFs lam γ t y := by
  unfold sF sFs
  have h1 : (1:ℝ) * (c + t) - c = t := by ring
  have h2 : (1:ℝ) * (c + y) - c = y := by ring
  have h3 : (1:ℝ) * ((c + t) + (c + y)) - 2 * c = t + y := by ring
  have h4 : (1:ℝ) - (c + t) + (c + y) = 1 - t + y := by ring
  rw [h1, h2, h3, h4]

theorem D_shift (lam γ c t y : ℝ) : D lam γ 1 c (c + t) (c + y) =
    if dPs lam γ (1 - c) t + dPs lam γ (1 - c) y ≤ lam then dPs lam γ (1 - c) t
    else dFs lam γ t y := by
  unfold D
  rw [dP_shift, dP_shift, dF_shift]

theorem S_shift (lam γ c t y : ℝ) : S lam γ 1 c (c + t) (c + y) =
    if dPs lam γ (1 - c) t + dPs lam γ (1 - c) y ≤ lam then sPs lam γ (1 - c) t
    else sFs lam γ t y := by
  unfold S
  rw [dP_shift, dP_shift, sP_shift, sF_shift]

theorem profit_shift (lam γ c q p : ℝ) : profit lam γ 1 c q p =
    c * min (D lam γ 1 c q p) (S lam γ 1 c q p) := by
  unfold profit
  simp

theorem sq_P (lam γ m t : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (ht : 0 ≤ t) (htm : t ≤ m) :
    0 ≤ sPs lam γ m t ∧ 0 ≤ dPs lam γ m t ∧ sPs lam γ m t ^ 2 = t * dPs lam γ m t := by
  have hK : 0 < t + lam * γ := by positivity
  have hQ : 0 ≤ lam * (m - t) / (t + lam * γ) := by
    apply div_nonneg (mul_nonneg hlam.le (by linarith)) hK.le
  refine ⟨?_, ?_, ?_⟩
  · unfold sPs; positivity
  · unfold dPs
    apply div_nonneg (mul_nonneg (mul_nonneg hlam.le ht) (by linarith)) hK.le
  · unfold sPs dPs
    rw [mul_pow, Real.sq_sqrt hQ]
    field_simp

theorem sq_F (lam γ t y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hy : 0 ≤ y) :
    0 ≤ sFs lam γ t y ∧ 0 ≤ dFs lam γ t y ∧ sFs lam γ t y ^ 2 = t * dFs lam γ t y := by
  have hK : 0 < 2 * t * y + lam * γ * (t + y) := by positivity
  have hN : 0 ≤ lam * (lam * γ + y * (1 - t + y)) := by
    apply mul_nonneg hlam.le
    have : 0 ≤ y * (1 - t + y) := mul_nonneg hy (by linarith)
    have : 0 < lam * γ := by positivity
    linarith
  have hQ : 0 ≤ lam * (lam * γ + y * (1 - t + y)) / (2 * t * y + lam * γ * (t + y)) :=
    div_nonneg hN hK.le
  refine ⟨?_, ?_, ?_⟩
  · unfold sFs; positivity
  · unfold dFs
    apply div_nonneg _ hK.le
    have : 0 ≤ y * (1 - t + y) := mul_nonneg hy (by linarith)
    have : 0 < lam * γ := by positivity
    have : 0 ≤ lam * γ + y * (1 - t + y) := by linarith
    positivity
  · unfold sFs dFs
    rw [mul_pow, Real.sq_sqrt hQ]
    field_simp

/-- common facts about `D`, `S` at shifted prices `t, y`. -/
theorem DS_facts (lam γ c t y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (ht : 0 < t) (htm : t ≤ 1 - c) (hy : 0 ≤ y) :
    0 ≤ D lam γ 1 c (c + t) (c + y) ∧ 0 ≤ S lam γ 1 c (c + t) (c + y) ∧
      S lam γ 1 c (c + t) (c + y) ^ 2 = t * D lam γ 1 c (c + t) (c + y) := by
  rw [D_shift, S_shift]
  split_ifs with h
  · exact ⟨(sq_P lam γ _ t hlam hγ ht.le htm).2.1, (sq_P lam γ _ t hlam hγ ht.le htm).1,
      (sq_P lam γ _ t hlam hγ ht.le htm).2.2⟩
  · have := sq_F lam γ t y hlam hγ ht (by linarith) hy
    exact ⟨this.2.1, this.1, this.2.2⟩

theorem supply_iff (lam γ c t y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (ht : 0 < t) (htm : t ≤ 1 - c) (hy : 0 ≤ y) :
    D lam γ 1 c (c + t) (c + y) ≤ S lam γ 1 c (c + t) (c + y) ↔
      D lam γ 1 c (c + t) (c + y) ≤ t := by
  obtain ⟨hD, hS, hsq⟩ := DS_facts lam γ c t y hlam hγ hc0 hc1 ht htm hy
  set d := D lam γ 1 c (c + t) (c + y)
  set s := S lam γ 1 c (c + t) (c + y)
  constructor
  · intro h
    rcases hD.eq_or_lt with h0 | h0
    · rw [← h0]; exact ht.le
    · by_contra hh
      push Not at hh
      nlinarith
  · intro h
    by_contra hh
    push Not at hh
    nlinarith

theorem Dsym_eq (lam γ c y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hy : 0 ≤ y) :
    D lam γ 1 c (c + y) (c + y) = min (dPs lam γ (1 - c) y) (lam / 2) := by
  rw [D_shift]
  split_ifs with h
  · rw [min_eq_left (by linarith)]
  · push Not at h
    rw [min_eq_right (by linarith)]
    have hy0 : y ≠ 0 := by
      rintro rfl
      unfold dPs at h
      simp at h
      linarith
    have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    unfold dFs
    have : lam * γ + y * (1 - y + y) = y + lam * γ := by ring
    rw [this]
    have h2 : 2 * y * y + lam * γ * (y + y) = 2 * y * (y + lam * γ) := by ring
    rw [h2]
    have : 0 < y + lam * γ := by positivity
    field_simp

/-! ### Type A -/

noncomputable def xA (lam γ c : ℝ) : ℝ :=
  Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ

theorem xA_eq (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    xA lam γ c ^ 2 + 2 * (lam * γ) * xA lam γ c = lam * γ * (1 - c) := by
  have h : 0 ≤ lam ^ 2 * γ ^ 2 + lam * γ * (1 - c) := by
    have : 0 < lam * γ * (1 - c) := by
      have : 0 < 1 - c := by linarith
      positivity
    positivity
  have := Real.sq_sqrt h
  unfold xA
  nlinarith

theorem xA_pos (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    0 < xA lam γ c := by
  have h := xA_eq lam γ c hlam hγ hc1
  have hK : 0 < lam * γ := by positivity
  have hm : 0 < lam * γ * (1 - c) := by
    have : 0 < 1 - c := by linarith
    positivity
  have h0 : 0 ≤ lam ^ 2 * γ ^ 2 + lam * γ * (1 - c) := by positivity
  unfold xA
  have : lam * γ < Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  linarith

theorem xA_lt (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    xA lam γ c < 1 - c := by
  have h := xA_eq lam γ c hlam hγ hc1
  have hp := xA_pos lam γ c hlam hγ hc1
  have hK : 0 < lam * γ := by positivity
  by_contra hh
  push Not at hh
  nlinarith [mul_pos hK hp]

/-- gap identity for the unilateral demand -/
theorem dPs_gap (lam γ c y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) (hy : 0 ≤ y) :
    dPs lam γ (1 - c) y = xA lam γ c ^ 2 / γ - lam * (y - xA lam γ c) ^ 2 / (y + lam * γ) := by
  have h := xA_eq lam γ c hlam hγ hc1
  have hyK : 0 < y + lam * γ := by positivity
  unfold dPs
  field_simp
  set X := xA lam γ c
  nlinarith [h]

theorem dPs_le (lam γ c y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) (hy : 0 ≤ y) :
    dPs lam γ (1 - c) y ≤ xA lam γ c ^ 2 / γ := by
  rw [dPs_gap lam γ c y hlam hγ hc1 hy]
  have : 0 ≤ lam * (y - xA lam γ c) ^ 2 / (y + lam * γ) := by positivity
  linarith

theorem dPs_lt (lam γ c y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) (hy : 0 ≤ y)
    (hne : y ≠ xA lam γ c) : dPs lam γ (1 - c) y < xA lam γ c ^ 2 / γ := by
  rw [dPs_gap lam γ c y hlam hγ hc1 hy]
  have : 0 < lam * (y - xA lam γ c) ^ 2 / (y + lam * γ) := by
    have : 0 < (y - xA lam γ c) ^ 2 := by
      have : y - xA lam γ c ≠ 0 := sub_ne_zero.mpr hne
      positivity
    positivity
  linarith

theorem dPs_xA (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    dPs lam γ (1 - c) (xA lam γ c) = xA lam γ c ^ 2 / γ := by
  rw [dPs_gap lam γ c _ hlam hγ hc1 (xA_pos lam γ c hlam hγ hc1).le]
  simp

theorem xA_sq_le (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1)
    (hA1 : (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c) :
    xA lam γ c ^ 2 ≤ lam * γ / 2 := by
  have h := xA_eq lam γ c hlam hγ hc1
  have hp := xA_pos lam γ c hlam hγ hc1
  have hK : 0 < lam * γ := by positivity
  by_contra hh
  push Not at hh
  set X := xA lam γ c
  have h1 : 1 / 2 + 2 * X < 1 - c := by
    by_contra h2
    push Not at h2
    nlinarith
  rcases hA1 with h3 | h3
  · rw [div_le_iff₀ (by positivity)] at h3
    nlinarith
  · linarith

theorem xA_le_gamma_iff (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    xA lam γ c ≤ γ ↔ lam * (1 - c) / (1 + 2 * lam) ≤ γ := by
  have h := xA_eq lam γ c hlam hγ hc1
  have hp := xA_pos lam γ c hlam hγ hc1
  rw [div_le_iff₀ (by positivity)]
  set X := xA lam γ c
  constructor
  · intro hX
    have : lam * γ * (1 - c) ≤ γ * γ * (1 + 2 * lam) := by nlinarith [mul_pos hlam hγ]
    nlinarith
  · intro hg
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hlam hγ]

theorem xA_lt_gamma_iff (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    xA lam γ c < γ ↔ lam * (1 - c) / (1 + 2 * lam) < γ := by
  have h := xA_eq lam γ c hlam hγ hc1
  have hp := xA_pos lam γ c hlam hγ hc1
  rw [div_lt_iff₀ (by positivity)]
  set X := xA lam γ c
  constructor
  · intro hX
    nlinarith [mul_pos hlam hγ]
  · intro hg
    by_contra hh
    push Not at hh
    nlinarith [mul_pos hlam hγ]

theorem xA_eq_gamma_iff (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) :
    xA lam γ c = γ ↔ γ = lam * (1 - c) / (1 + 2 * lam) := by
  have h1 := xA_le_gamma_iff lam γ c hlam hγ hc1
  have h2 := xA_lt_gamma_iff lam γ c hlam hγ hc1
  constructor
  · intro hX
    have a : xA lam γ c ≤ γ := hX.le
    have b : ¬ xA lam γ c < γ := by rw [hX]; exact lt_irrefl _
    have := h1.mp a
    have := mt h2.mpr b
    push Not at this
    exact le_antisymm (by assumption) (by assumption) |>.symm
  · intro hg
    have a := h1.mpr hg.symm.le
    have b := mt h2.mp (by rw [← hg]; exact lt_irrefl _)
    push Not at b
    exact le_antisymm a b

theorem D_eq_P (lam γ c t y : ℝ) (h : dPs lam γ (1 - c) t + dPs lam γ (1 - c) y ≤ lam) :
    D lam γ 1 c (c + t) (c + y) = dPs lam γ (1 - c) t := by
  rw [D_shift, if_pos h]

theorem two_dPs_le (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hX2 : xA lam γ c ^ 2 ≤ lam * γ / 2) :
    2 * (xA lam γ c ^ 2 / γ) ≤ lam := by
  have : xA lam γ c ^ 2 / γ ≤ lam / 2 := by
    rw [div_le_iff₀ hγ]; nlinarith
  linarith

theorem neA_iff (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 < c) (hc1 : c < 1)
    (hX2 : xA lam γ c ^ 2 ≤ lam * γ / 2) (hXg : xA lam γ c ≤ γ) (p : ℝ) :
    IsSymNE lam γ 1 c p ↔ p = c + xA lam γ c := by
  have hXp := xA_pos lam γ c hlam hγ hc1
  have hXm := xA_lt lam γ c hlam hγ hc1
  have h2 := two_dPs_le lam γ c hlam hγ hX2
  have hXpoint : D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) = xA lam γ c ^ 2 / γ := by
    rw [Dsym_eq lam γ c _ hlam hγ hXp.le, dPs_xA lam γ c hlam hγ hc1]
    exact min_eq_left (by linarith)
  have hXfeas : D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) ≤ xA lam γ c := by
    rw [hXpoint, div_le_iff₀ hγ]
    nlinarith
  constructor
  · intro hne
    obtain ⟨hp1, hp2, hsup, hdev⟩ := hne
    by_contra hneq
    obtain ⟨y, rfl⟩ : ∃ y, p = c + y := ⟨p - c, by ring⟩
    have hy0 : 0 ≤ y := by simp at hp1; linarith
    have hyne : y ≠ xA lam γ c := by
      intro h; apply hneq; rw [h]
    -- deviation to c + xA
    have hreg : dPs lam γ (1 - c) (xA lam γ c) + dPs lam γ (1 - c) y ≤ lam := by
      have := dPs_le lam γ c y hlam hγ hc1 hy0
      rw [dPs_xA lam γ c hlam hγ hc1]
      linarith
    have hDq : D lam γ 1 c (c + xA lam γ c) (c + y) = xA lam γ c ^ 2 / γ := by
      rw [D_eq_P lam γ c _ _ hreg, dPs_xA lam γ c hlam hγ hc1]
    have hfeas : SupplyOK lam γ 1 c (c + xA lam γ c) (c + y) := by
      unfold SupplyOK
      rw [supply_iff lam γ c _ _ hlam hγ hc0.le hc1 hXp hXm.le hy0, hDq, div_le_iff₀ hγ]
      nlinarith
    have hle := hdev (c + xA lam γ c) (by simp; linarith) (by linarith) hfeas
    rw [profit_shift, profit_shift] at hle
    have hDpp : D lam γ 1 c (c + y) (c + y) < xA lam γ c ^ 2 / γ := by
      rw [Dsym_eq lam γ c _ hlam hγ hy0]
      exact lt_of_le_of_lt (min_le_left _ _) (dPs_lt lam γ c y hlam hγ hc1 hy0 hyne)
    have hmin : min (D lam γ 1 c (c + xA lam γ c) (c + y)) (S lam γ 1 c (c + xA lam γ c) (c + y))
        = xA lam γ c ^ 2 / γ := by
      rw [min_eq_left (show D lam γ 1 c (c + xA lam γ c) (c + y) ≤ S lam γ 1 c (c + xA lam γ c) (c + y) from hfeas), hDq]
    rw [hmin] at hle
    have := le_of_mul_le_mul_left hle hc0
    have h3 : min (D lam γ 1 c (c + y) (c + y)) (S lam γ 1 c (c + y) (c + y)) ≤
        D lam γ 1 c (c + y) (c + y) := min_le_left _ _
    linarith
  · intro hp
    subst hp
    refine ⟨by simp; linarith, by linarith, ?_, ?_⟩
    · unfold SupplyOK
      rw [supply_iff lam γ c _ _ hlam hγ hc0.le hc1 hXp hXm.le hXp.le]
      exact hXfeas
    · intro q hq1 hq2 hsup
      obtain ⟨t, rfl⟩ : ∃ t, q = c + t := ⟨q - c, by ring⟩
      have ht0 : 0 ≤ t := by simp at hq1; linarith
      have hreg : dPs lam γ (1 - c) t + dPs lam γ (1 - c) (xA lam γ c) ≤ lam := by
        have := dPs_le lam γ c t hlam hγ hc1 ht0
        rw [dPs_xA lam γ c hlam hγ hc1]
        linarith
      have hDq : D lam γ 1 c (c + t) (c + xA lam γ c) ≤ xA lam γ c ^ 2 / γ := by
        rw [D_eq_P lam γ c _ _ hreg]
        exact dPs_le lam γ c t hlam hγ hc1 ht0
      rw [profit_shift, profit_shift]
      apply mul_le_mul_of_nonneg_left _ hc0.le
      have hS : D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) ≤
          S lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) := by
        unfold SupplyOK at *
        rw [supply_iff lam γ c _ _ hlam hγ hc0.le hc1 hXp hXm.le hXp.le]
        exact hXfeas
      rw [min_eq_left hS, hXpoint]
      exact (min_le_left _ _).trans hDq

theorem pA_eq (lam γ c : ℝ) :
    c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ = c + xA lam γ c := by
  unfold xA; ring

theorem DA_point (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1)
    (hX2 : xA lam γ c ^ 2 ≤ lam * γ / 2) :
    D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) = xA lam γ c ^ 2 / γ := by
  have hXp := xA_pos lam γ c hlam hγ hc1
  have h2 := two_dPs_le lam γ c hlam hγ hX2
  rw [Dsym_eq lam γ c _ hlam hγ hXp.le, dPs_xA lam γ c hlam hγ hc1]
  exact min_eq_left (by linarith)

theorem prop_1_a_aux (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hA1 : (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c) (hA2 : lam * (1 - c) / (1 + 2 * lam) ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔
      p = c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ∧
    (dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) +
        dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ≤ lam) ∧
    (lam * (1 - c) / (1 + 2 * lam) < γ →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) <
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) ∧
    (γ = lam * (1 - c) / (1 + 2 * lam) →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) =
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) := by
  have hγ : 0 < γ := by
    have : 0 < lam * (1 - c) / (1 + 2 * lam) := by
      have : 0 < 1 - c := by linarith
      positivity
    linarith
  have hX2 := xA_sq_le lam γ c hlam hγ hc1 hA1
  have hXg := (xA_le_gamma_iff lam γ c hlam hγ hc1).mpr hA2
  have hXp := xA_pos lam γ c hlam hγ hc1
  have hXm := xA_lt lam γ c hlam hγ hc1
  rw [pA_eq]
  have hpt := DA_point lam γ c hlam hγ hc1 hX2
  refine ⟨neA_iff lam γ c hlam hγ hc0 hc1 hX2 hXg, ?_, ?_, ?_⟩
  · rw [dP_shift, dPs_xA lam γ c hlam hγ hc1]
    have := two_dPs_le lam γ c hlam hγ hX2
    linarith
  · intro hlt
    have hXlt := (xA_lt_gamma_iff lam γ c hlam hγ hc1).mpr hlt
    obtain ⟨hD, hS, hsq⟩ := DS_facts lam γ c (xA lam γ c) (xA lam γ c) hlam hγ hc0.le hc1
      hXp hXm.le hXp.le
    set X := xA lam γ c
    have hDpos : 0 < D lam γ 1 c (c + X) (c + X) := by rw [hpt]; positivity
    have hDX : D lam γ 1 c (c + X) (c + X) < X := by
      rw [hpt, div_lt_iff₀ hγ]; nlinarith
    nlinarith
  · intro heq
    have hXe := (xA_eq_gamma_iff lam γ c hlam hγ hc1).mpr heq
    obtain ⟨hD, hS, hsq⟩ := DS_facts lam γ c (xA lam γ c) (xA lam γ c) hlam hγ hc0.le hc1
      hXp hXm.le hXp.le
    set X := xA lam γ c
    have hDX : D lam γ 1 c (c + X) (c + X) = X := by
      rw [hpt, hXe]; field_simp
    rw [hDX] at hsq ⊢
    nlinarith

end CongestedPlatforms.Surge

open CongestedPlatforms.Surge

theorem solution (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hA1 : (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c) (hA2 : lam * (1 - c) / (1 + 2 * lam) ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔
      p = c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ∧
    (dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) +
        dP lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) ≤ lam) ∧
    (lam * (1 - c) / (1 + 2 * lam) < γ →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) <
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) ∧
    (γ = lam * (1 - c) / (1 + 2 * lam) →
      D lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ) =
        S lam γ 1 c (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)
          (c + Real.sqrt (lam ^ 2 * γ ^ 2 + lam * γ * (1 - c)) - lam * γ)) := by
  exact prop_1_a_aux lam γ c hlam hc0 hc1 hA1 hA2
