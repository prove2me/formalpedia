-- Prove2me | solution 1 for CongestedPlatforms.Surge.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:21:51.118156+00:00
-- url     : https://prove2.me/submissions/5bff4b05-17bb-4135-a7e3-e8adddc79f9d

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

/-! ### Type D -/

theorem zD_sq (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) :
    Real.sqrt (lam * γ / 2) ^ 2 = lam * γ / 2 := Real.sq_sqrt (by positivity)

theorem zD_pos (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) :
    0 < Real.sqrt (lam * γ / 2) := Real.sqrt_pos.mpr (by positivity)

theorem zD_ge (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hD2 : lam / 2 ≤ γ) :
    lam / 2 ≤ Real.sqrt (lam * γ / 2) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem zD_lt (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) :
    4 * Real.sqrt (lam * γ / 2) < 1 - 2 * c := by
  rw [lt_div_iff₀ (by positivity)] at hD1
  have hz := zD_sq lam γ hlam hγ
  have hzp := zD_pos lam γ hlam hγ
  set z := Real.sqrt (lam * γ / 2)
  by_contra h
  push Not at h
  nlinarith

theorem dPs_zD (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) :
    lam / 2 < dPs lam γ (1 - c) (Real.sqrt (lam * γ / 2)) := by
  have hz := zD_sq lam γ hlam hγ
  have hzp := zD_pos lam γ hlam hγ
  have hlt := zD_lt lam γ c hlam hγ hc hD1
  set z := Real.sqrt (lam * γ / 2)
  unfold dPs
  rw [lt_div_iff₀ (by positivity)]
  have key : 0 < lam * z * (1 - 2 * c - 4 * z) := mul_pos (mul_pos hlam hzp) (by linarith)
  have h3 : lam * (lam * γ) = 2 * lam * z ^ 2 := by rw [hz]; ring
  nlinarith [key, h3]

theorem zD_lt_m (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 < c) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) :
    Real.sqrt (lam * γ / 2) < 1 - c := by
  have hzp := zD_pos lam γ hlam hγ
  have hlt := zD_lt lam γ c hlam hγ hc hD1
  linarith

theorem dFs_sub (lam γ t y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (ht : 0 ≤ t) (hy : 0 ≤ y)
    (hty : 0 < t + y) :
    dFs lam γ t y - lam / 2 =
      lam * (t - y) * (lam * γ - 2 * t * y) / (2 * (2 * t * y + lam * γ * (t + y))) := by
  have hden : 0 < 2 * t * y + lam * γ * (t + y) := by positivity
  unfold dFs
  field_simp
  ring

theorem dPs_sum_iff (lam γ m t y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (ht : 0 < t) (hy : 0 ≤ y) :
    dPs lam γ m t + dPs lam γ m y ≤ lam ↔ dPs lam γ m t ≤ dFs lam γ t y := by
  set K := lam * γ with hK
  have hKp : 0 < K := by positivity
  have hden : 0 < 2 * t * y + K * (t + y) := by positivity
  have h1 : 0 < t + K := by positivity
  have h2 : 0 < y + K := by positivity
  set Φ := (t + K) * (y + K) - t * (m - t) * (y + K) - y * (m - y) * (t + K) with hΦ
  have e1 : lam - (dPs lam γ m t + dPs lam γ m y) = lam * Φ / ((t + K) * (y + K)) := by
    unfold dPs
    rw [← hK]
    field_simp
    ring
  have e2 : dFs lam γ t y - dPs lam γ m t = lam * t * Φ / ((t + K) * (2 * t * y + K * (t + y))) := by
    unfold dPs dFs
    rw [← hK]
    field_simp
    ring
  have s1 : 0 ≤ lam * Φ / ((t + K) * (y + K)) ↔ 0 ≤ Φ := by
    rw [div_nonneg_iff]
    constructor
    · rintro (⟨a, _⟩ | ⟨a, b⟩)
      · exact nonneg_of_mul_nonneg_right a hlam
      · exfalso; have := mul_pos h1 h2; linarith
    · intro h; left; exact ⟨mul_nonneg hlam.le h, (mul_pos h1 h2).le⟩
  have s2 : 0 ≤ lam * t * Φ / ((t + K) * (2 * t * y + K * (t + y))) ↔ 0 ≤ Φ := by
    rw [div_nonneg_iff]
    have hlt : 0 < lam * t := mul_pos hlam ht
    constructor
    · rintro (⟨a, _⟩ | ⟨a, b⟩)
      · exact nonneg_of_mul_nonneg_right a hlt
      · exfalso; have := mul_pos h1 hden; linarith
    · intro h; left; exact ⟨mul_nonneg hlt.le h, (mul_pos h1 hden).le⟩
  constructor
  · intro h
    have : 0 ≤ lam - (dPs lam γ m t + dPs lam γ m y) := by linarith
    rw [e1, s1] at this
    have := s2.mpr this
    rw [← e2] at this
    linarith
  · intro h
    have : 0 ≤ dFs lam γ t y - dPs lam γ m t := by linarith
    rw [e2, s2] at this
    have := s1.mpr this
    rw [← e1] at this
    linarith

theorem D_min (lam γ c t y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (ht : 0 < t) (hy : 0 ≤ y) :
    D lam γ 1 c (c + t) (c + y) = min (dPs lam γ (1 - c) t) (dFs lam γ t y) := by
  rw [D_shift]
  split_ifs with h
  · exact (min_eq_left ((dPs_sum_iff lam γ _ t y hlam hγ ht hy).mp h)).symm
  · have : ¬ dPs lam γ (1 - c) t ≤ dFs lam γ t y := fun h' =>
      h ((dPs_sum_iff lam γ _ t y hlam hγ ht hy).mpr h')
    push Not at this
    exact (min_eq_right this.le).symm

theorem D_cont (lam γ c y z m : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hz : 0 < z) (hy : 0 ≤ y) :
    ContinuousOn (fun t => D lam γ 1 c (c + t) (c + y) - t) (Set.Icc z m) := by
  have hcongr : ∀ t ∈ Set.Icc z m, D lam γ 1 c (c + t) (c + y) - t =
      min (dPs lam γ (1 - c) t) (dFs lam γ t y) - t := by
    intro t ht
    rw [D_min lam γ c t y hlam hγ (lt_of_lt_of_le hz ht.1) hy]
  refine ContinuousOn.congr ?_ hcongr
  apply ContinuousOn.sub _ continuousOn_id
  apply ContinuousOn.inf
  · unfold dPs
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have : 0 < t := lt_of_lt_of_le hz ht.1
    positivity
  · unfold dFs
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have : 0 < t := lt_of_lt_of_le hz ht.1
    positivity

theorem D_ivt (lam γ c y z : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hz : 0 < z) (hzm : z ≤ 1 - c)
    (hy : 0 ≤ y) (hbig : z < D lam γ 1 c (c + z) (c + y)) :
    ∃ t, z < t ∧ t ≤ 1 - c ∧ D lam γ 1 c (c + t) (c + y) = t := by
  have hcont := D_cont lam γ c y z (1 - c) hlam hγ hz hy
  have hm : D lam γ 1 c (c + (1 - c)) (c + y) - (1 - c) ≤ 0 := by
    have hmpos : 0 < 1 - c := lt_of_lt_of_le hz hzm
    rw [D_min lam γ c _ y hlam hγ hmpos hy]
    have : dPs lam γ (1 - c) (1 - c) = 0 := by unfold dPs; simp
    have h2 : min (dPs lam γ (1 - c) (1 - c)) (dFs lam γ (1 - c) y) ≤ 0 := by
      rw [this]; exact min_le_left _ _
    linarith
  have hivt := intermediate_value_Icc' hzm hcont
  have h0 : (0:ℝ) ∈ Set.Icc (D lam γ 1 c (c + (1 - c)) (c + y) - (1 - c))
      (D lam γ 1 c (c + z) (c + y) - z) := ⟨hm, by linarith⟩
  obtain ⟨t, ht, hft⟩ := hivt h0
  refine ⟨t, ?_, ht.2, by simp only at hft; linarith⟩
  rcases ht.1.eq_or_lt with h | h
  · exfalso; rw [← h] at hft; simp only at hft; linarith
  · exact h

theorem D_le_half_z (lam γ c t z : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hz : 0 < z)
    (hzK : lam * γ = 2 * z ^ 2) (hzd : lam / 2 < dPs lam γ (1 - c) z) (ht : 0 ≤ t) :
    D lam γ 1 c (c + t) (c + z) ≤ lam / 2 := by
  rw [D_shift]
  split_ifs with h
  · linarith
  · have := dFs_sub lam γ t z hlam hγ ht hz.le (by linarith)
    have hden : 0 < 2 * (2 * t * z + lam * γ * (t + z)) := by positivity
    have hn : lam * (t - z) * (lam * γ - 2 * t * z) ≤ 0 := by
      rw [hzK]
      nlinarith [mul_pos hlam hz, sq_nonneg (t - z), mul_nonneg (mul_pos hlam hz).le (sq_nonneg (t - z))]
    have : dFs lam γ t z - lam / 2 ≤ 0 := by
      rw [this]; exact div_nonpos_of_nonpos_of_nonneg hn hden.le
    linarith

theorem D_gt_half_z (lam γ c y z : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hz : 0 < z)
    (hzK : lam * γ = 2 * z ^ 2) (hzd : lam / 2 < dPs lam γ (1 - c) z) (hy : 0 ≤ y) (hne : y ≠ z) :
    lam / 2 < D lam γ 1 c (c + z) (c + y) := by
  rw [D_shift]
  split_ifs with h
  · exact hzd
  · have := dFs_sub lam γ z y hlam hγ hz.le hy (by linarith)
    have hden : 0 < 2 * (2 * z * y + lam * γ * (z + y)) := by positivity
    have hn : 0 < lam * (z - y) * (lam * γ - 2 * z * y) := by
      rw [hzK]
      have : 0 < (z - y) ^ 2 := by
        have : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
        positivity
      nlinarith [mul_pos hlam hz, mul_pos (mul_pos hlam hz) this]
    have : 0 < dFs lam γ z y - lam / 2 := by
      rw [this]; exact div_pos hn hden
    linarith

theorem neD_iff (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 < c) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) (hD2 : lam / 2 ≤ γ) (p : ℝ) :
    IsSymNE lam γ 1 c p ↔ p = c + Real.sqrt (lam * γ / 2) := by
  have hc1 : c < 1 := by linarith
  have hzp := zD_pos lam γ hlam hγ
  have hzm := zD_lt_m lam γ c hlam hγ hc0 hc hD1
  have hzd := dPs_zD lam γ c hlam hγ hc hD1
  have hzge := zD_ge lam γ hlam hγ hD2
  have hzsq := zD_sq lam γ hlam hγ
  set z := Real.sqrt (lam * γ / 2) with hzdef
  have hzK : lam * γ = 2 * z ^ 2 := by rw [hzsq]; ring
  have hDz : D lam γ 1 c (c + z) (c + z) = lam / 2 := by
    rw [Dsym_eq lam γ c _ hlam hγ hzp.le]
    exact min_eq_right hzd.le
  have hfeas : D lam γ 1 c (c + z) (c + z) ≤ S lam γ 1 c (c + z) (c + z) := by
    rw [supply_iff lam γ c _ _ hlam hγ hc0.le hc1 hzp hzm.le hzp.le, hDz]
    exact hzge
  constructor
  · intro hne
    obtain ⟨hp1, hp2, hsup, hdev⟩ := hne
    by_contra hneq
    obtain ⟨y, rfl⟩ : ∃ y, p = c + y := ⟨p - c, by ring⟩
    have hy0 : 0 ≤ y := by simp at hp1; linarith
    have hyne : y ≠ z := by
      intro h; apply hneq; rw [h]
    have hbig := D_gt_half_z lam γ c y z hlam hγ hzp hzK hzd hy0 hyne
    -- find a profitable feasible deviation t
    obtain ⟨t, htz, htm, hDt, hlt⟩ : ∃ t, 0 < t ∧ t ≤ 1 - c ∧
        D lam γ 1 c (c + t) (c + y) ≤ t ∧ lam / 2 < D lam γ 1 c (c + t) (c + y) := by
      by_cases hfz : D lam γ 1 c (c + z) (c + y) ≤ z
      · exact ⟨z, hzp, hzm.le, hfz, hbig⟩
      · push Not at hfz
        obtain ⟨t, hzt, htm, hDt⟩ := D_ivt lam γ c y z hlam hγ hzp hzm.le hy0 hfz
        refine ⟨t, by linarith, htm, hDt.le, ?_⟩
        rw [hDt]; linarith
    have hfeas' : SupplyOK lam γ 1 c (c + t) (c + y) := by
      unfold SupplyOK
      rw [supply_iff lam γ c _ _ hlam hγ hc0.le hc1 htz htm hy0]
      exact hDt
    have hle := hdev (c + t) (by simp; linarith) (by linarith) hfeas'
    rw [profit_shift, profit_shift] at hle
    have hSt : D lam γ 1 c (c + t) (c + y) ≤ S lam γ 1 c (c + t) (c + y) := hfeas'
    rw [min_eq_left hSt] at hle
    have h1 := le_of_mul_le_mul_left hle hc0
    have h2 : min (D lam γ 1 c (c + y) (c + y)) (S lam γ 1 c (c + y) (c + y)) ≤ lam / 2 :=
      (min_le_left _ _).trans (by rw [Dsym_eq lam γ c _ hlam hγ hy0]; exact min_le_right _ _)
    linarith
  · intro hp
    subst hp
    refine ⟨by simp; linarith, by linarith, hfeas, ?_⟩
    intro q hq1 hq2 hsup
    obtain ⟨t, rfl⟩ : ∃ t, q = c + t := ⟨q - c, by ring⟩
    have ht0 : 0 ≤ t := by simp at hq1; linarith
    rw [profit_shift, profit_shift]
    apply mul_le_mul_of_nonneg_left _ hc0.le
    rw [min_eq_left hfeas, hDz]
    exact (min_le_left _ _).trans (D_le_half_z lam γ c t z hlam hγ hzp hzK hzd ht0)

theorem prop_1_d_aux (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) (hD2 : lam / 2 ≤ γ) :
    (∀ p : ℝ, IsSymNE lam γ 1 c p ↔ p = c + Real.sqrt (lam * γ / 2)) ∧
    (lam < dP lam γ 1 c (c + Real.sqrt (lam * γ / 2)) + dP lam γ 1 c (c + Real.sqrt (lam * γ / 2))) ∧
    (lam / 2 < γ →
      D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) <
        S lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) ∧
    (γ = lam / 2 →
      D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) =
        S lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) := by
  have hγ : 0 < γ := by linarith
  have hc1 : c < 1 := by linarith
  have hzp := zD_pos lam γ hlam hγ
  have hzm := zD_lt_m lam γ c hlam hγ hc0 hc hD1
  have hzd := dPs_zD lam γ c hlam hγ hc hD1
  have hzsq := zD_sq lam γ hlam hγ
  set z := Real.sqrt (lam * γ / 2) with hzdef
  have hDz : D lam γ 1 c (c + z) (c + z) = lam / 2 := by
    rw [Dsym_eq lam γ c _ hlam hγ hzp.le]
    exact min_eq_right hzd.le
  obtain ⟨hD, hS, hsq⟩ := DS_facts lam γ c z z hlam hγ hc0.le hc1 hzp hzm.le hzp.le
  rw [hDz] at hsq
  refine ⟨neD_iff lam γ c hlam hγ hc0 hc hD1 hD2, ?_, ?_, ?_⟩
  · rw [dP_shift]; linarith
  · intro hlt
    have hz2 : lam / 2 < z := by
      by_contra h; push Not at h
      nlinarith
    rw [hDz]
    nlinarith
  · intro heq
    have hz2 : z = lam / 2 := by
      have : z ^ 2 = (lam / 2) ^ 2 := by rw [hzsq, heq]; ring
      nlinarith
    rw [hDz]
    have h' : S lam γ 1 c (c + z) (c + z) ^ 2 = (lam / 2) ^ 2 := by
      rw [hsq, hz2]; ring
    nlinarith

/-! ### Data on the equilibrium -/

theorem cust_A (lam γ c y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1) (hy : 0 < y) :
    y + γ * dPs lam γ (1 - c) y / y - 2 * xA lam γ c = (y - xA lam γ c) ^ 2 / (y + lam * γ) := by
  have e := xA_eq lam γ c hlam hγ hc1
  have hu : 0 < y + lam * γ := by positivity
  have h1 : γ * dPs lam γ (1 - c) y / y = lam * γ * (1 - c - y) / (y + lam * γ) := by
    unfold dPs; field_simp
  rw [h1]
  field_simp
  linear_combination (-1) * e

theorem dataA (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc1 : c < 1)
    (hX2 : xA lam γ c ^ 2 ≤ lam * γ / 2) :
    (∀ y, 0 ≤ y → D lam γ 1 c (c + y) (c + y) ≤ D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c)) ∧
    γ * D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) = xA lam γ c ^ 2 ∧
    0 < D lam γ 1 c (c + xA lam γ c) (c + xA lam γ c) ∧
    (∀ y, 0 < y → y ≠ xA lam γ c →
      2 * xA lam γ c < y + γ * D lam γ 1 c (c + y) (c + y) / y) := by
  have hXp := xA_pos lam γ c hlam hγ hc1
  have h2 := two_dPs_le lam γ c hlam hγ hX2
  have hpt := DA_point lam γ c hlam hγ hc1 hX2
  have hmin : ∀ y, 0 ≤ y → D lam γ 1 c (c + y) (c + y) = dPs lam γ (1 - c) y := by
    intro y hy
    rw [Dsym_eq lam γ c y hlam hγ hy]
    exact min_eq_left (by have := dPs_le lam γ c y hlam hγ hc1 hy; linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hmin y hy, hpt]
    exact dPs_le lam γ c y hlam hγ hc1 hy
  · rw [hpt]; field_simp
  · rw [hpt]; positivity
  · intro y hy hne
    rw [hmin y hy.le]
    have := cust_A lam γ c y hlam hγ hc1 hy
    have hpos : 0 < (y - xA lam γ c) ^ 2 / (y + lam * γ) := by
      have : y - xA lam γ c ≠ 0 := sub_ne_zero.mpr hne
      positivity
    linarith

theorem z_lt_xA (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) :
    Real.sqrt (lam * γ / 2) < xA lam γ c := by
  have hc1 : c < 1 := by linarith
  have e := xA_eq lam γ c hlam hγ hc1
  have hz := zD_sq lam γ hlam hγ
  have hlt := zD_lt lam γ c hlam hγ hc hD1
  have hzp := zD_pos lam γ hlam hγ
  have hK : 0 < lam * γ := by positivity
  set z := Real.sqrt (lam * γ / 2)
  set X := xA lam γ c
  by_contra h
  push Not at h
  have hXp := xA_pos lam γ c hlam hγ hc1
  have h1 : X ^ 2 ≤ z ^ 2 := by nlinarith
  have h2 : lam * γ * (1 - c) ≤ lam * γ * (1 / 2 + 2 * z) := by nlinarith
  have h3 : 1 - c ≤ 1 / 2 + 2 * z := le_of_mul_le_mul_left h2 hK
  linarith

theorem dataZ (lam γ c : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 < c) (hc : c < 1 / 2)
    (hD1 : γ < (1 / 2 - c) ^ 2 / (2 * lam)) :
    (∀ y, 0 ≤ y → D lam γ 1 c (c + y) (c + y) ≤
        D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2))) ∧
    γ * D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) =
        Real.sqrt (lam * γ / 2) ^ 2 ∧
    0 < D lam γ 1 c (c + Real.sqrt (lam * γ / 2)) (c + Real.sqrt (lam * γ / 2)) ∧
    (∀ y, 0 < y → y ≠ Real.sqrt (lam * γ / 2) →
      2 * Real.sqrt (lam * γ / 2) < y + γ * D lam γ 1 c (c + y) (c + y) / y) := by
  have hc1 : c < 1 := by linarith
  have hzp := zD_pos lam γ hlam hγ
  have hzd := dPs_zD lam γ c hlam hγ hc hD1
  have hzsq := zD_sq lam γ hlam hγ
  have hzA := z_lt_xA lam γ c hlam hγ hc hD1
  set z := Real.sqrt (lam * γ / 2) with hzdef
  have hDz : D lam γ 1 c (c + z) (c + z) = lam / 2 := by
    rw [Dsym_eq lam γ c _ hlam hγ hzp.le]
    exact min_eq_right hzd.le
  rw [hDz]
  refine ⟨?_, ?_, by positivity, ?_⟩
  · intro y hy
    rw [Dsym_eq lam γ c y hlam hγ hy]
    exact min_le_right _ _
  · rw [hzsq]; ring
  · intro y hy hne
    rw [Dsym_eq lam γ c y hlam hγ hy.le]
    by_cases hcase : dPs lam γ (1 - c) y ≤ lam / 2
    · rw [min_eq_left hcase]
      have := cust_A lam γ c y hlam hγ hc1 hy
      have : 0 ≤ (y - xA lam γ c) ^ 2 / (y + lam * γ) := by positivity
      linarith
    · push Not at hcase
      rw [min_eq_right hcase.le]
      have hpos : 0 < (y - z) ^ 2 / y := by
        have : y - z ≠ 0 := sub_ne_zero.mpr hne
        positivity
      have e : y + γ * (lam / 2) / y - 2 * z = (y - z) ^ 2 / y := by
        field_simp
        nlinarith [hzsq]
      linarith

def Ztype (lam γ c : ℝ) : Prop := c < 1 / 2 ∧ γ < (1 / 2 - c) ^ 2 / (2 * lam)

open Classical in
noncomputable def XNE (lam γ c : ℝ) : ℝ :=
  if Ztype lam γ c then Real.sqrt (lam * γ / 2) else xA lam γ c

theorem region_pos (lam γ c : ℝ) (hlam : 0 < lam) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) : 0 < γ := by
  rcases hR with h | h
  · have : 0 < lam * (1 - c) / (1 + 2 * lam) := by
      have : 0 < 1 - c := by linarith
      positivity
    linarith [h.2]
  · linarith [h.2]

theorem region_Z (lam γ c : ℝ) (hZ : Ztype lam γ c)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) : lam / 2 ≤ γ := by
  rcases hR with h | h
  · exfalso; linarith [h.1, hZ.2]
  · exact h.2

theorem region_A (lam γ c : ℝ) (hlam : 0 < lam) (hc1 : c < 1) (hZ : ¬ Ztype lam γ c)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) :
    ((1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c) ∧ lam * (1 - c) / (1 + 2 * lam) ≤ γ := by
  have hA1 : (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∨ 1 / 2 ≤ c := by
    by_cases hc : c < 1 / 2
    · left
      by_contra h
      push Not at h
      exact hZ ⟨hc, h⟩
    · right; linarith
  refine ⟨hA1, ?_⟩
  rcases hR with h | h
  · exact h.2
  · have hc : 1 / 2 ≤ c := by
      by_contra hc
      push Not at hc
      exact hZ ⟨hc, h.1⟩
    have := h.2
    rw [div_le_iff₀ (by positivity)]
    nlinarith

theorem ne_data (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) :
    0 < γ ∧ 0 < XNE lam γ c ∧ XNE lam γ c < 1 - c ∧
    (∀ p, IsSymNE lam γ 1 c p ↔ p = c + XNE lam γ c) ∧
    (∀ y, 0 ≤ y → D lam γ 1 c (c + y) (c + y) ≤
        D lam γ 1 c (c + XNE lam γ c) (c + XNE lam γ c)) ∧
    γ * D lam γ 1 c (c + XNE lam γ c) (c + XNE lam γ c) = XNE lam γ c ^ 2 ∧
    0 < D lam γ 1 c (c + XNE lam γ c) (c + XNE lam γ c) ∧
    (∀ y, 0 < y → y ≠ XNE lam γ c →
      2 * XNE lam γ c < y + γ * D lam γ 1 c (c + y) (c + y) / y) := by
  have hγ := region_pos lam γ c hlam hc1 hR
  by_cases hZ : Ztype lam γ c
  · have hD2 := region_Z lam γ c hZ hR
    have hc : c < 1 / 2 := hZ.1
    have hD1 := hZ.2
    unfold XNE
    rw [if_pos hZ]
    exact ⟨hγ, zD_pos lam γ hlam hγ, zD_lt_m lam γ c hlam hγ hc0 hc hD1,
      neD_iff lam γ c hlam hγ hc0 hc hD1 hD2, dataZ lam γ c hlam hγ hc0 hc hD1⟩
  · obtain ⟨hA1, hA2⟩ := region_A lam γ c hlam hc1 hZ hR
    have hX2 := xA_sq_le lam γ c hlam hγ hc1 hA1
    have hXg := (xA_le_gamma_iff lam γ c hlam hγ hc1).mpr hA2
    unfold XNE
    rw [if_neg hZ]
    exact ⟨hγ, xA_pos lam γ c hlam hγ hc1, xA_lt lam γ c hlam hγ hc1,
      neA_iff lam γ c hlam hγ hc0 hc1 hX2 hXg, dataA lam γ c hlam hγ hc1 hX2⟩

theorem xA_mono (lam lam' γ c : ℝ) (hlam : 0 < lam) (hlt : lam < lam') (hγ : 0 < γ) (hc1 : c < 1) :
    xA lam γ c < xA lam' γ c := by
  have hlam' : 0 < lam' := by linarith
  have e := xA_eq lam γ c hlam hγ hc1
  have e' := xA_eq lam' γ c hlam' hγ hc1
  have hp := xA_pos lam γ c hlam hγ hc1
  have hp' := xA_pos lam' γ c hlam' hγ hc1
  set X := xA lam γ c
  set X' := xA lam' γ c
  by_contra h
  push Not at h
  have hK : 0 < lam * γ := by positivity
  have hK' : lam * γ < lam' * γ := by nlinarith
  -- m = X²/K + 2X
  have m1 : (1 - c) = X ^ 2 / (lam * γ) + 2 * X := by
    field_simp; linarith
  have m2 : (1 - c) = X' ^ 2 / (lam' * γ) + 2 * X' := by
    have : 0 < lam' * γ := by positivity
    field_simp; linarith
  have hK'p : 0 < lam' * γ := by positivity
  have h1 : X' ^ 2 / (lam' * γ) ≤ X ^ 2 / (lam' * γ) :=
    div_le_div_of_nonneg_right (by nlinarith) hK'p.le
  have h2 : X ^ 2 / (lam' * γ) < X ^ 2 / (lam * γ) :=
    div_lt_div_of_pos_left (by positivity) hK hK'
  linarith

theorem XNE_mono (lam lam' γ c : ℝ) (hlam : 0 < lam) (hlt : lam < lam') (hc0 : 0 < c) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) (hR' : RegionA lam' γ c ∨ RegionD lam' γ c) :
    XNE lam γ c < XNE lam' γ c := by
  have hlam' : 0 < lam' := by linarith
  have hγ := region_pos lam γ c hlam hc1 hR
  by_cases hZ : Ztype lam γ c
  · have hD1 := hZ.2
    have hc := hZ.1
    have h1 : XNE lam γ c = Real.sqrt (lam * γ / 2) := by unfold XNE; rw [if_pos hZ]
    rw [h1]
    by_cases hZ' : Ztype lam' γ c
    · have : XNE lam' γ c = Real.sqrt (lam' * γ / 2) := by unfold XNE; rw [if_pos hZ']
      rw [this]
      apply Real.sqrt_lt_sqrt (by positivity)
      have := mul_lt_mul_of_pos_right hlt hγ
      linarith
    · have : XNE lam' γ c = xA lam' γ c := by unfold XNE; rw [if_neg hZ']
      rw [this]
      exact (z_lt_xA lam γ c hlam hγ hc hD1).trans (xA_mono lam lam' γ c hlam hlt hγ hc1)
  · have h1 : XNE lam γ c = xA lam γ c := by unfold XNE; rw [if_neg hZ]
    have hZ' : ¬ Ztype lam' γ c := by
      rintro ⟨hc, hD1'⟩
      apply hZ
      refine ⟨hc, ?_⟩
      have hpos : 0 < (1 / 2 - c) ^ 2 := by
        have : 1 / 2 - c ≠ 0 := by linarith
        positivity
      have : (1 / 2 - c) ^ 2 / (2 * lam') < (1 / 2 - c) ^ 2 / (2 * lam) := by
        apply div_lt_div_of_pos_left hpos (by positivity) (by linarith)
      linarith
    have h2 : XNE lam' γ c = xA lam' γ c := by unfold XNE; rw [if_neg hZ']
    rw [h1, h2]
    exact xA_mono lam lam' γ c hlam hlt hγ hc1

theorem rho_facts (lam γ c t : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (ht : 0 < t) (htm : t ≤ 1 - c) (hD : 0 < D lam γ 1 c (c + t) (c + t)) :
    0 < rho lam γ 1 c (c + t) ∧ rho lam γ 1 c (c + t) ^ 2 = D lam γ 1 c (c + t) (c + t) / t ∧
      (t * rho lam γ 1 c (c + t)) ^ 2 = t * D lam γ 1 c (c + t) (c + t) := by
  obtain ⟨hD0, hS, hsq⟩ := DS_facts lam γ c t t hlam hγ hc0 hc1 ht htm ht.le
  set d := D lam γ 1 c (c + t) (c + t)
  set s := S lam γ 1 c (c + t) (c + t)
  have hs : 0 < s := by
    rcases hS.eq_or_lt with h | h
    · exfalso; rw [← h] at hsq; nlinarith [mul_pos ht hD]
    · exact h
  have hr : rho lam γ 1 c (c + t) = d / s := rfl
  rw [hr]
  refine ⟨div_pos hD hs, ?_, ?_⟩
  · rw [div_pow, hsq]; field_simp
  · rw [mul_pow, div_pow, hsq]; field_simp

theorem Dsym_pos (lam γ c y : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hy : 0 < y) (hym : y < 1 - c) :
    0 < D lam γ 1 c (c + y) (c + y) := by
  rw [Dsym_eq lam γ c y hlam hγ hy.le]
  apply lt_min _ (by positivity)
  unfold dPs
  have : 0 < 1 - c - y := by linarith
  positivity

theorem uD0_eq (lam γ c v t : ℝ) :
    uD0 lam γ 1 c v (c + t) = 1 - v - (c + t) - γ * rho lam γ 1 c (c + t) ^ 2 := rfl

theorem uD1_eq (lam γ c v t : ℝ) :
    uD1 lam γ 1 c v (c + t) = v - (c + t) - γ * rho lam γ 1 c (c + t) ^ 2 := rfl

theorem uS_eq (lam γ c k t : ℝ) :
    uS lam γ 1 c k (c + t) = -k + t * rho lam γ 1 c (c + t) := by
  unfold uS
  have : (1:ℝ) * (c + t) - c = t := by ring
  rw [this]

theorem lt_of_sq_lt (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra h'
  push Not at h'
  nlinarith [mul_nonneg (sub_nonneg.2 h') (add_nonneg hb (hb.trans h'))]

theorem prop_3_aux (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) :
    (∃ p : ℝ, IsSymNE lam γ 1 c p) ∧
    (∀ lamHat : ℝ, lam < lamHat → (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
      (∃ q : ℝ, IsSymNE lamHat γ 1 c q) ∧
      ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
        uD0 lamHat γ 1 c v q < uD0 lam γ 1 c v p ∧
        uD1 lamHat γ 1 c v q < uD1 lam γ 1 c v p ∧
        uS lam γ 1 c k p < uS lamHat γ 1 c k q) ∧
    (∃ Λ : EReal, (lam : EReal) < Λ ∧
      ∀ lamHat : ℝ, lam < lamHat → (lamHat : EReal) ≤ Λ →
        (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
        ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
          uD0 lamHat γ 1 c v p < uD0 lamHat γ 1 c v q ∧
          uD1 lamHat γ 1 c v p < uD1 lamHat γ 1 c v q ∧
          uS lamHat γ 1 c k p < uS lamHat γ 1 c k q) := by
  obtain ⟨hγ, hXp, hXm, hNE, hmax, hFOC, hDpos, hcust⟩ := ne_data lam γ c hlam hc0 hc1 hR
  set X := XNE lam γ c with hXdef
  have hρ := rho_facts lam γ c X hlam hγ hc0.le hc1 hXp hXm.le hDpos
  refine ⟨⟨c + X, (hNE _).mpr rfl⟩, ?_, ?_⟩
  · intro lamHat hlt hR'
    have hlam' : 0 < lamHat := by linarith
    obtain ⟨_, hX'p, hX'm, hNE', hmax', hFOC', hDpos', hcust'⟩ :=
      ne_data lamHat γ c hlam' hc0 hc1 hR'
    set X' := XNE lamHat γ c with hX'def
    have hXX' : X < X' := XNE_mono lam lamHat γ c hlam hlt hc0 hc1 hR hR'
    have hρ' := rho_facts lamHat γ c X' hlam' hγ hc0.le hc1 hX'p hX'm.le hDpos'
    refine ⟨⟨c + X', (hNE' _).mpr rfl⟩, ?_⟩
    intro p q hp hq v k
    rw [(hNE p).mp hp, (hNE' q).mp hq]
    set D1 := D lam γ 1 c (c + X) (c + X)
    set D2 := D lamHat γ 1 c (c + X') (c + X')
    have g1 : γ * rho lam γ 1 c (c + X) ^ 2 = X := by
      rw [hρ.2.1]; field_simp; linarith
    have g2 : γ * rho lamHat γ 1 c (c + X') ^ 2 = X' := by
      rw [hρ'.2.1]; field_simp; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [uD0_eq, uD0_eq, g1, g2]; linarith
    · rw [uD1_eq, uD1_eq, g1, g2]; linarith
    · rw [uS_eq, uS_eq]
      have hXD : X * D1 < X' * D2 := by
        by_contra h
        push Not at h
        have : γ * (X' * D2) ≤ γ * (X * D1) := mul_le_mul_of_nonneg_left h hγ.le
        have e1 : γ * (X * D1) = X ^ 3 := by rw [← mul_assoc, mul_comm γ X, mul_assoc, hFOC]; ring
        have e2 : γ * (X' * D2) = X' ^ 3 := by rw [← mul_assoc, mul_comm γ X', mul_assoc, hFOC']; ring
        rw [e1, e2] at this
        nlinarith [pow_lt_pow_left₀ hXX' hXp.le (by norm_num : (3:ℕ) ≠ 0)]
      have : X * rho lam γ 1 c (c + X) < X' * rho lamHat γ 1 c (c + X') := by
        apply lt_of_sq_lt _ _ (mul_nonneg hX'p.le hρ'.1.le)
        rw [hρ.2.2, hρ'.2.2]; exact hXD
      linarith
  · refine ⟨⊤, EReal.coe_lt_top lam, ?_⟩
    intro lamHat hlt _ hR' p q hp hq v k
    have hlam' : 0 < lamHat := by linarith
    obtain ⟨_, hX'p, hX'm, hNE', hmax', hFOC', hDpos', hcust'⟩ :=
      ne_data lamHat γ c hlam' hc0 hc1 hR'
    set X' := XNE lamHat γ c with hX'def
    have hXX' : X < X' := XNE_mono lam lamHat γ c hlam hlt hc0 hc1 hR hR'
    have hρ' := rho_facts lamHat γ c X' hlam' hγ hc0.le hc1 hX'p hX'm.le hDpos'
    rw [(hNE p).mp hp, (hNE' q).mp hq]
    have hDh : 0 < D lamHat γ 1 c (c + X) (c + X) := Dsym_pos lamHat γ c X hlam' hγ hXp hXm
    have hρh := rho_facts lamHat γ c X hlam' hγ hc0.le hc1 hXp hXm.le hDh
    set D1 := D lamHat γ 1 c (c + X) (c + X)
    set D2 := D lamHat γ 1 c (c + X') (c + X')
    have g2 : γ * rho lamHat γ 1 c (c + X') ^ 2 = X' := by
      rw [hρ'.2.1]; field_simp; linarith
    have g1 : 2 * X' < X + γ * rho lamHat γ 1 c (c + X) ^ 2 := by
      rw [hρh.2.1]
      have := hcust' X hXp (ne_of_lt hXX')
      rw [mul_div_assoc] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · rw [uD0_eq, uD0_eq, g2]; linarith
    · rw [uD1_eq, uD1_eq, g2]; linarith
    · rw [uS_eq, uS_eq]
      have hXD : X * D1 < X' * D2 := by
        have h1 : D1 ≤ D2 := hmax' X hXp.le
        have h2 : X * D1 ≤ X * D2 := mul_le_mul_of_nonneg_left h1 hXp.le
        have h3 : X * D2 < X' * D2 := mul_lt_mul_of_pos_right hXX' hDpos'
        linarith
      have : X * rho lamHat γ 1 c (c + X) < X' * rho lamHat γ 1 c (c + X') := by
        apply lt_of_sq_lt _ _ (mul_nonneg hX'p.le hρ'.1.le)
        rw [hρh.2.2, hρ'.2.2]; exact hXD
      linarith

end CongestedPlatforms.Surge

open CongestedPlatforms.Surge

theorem solution (lam γ c : ℝ) (hlam : 0 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hR : RegionA lam γ c ∨ RegionD lam γ c) :
    (∃ p : ℝ, IsSymNE lam γ 1 c p) ∧
    (∀ lamHat : ℝ, lam < lamHat → (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
      (∃ q : ℝ, IsSymNE lamHat γ 1 c q) ∧
      ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
        uD0 lamHat γ 1 c v q < uD0 lam γ 1 c v p ∧
        uD1 lamHat γ 1 c v q < uD1 lam γ 1 c v p ∧
        uS lam γ 1 c k p < uS lamHat γ 1 c k q) ∧
    (∃ Λ : EReal, (lam : EReal) < Λ ∧
      ∀ lamHat : ℝ, lam < lamHat → (lamHat : EReal) ≤ Λ →
        (RegionA lamHat γ c ∨ RegionD lamHat γ c) →
        ∀ p q : ℝ, IsSymNE lam γ 1 c p → IsSymNE lamHat γ 1 c q → ∀ v k : ℝ,
          uD0 lamHat γ 1 c v p < uD0 lamHat γ 1 c v q ∧
          uD1 lamHat γ 1 c v p < uD1 lamHat γ 1 c v q ∧
          uS lamHat γ 1 c k p < uS lamHat γ 1 c k q) := by
  exact prop_3_aux lam γ c hlam hc0 hc1 hR
