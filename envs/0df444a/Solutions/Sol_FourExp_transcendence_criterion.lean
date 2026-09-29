-- Prove2me | solution 1 for FourExp.transcendence_criterion
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T04:28:56.808677+00:00
-- url     : https://prove2.me/submissions/194bf0ce-5193-4d00-99d4-aedfaaf90b53

import Mathlib
import Theorems.Thm_FourExp_transcendence_criterion_continuous

open Filter Topology

namespace FourExpInterp

/-- Piecewise-linear interpolation of `σ` through its values at the integers. -/
noncomputable def I (σ : ℝ → ℝ) (x : ℝ) : ℝ :=
  σ (⌊x⌋ : ℝ) + (x - ⌊x⌋) * (σ ((⌊x⌋ : ℝ) + 1) - σ (⌊x⌋ : ℝ))

theorem I_eq_of_mem (σ : ℝ → ℝ) (k : ℤ) (x : ℝ) (h1 : (k : ℝ) ≤ x) (h2 : x ≤ (k : ℝ) + 1) :
    I σ x = σ (k : ℝ) + (x - k) * (σ ((k : ℝ) + 1) - σ (k : ℝ)) := by
  rcases h2.lt_or_eq with h2 | h2
  · have hf : ⌊x⌋ = k := Int.floor_eq_iff.mpr ⟨h1, h2⟩
    simp [I, hf]
  · have hf : ⌊x⌋ = k + 1 := by
      rw [h2]; exact_mod_cast Int.floor_intCast (k + 1)
    unfold I
    rw [hf, h2]
    push_cast
    ring

theorem I_natCast (σ : ℝ → ℝ) (N : ℕ) : I σ (N : ℝ) = σ (N : ℝ) := by
  have := I_eq_of_mem σ (N : ℤ) (N : ℝ) (by simp) (by simp)
  simpa using this

theorem I_strictMono (σ : ℝ → ℝ) (hσ : StrictMono σ) : StrictMono (I σ) := by
  intro x y hxy
  have hk := Int.floor_le x
  have hk2 := Int.lt_floor_add_one x
  have hm := Int.floor_le y
  have hm2 := Int.lt_floor_add_one y
  have hIx := I_eq_of_mem σ ⌊x⌋ x hk hk2.le
  have hIy := I_eq_of_mem σ ⌊y⌋ y hm hm2.le
  have hΔx : 0 < σ ((⌊x⌋ : ℝ) + 1) - σ (⌊x⌋ : ℝ) := sub_pos.mpr (hσ (by linarith))
  have hΔy : 0 < σ ((⌊y⌋ : ℝ) + 1) - σ (⌊y⌋ : ℝ) := sub_pos.mpr (hσ (by linarith))
  rcases (Int.floor_mono hxy.le).lt_or_eq with hkm | hkm
  · have h1 : I σ x < σ ((⌊x⌋ : ℝ) + 1) := by
      rw [hIx]; nlinarith
    have h2 : σ ((⌊x⌋ : ℝ) + 1) ≤ σ (⌊y⌋ : ℝ) := by
      apply hσ.monotone
      have : ⌊x⌋ + 1 ≤ ⌊y⌋ := hkm
      exact_mod_cast this
    have h3 : σ (⌊y⌋ : ℝ) ≤ I σ y := by
      rw [hIy]; nlinarith
    linarith
  · rw [hIx, hIy, hkm]
    rw [hkm] at hΔx
    nlinarith

theorem I_continuous (σ : ℝ → ℝ) : Continuous (I σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  let L : ℤ → ℝ → ℝ := fun j y => σ (j : ℝ) + (y - j) * (σ ((j : ℝ) + 1) - σ (j : ℝ))
  have hL : ∀ j, Continuous (L j) := fun j => by
    simp only [L]; fun_prop
  have hk := Int.floor_le x
  have hk2 := Int.lt_floor_add_one x
  by_cases hx : (⌊x⌋ : ℝ) < x
  · have hev : I σ =ᶠ[𝓝 x] L ⌊x⌋ := by
      filter_upwards [Ioo_mem_nhds hx hk2] with y hy
      exact I_eq_of_mem σ ⌊x⌋ y hy.1.le hy.2.le
    exact (hL _).continuousAt.congr hev.symm
  · have hxk : x = (⌊x⌋ : ℝ) := le_antisymm (not_lt.mp hx) hk
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have hev : I σ =ᶠ[𝓝[≤] x] L (⌊x⌋ - 1) := by
        filter_upwards [Ioc_mem_nhdsLE (show ((⌊x⌋ - 1 : ℤ) : ℝ) < x by push_cast; linarith)]
          with y hy
        exact I_eq_of_mem σ (⌊x⌋ - 1) y hy.1.le (by push_cast; linarith [hy.2])
      have hval : I σ x = L (⌊x⌋ - 1) x :=
        I_eq_of_mem σ (⌊x⌋ - 1) x (by push_cast; linarith) (by push_cast; linarith)
      exact (hL _).continuousAt.continuousWithinAt.congr_of_eventuallyEq hev hval
    · have hev : I σ =ᶠ[𝓝[≥] x] L ⌊x⌋ := by
        filter_upwards [Ico_mem_nhdsGE hk2] with y hy
        exact I_eq_of_mem σ ⌊x⌋ y (by linarith [hy.1]) hy.2.le
      have hval : I σ x = L ⌊x⌋ x := I_eq_of_mem σ ⌊x⌋ x hk hk2.le
      exact (hL _).continuousAt.continuousWithinAt.congr_of_eventuallyEq hev hval

theorem I_tendsto (σ : ℝ → ℝ) (hσ : StrictMono σ) (ht : Tendsto σ atTop atTop) :
    Tendsto (I σ) atTop atTop := by
  have hshift : Tendsto (fun x : ℝ => σ (x - 1)) atTop atTop :=
    ht.comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id |>.congr (fun x => by simp [sub_eq_add_neg]))
  refine tendsto_atTop_mono (fun x => ?_) hshift
  have hk := Int.floor_le x
  have hk2 := Int.lt_floor_add_one x
  rw [I_eq_of_mem σ ⌊x⌋ x hk hk2.le]
  have h1 : σ (x - 1) ≤ σ (⌊x⌋ : ℝ) := hσ.monotone (by linarith)
  have h2 : 0 ≤ (x - ⌊x⌋) * (σ ((⌊x⌋ : ℝ) + 1) - σ (⌊x⌋ : ℝ)) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr (hσ.monotone (by linarith)))
  linarith

theorem one_le_floor {x : ℝ} (hx : 1 ≤ x) : (1 : ℝ) ≤ (⌊x⌋ : ℝ) := by
  have : (1 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast hx)
  exact_mod_cast this

theorem I_le (σ τ : ℝ → ℝ) (h : ∀ x : ℝ, 0 < x → τ x ≤ σ x) (x : ℝ) (hx : 1 ≤ x) :
    I τ x ≤ I σ x := by
  have hk := Int.floor_le x
  have hk2 := Int.lt_floor_add_one x
  have hk1 := one_le_floor hx
  rw [I_eq_of_mem τ ⌊x⌋ x hk hk2.le, I_eq_of_mem σ ⌊x⌋ x hk hk2.le]
  have h1 := h (⌊x⌋ : ℝ) (by linarith)
  have h2 := h ((⌊x⌋ : ℝ) + 1) (by linarith)
  have ht0 : 0 ≤ x - ⌊x⌋ := by linarith
  have ht1 : 0 ≤ 1 - (x - ⌊x⌋) := by linarith
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h2), mul_nonneg ht1 (sub_nonneg.mpr h1)]

theorem I_growth (σ : ℝ → ℝ) (a : ℝ) (h : ∀ x : ℝ, 0 < x → σ (x + 1) ≤ a * σ x) (x : ℝ)
    (hx : 1 ≤ x) : I σ (x + 1) ≤ a * I σ x := by
  have hk := Int.floor_le x
  have hk2 := Int.lt_floor_add_one x
  have hk1 := one_le_floor hx
  have e1 := I_eq_of_mem σ (⌊x⌋ + 1) (x + 1) (by push_cast; linarith) (by push_cast; linarith)
  have e2 := I_eq_of_mem σ ⌊x⌋ x hk hk2.le
  push_cast at e1
  rw [e1, e2]
  have g1 := h (⌊x⌋ : ℝ) (by linarith)
  have g2 := h ((⌊x⌋ : ℝ) + 1) (by linarith)
  have ht0 : 0 ≤ x - ⌊x⌋ := by linarith
  have ht1 : 0 ≤ 1 - (x - ⌊x⌋) := by linarith
  have hx1 : x + 1 - ((⌊x⌋ : ℝ) + 1) = x - ⌊x⌋ := by ring
  rw [hx1]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr g2), mul_nonneg ht1 (sub_nonneg.mpr g1)]

end FourExpInterp

open FourExpInterp in
theorem solution
    (α : ℂ) (ε : ℝ) (hε : 0 < ε)
    (σ₁ σ₂ : ℝ → ℝ) (hσ₁ : StrictMono σ₁) (hσ₂ : StrictMono σ₂)
    (hσ₁t : Tendsto σ₁ atTop atTop) (hσ₂t : Tendsto σ₂ atTop atTop)
    (a₁ a₂ : ℝ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (h₂₁ : ∀ x : ℝ, 0 < x → σ₂ x ≤ σ₁ x)
    (hgrowth₁ : ∀ x : ℝ, 0 < x → σ₁ (x + 1) ≤ a₁ * σ₁ x)
    (hgrowth₂ : ∀ x : ℝ, 0 < x → σ₂ (x + 1) ≤ a₂ * σ₂ x)
    (N₀ : ℕ) (P : ℕ → Polynomial ℤ)
    (hP_ne : ∀ N : ℕ, N₀ < N → P N ≠ 0)
    (hP_height : ∀ N : ℕ, N₀ < N → ∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N))
    (hP_deg : ∀ N : ℕ, N₀ < N → ((P N).natDegree : ℝ) ≤ σ₂ N)
    (hP_small : ∀ N : ℕ, N₀ < N →
      ‖Polynomial.aeval α (P N)‖ <
        Real.exp (-(max (10 + ε) ((4 + ε) * (a₁ * a₂)) * σ₁ N * σ₂ N))) :
    IsAlgebraic ℚ α := by
  apply FourExp.transcendence_criterion_continuous α ε hε (I σ₁) (I σ₂)
    (I_strictMono σ₁ hσ₁) (I_strictMono σ₂ hσ₂) (I_continuous σ₁) (I_continuous σ₂)
    (I_tendsto σ₁ hσ₁ hσ₁t) (I_tendsto σ₂ hσ₂ hσ₂t) a₁ a₂ ha₁ ha₂
    (fun x hx => I_le σ₁ σ₂ h₂₁ x hx) (fun x hx => I_growth σ₁ a₁ hgrowth₁ x hx)
    (fun x hx => I_growth σ₂ a₂ hgrowth₂ x hx) N₀ P hP_ne
  · intro N hN i
    rw [I_natCast]
    exact hP_height N hN i
  · intro N hN
    rw [I_natCast]
    exact hP_deg N hN
  · intro N hN
    rw [I_natCast, I_natCast]
    exact hP_small N hN
