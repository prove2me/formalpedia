-- Prove2me | solution 1 for EqualTwoSquares.four_factor_param
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:20:19.37692+00:00
-- url     : https://prove2.me/submissions/e830e247-7314-4acc-b621-5d59eb233b01

-- Public-mission submission for EqualTwoSquares.four_factor_param.
--
-- `g` is bound as a local constant so that rewriting with `X = r*g` and `U = s*g` cannot
-- reach inside `Int.gcd X U`.

import Mathlib

theorem solution (X Y U V : ℤ) (h : X * Y = U * V) :
    ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by
  by_cases hX : X = 0
  · by_cases hU : U = 0
    · refine ⟨0, 1, V, Y, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hU]
    · have hV : V = 0 := by
        have h' := h
        rw [hX] at h'
        have hUV : U * V = 0 := by simpa using h'.symm
        exact (mul_eq_zero.mp hUV).resolve_left hU
      refine ⟨U, Y, 0, 1, ?_, ?_, ?_, ?_⟩ <;> simp [hX, hV]
  · by_cases hU : U = 0
    · have hY : Y = 0 := by
        have h' := h
        rw [hU] at h'
        have hXY : X * Y = 0 := by simpa using h'
        exact (mul_eq_zero.mp hXY).resolve_left hX
      refine ⟨X, V, 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [hU, hY]
    · have hgpos : 0 < Int.gcd X U := Int.gcd_pos_of_ne_zero_left U hX
      let g : ℤ := (Int.gcd X U : ℤ)
      obtain ⟨r, s, hcop, hXeq0, hUeq0⟩ := Int.exists_gcd_one (m := X) (n := U) hgpos
      have hXeq : X = r * g := by simpa [g] using hXeq0
      have hUeq : U = s * g := by simpa [g] using hUeq0
      have hgne : g ≠ 0 := by
        dsimp [g]
        exact_mod_cast (ne_of_gt hgpos)
      -- Cancel the nonzero gcd from X*Y = U*V after substituting X = r*g and U = s*g.
      have hmul : g * (r * Y) = g * (s * V) := by
        calc
          g * (r * Y) = (r * g) * Y := by ring
          _ = X * Y := by rw [← hXeq]
          _ = U * V := h
          _ = (s * g) * V := by rw [hUeq]
          _ = g * (s * V) := by ring
      have hrY : r * Y = s * V := mul_left_cancel₀ hgne hmul
      have hr_ne : r ≠ 0 := by
        intro hr
        apply hX
        calc
          X = r * g := hXeq
          _ = 0 := by rw [hr]; ring
      have hs_ne : s ≠ 0 := by
        intro hs
        apply hU
        calc
          U = s * g := hUeq
          _ = 0 := by rw [hs]; ring
      -- Bezout for the coprime pair (r, s): 1 = r*A + s*B.
      have hbez : (1 : ℤ) = r * Int.gcdA r s + s * Int.gcdB r s := by
        have := Int.gcd_eq_gcd_ab r s
        simpa [hcop] using this
      have hsry : s ∣ r * Y := ⟨V, hrY⟩
      have hrsv : r ∣ s * V := ⟨Y, hrY.symm⟩
      have hsY : s ∣ Y := by
        have h1 : s ∣ (r * Y) * Int.gcdA r s := dvd_mul_of_dvd_left hsry _
        have h2 : s ∣ s * (Y * Int.gcdB r s) := dvd_mul_right s _
        have hsum := dvd_add h1 h2
        have heq : (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) = Y := by
          calc
            (r * Y) * Int.gcdA r s + s * (Y * Int.gcdB r s) =
                Y * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
            _ = Y * 1 := by rw [hbez]
            _ = Y := by ring
        rwa [heq] at hsum
      have hrV : r ∣ V := by
        have h1 : r ∣ r * (V * Int.gcdA r s) := dvd_mul_right r _
        have h2 : r ∣ (s * V) * Int.gcdB r s := dvd_mul_of_dvd_left hrsv _
        have hsum := dvd_add h1 h2
        have heq : r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s = V := by
          calc
            r * (V * Int.gcdA r s) + (s * V) * Int.gcdB r s =
                V * (r * Int.gcdA r s + s * Int.gcdB r s) := by ring
            _ = V * 1 := by rw [hbez]
            _ = V := by ring
        rwa [heq] at hsum
      rcases hsY with ⟨q, hq⟩
      rcases hrV with ⟨q', hq'⟩
      have hqq : q = q' := by
        have hmain : r * s * q = r * s * q' := by
          calc
            r * s * q = r * (s * q) := by ring
            _ = r * Y := by rw [← hq]
            _ = s * V := hrY
            _ = s * (r * q') := by rw [hq']
            _ = r * s * q' := by ring
        exact mul_left_cancel₀ (mul_ne_zero hr_ne hs_ne) hmain
      refine ⟨g, q, r, s, ?_, ?_, ?_, ?_⟩
      · calc
          X = r * g := hXeq
          _ = g * r := by ring
      · rw [hq]
        ring
      · calc
          U = s * g := hUeq
          _ = g * s := by ring
      · rw [hq', ← hqq]
        ring
