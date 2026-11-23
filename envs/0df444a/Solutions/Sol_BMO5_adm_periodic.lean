-- Prove2me | solution 1 for BMO5.adm_periodic
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T17:30:43.753581+00:00
-- url     : https://prove2.me/submissions/2a02df2b-2d37-4e3d-af8a-c760a1406344

import Mathlib
import Definitions.Def_BMO5Adm

namespace BMO5P

theorem four_pow : ∀ m : ℕ, (3:ℤ) ^ (m + 1) ∣ 4 ^ (3 ^ m) - 1
  | 0 => by norm_num
  | m + 1 => by
    have ih := four_pow m
    have h3 : (3:ℤ) ∣ 4 ^ (3 ^ m) - 1 := dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero m)) ih
    have e : (4:ℤ) ^ (3 ^ (m + 1)) - 1 =
        (4 ^ (3 ^ m) - 1) * ((4 ^ (3 ^ m) - 1) ^ 2 + 3 * 4 ^ (3 ^ m)) := by
      rw [pow_succ 3 m, pow_mul]; ring
    rw [e, pow_succ (3:ℤ) (m + 1)]
    exact mul_dvd_mul ih (dvd_add (dvd_pow h3 two_ne_zero) (dvd_mul_right 3 _))

theorem pw_congr (D x y : ℕ) (h : x % (2 * 3 ^ D) = y % (2 * 3 ^ D)) :
    (2:ℤ) ^ x ≡ 2 ^ y [ZMOD 3 ^ D] := by
  have h4 : (4:ℤ) ^ (3 ^ D) ≡ 1 [ZMOD 3 ^ D] :=
    (Int.modEq_iff_dvd.mpr (dvd_trans (pow_dvd_pow 3 (Nat.le_succ D)) (four_pow D))).symm
  have key : ∀ u v : ℕ, v ≤ u → u % (2 * 3 ^ D) = v % (2 * 3 ^ D) →
      (2:ℤ) ^ u ≡ 2 ^ v [ZMOD 3 ^ D] := by
    intro u v hvu huv
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hvu).mp huv.symm
    have hu : u = v + 2 * (3 ^ D * t) := by
      rw [← mul_assoc]
      generalize 2 * 3 ^ D * t = K at ht ⊢
      omega
    rw [hu, pow_add, pow_mul, pow_mul, show (2:ℤ) ^ 2 = 4 by norm_num]
    calc (2:ℤ) ^ v * ((4:ℤ) ^ 3 ^ D) ^ t ≡ 2 ^ v * 1 ^ t [ZMOD 3 ^ D] := (h4.pow t).mul_left _
      _ = 2 ^ v := by ring
  rcases le_total y x with hyx | hxy
  · exact key x y hyx h
  · exact (key y x hxy h.symm).symm

theorem okb_congr (i i' : ℕ) : ∀ (D m d : ℕ) (F F' : ℤ), F ≡ F' [ZMOD 3 ^ (m + D)] →
    (∀ e, d ≤ e → e < d + D → (2:ℤ) ^ (i - e - 1) ≡ 2 ^ (i' - e - 1) [ZMOD 3 ^ D]) →
    BMO5Adm.okb i D F m d = BMO5Adm.okb i' D F' m d
  | 0, m, d, F, F', _, _ => by simp [BMO5Adm.okb]
  | D + 1, m, d, F, F', hF, h2 => by
    have hF1 : F % 3 ^ (m + 1) = F' % 3 ^ (m + 1) :=
      Int.ModEq.of_dvd (pow_dvd_pow 3 (by omega)) hF
    have h2d := h2 d le_rfl (by omega)
    have hT : (3:ℤ) ^ m * (20 * 2 ^ (i - d - 1) - 3) ≡ 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)
        [ZMOD 3 ^ (m + (D + 1))] := by
      rw [pow_add]
      exact Int.ModEq.mul_left' ((h2d.mul_left 20).sub_right 3)
    have hG := hF.add hT
    have hG1 : (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) % 3 ^ (m + 1) =
        (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) % 3 ^ (m + 1) :=
      Int.ModEq.of_dvd (pow_dvd_pow 3 (by omega)) hG
    have r1 := okb_congr i i' D (m + 1) d F F'
      (by rw [show m + 1 + D = m + (D + 1) by omega]; exact hF)
      (fun e h1 h3 => (h2 e h1 (by omega)).of_dvd (pow_dvd_pow 3 (by omega)))
    have r2 := okb_congr i i' D (m + 1) (d + 1)
      (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3))
      (by rw [show m + 1 + D = m + (D + 1) by omega]; exact hG)
      (fun e h1 h3 => (h2 e (by omega) (by omega)).of_dvd (pow_dvd_pow 3 (by omega)))
    simp only [BMO5Adm.okb, hF1, hG1, r1, r2]

end BMO5P

theorem solution (D i j : ℕ) (hi : D + 1 ≤ i) (hj : D + 1 ≤ j)
    (h : i % (2 * 3 ^ D) = j % (2 * 3 ^ D)) : BMO5Adm.adm D i = BMO5Adm.adm D j := by
  unfold BMO5Adm.adm
  apply BMO5P.okb_congr i j D 0 0
  · rw [zero_add]
    have hm : i ≡ j [MOD 3 ^ D] := Nat.ModEq.of_dvd (Dvd.intro_left 2 rfl) h
    have hij : (i:ℤ) ≡ j [ZMOD 3 ^ D] := Int.modEq_iff_dvd.mpr (by
      have := Nat.modEq_iff_dvd.mp hm
      push_cast at this
      exact this)
    exact (((BMO5P.pw_congr D i j h).mul_left 20).add hij).add_right 1
  · intro e _ he
    apply BMO5P.pw_congr
    have hi' : i - e - 1 + (e + 1) = i := by omega
    have hj' : j - e - 1 + (e + 1) = j := by omega
    exact Nat.ModEq.add_right_cancel' (e + 1) (by unfold Nat.ModEq; rw [hi', hj']; exact h)
