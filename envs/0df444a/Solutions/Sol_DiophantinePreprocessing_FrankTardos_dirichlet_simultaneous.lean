-- Prove2me | solution 1 for DiophantinePreprocessing.FrankTardos.dirichlet_simultaneous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:36:15.513994+00:00
-- url     : https://prove2.me/submissions/324f9689-ba92-4db0-a778-5add17435752

import Mathlib

private theorem fract_close (N : ℕ) (hN : 0 < N) (x y : ℝ)
    (h : ⌊(N : ℝ) * Int.fract x⌋₊ = ⌊(N : ℝ) * Int.fract y⌋₊) :
    |Int.fract y - Int.fract x| < 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx1 : ((⌊(N : ℝ) * Int.fract x⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * Int.fract x :=
    Nat.floor_le (mul_nonneg hNR.le (Int.fract_nonneg _))
  have hx2 : (N : ℝ) * Int.fract x < ((⌊(N : ℝ) * Int.fract x⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hy1 : ((⌊(N : ℝ) * Int.fract y⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * Int.fract y :=
    Nat.floor_le (mul_nonneg hNR.le (Int.fract_nonneg _))
  have hy2 : (N : ℝ) * Int.fract y < ((⌊(N : ℝ) * Int.fract y⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [h] at hx1 hx2
  have habs : |(N : ℝ) * (Int.fract y - Int.fract x)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hNR] at habs
  rw [lt_div_iff₀ hNR, mul_comm]
  exact habs

theorem solution (n N : ℕ) (hN : 0 < N) (α : Fin n → ℝ) :
    ∃ (p : Fin n → ℤ) (q : ℤ), 1 ≤ q ∧ q ≤ (N : ℤ) ^ n ∧
      ∀ i, |(q : ℝ) * α i - (p i : ℝ)| < 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : ∀ (k : ℕ) (i : Fin n), ⌊(N : ℝ) * Int.fract ((k : ℝ) * α i)⌋₊ < N := by
    intro k i
    rw [Nat.floor_lt (mul_nonneg hNR.le (Int.fract_nonneg _))]
    have h1 : Int.fract ((k : ℝ) * α i) < 1 := Int.fract_lt_one _
    calc (N : ℝ) * Int.fract ((k : ℝ) * α i) < (N : ℝ) * 1 :=
          mul_lt_mul_of_pos_left h1 hNR
      _ = (N : ℝ) := mul_one _
  have hcard : Fintype.card (Fin n → Fin N) < Fintype.card (Fin (N ^ n + 1)) := by
    simp
  obtain ⟨k1, k2, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (N ^ n + 1) => fun i : Fin n =>
        (⟨⌊(N : ℝ) * Int.fract (((k : ℕ) : ℝ) * α i)⌋₊, hlt (k : ℕ) i⟩ : Fin N)) hcard
  have hm : ∀ i : Fin n, ⌊(N : ℝ) * Int.fract (((k1 : ℕ) : ℝ) * α i)⌋₊
      = ⌊(N : ℝ) * Int.fract (((k2 : ℕ) : ℝ) * α i)⌋₊ := by
    intro i
    exact congrArg Fin.val (congrFun heq i)
  have main : ∀ a b : Fin (N ^ n + 1), (a : ℕ) < (b : ℕ) →
      (∀ i : Fin n, ⌊(N : ℝ) * Int.fract (((a : ℕ) : ℝ) * α i)⌋₊
        = ⌊(N : ℝ) * Int.fract (((b : ℕ) : ℝ) * α i)⌋₊) →
      ∃ (p : Fin n → ℤ) (q : ℤ), 1 ≤ q ∧ q ≤ (N : ℤ) ^ n ∧
        ∀ i, |(q : ℝ) * α i - (p i : ℝ)| < 1 / (N : ℝ) := by
    intro a b hab hfl
    have hbn : (b : ℕ) < N ^ n + 1 := b.isLt
    have hpow : ((N ^ n : ℕ) : ℤ) = (N : ℤ) ^ n := by push_cast; ring
    refine ⟨fun i => ⌊((b : ℕ) : ℝ) * α i⌋ - ⌊((a : ℕ) : ℝ) * α i⌋,
      ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ), by omega, by omega, ?_⟩
    intro i
    have hfr : ((((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) : ℤ) : ℝ) * α i
        - ((⌊((b : ℕ) : ℝ) * α i⌋ - ⌊((a : ℕ) : ℝ) * α i⌋ : ℤ) : ℝ)
        = Int.fract (((b : ℕ) : ℝ) * α i) - Int.fract (((a : ℕ) : ℝ) * α i) := by
      rw [← Int.self_sub_floor, ← Int.self_sub_floor]
      push_cast
      ring
    rw [hfr]
    exact fract_close N hN _ _ (hfl i)
  rcases lt_trichotomy ((k1 : ℕ)) ((k2 : ℕ)) with h | h | h
  · exact main k1 k2 h hm
  · exact absurd (Fin.val_injective h) hne
  · exact main k2 k1 h (fun i => (hm i).symm)
