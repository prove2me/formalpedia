-- Prove2me | solution 1 for Erdos287.grouped_prime_occupancy_reduction
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:42:43.92874+00:00
-- url     : https://prove2.me/submissions/c59430ad-d36b-4e29-8503-6bda49682a00

import Mathlib
import Theorems.Thm_Erdos287_compatible_slopes_realize_distance_band
import Theorems.Thm_Erdos287_gap_from_uniform_prime_window

open Finset

set_option autoImplicit false

/-- Prescribed equal-sized groups admit fixed prime forms for the density reduction. -/
theorem solution (N K u v : ℕ) (hK : 0 < K) (hu : 0 < u) (huv : u ≤ v)
    (hv : 2 * u ≤ v + 2) (hve : (v : ℝ) < Real.exp 1 * u) :
    ∃ (b : ℕ → ℕ → ℕ) (α β : ℝ) (M₀ : ℕ), 0 < α ∧ α < β ∧
      (∀ s < N, ∀ j < K, 0 < b s j) ∧
      (∀ s r i j, s < N → r < N → i < K → j < K →
        b s i = b r j → s = r ∧ i = j) ∧
      ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
        (∀ i, i < k → 1 < f i) →
        (∀ i j, i < j → j < k → f i < f j) →
        (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
        M₀ ≤ f (k - 1) →
        ∀ t : ℕ, α * (f (k - 1) : ℝ) ≤ t → (t : ℝ) ≤ β * f (k - 1) →
        u * (N + v) < (u + v) *
          ((Finset.range N).filter fun s => ∃ j : Fin K, Nat.Prime (b s j * t + 1)).card →
        ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  classical
  have hE := Real.exp_pos 1
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have huvR : (u : ℝ) ≤ v := by exact_mod_cast huv
  have hmargin : 0 < Real.exp 1 * (u : ℝ) - v := sub_pos.mpr hve
  obtain ⟨J, hJ⟩ := exists_nat_gt
    (max 0 (((Real.exp 1 + 1) * K) / (Real.exp 1 * (u : ℝ) - v)))
  let D : ℝ := (J : ℝ) + K
  have hJp : (0 : ℝ) < J := (le_max_left _ _).trans_lt hJ
  have hD : 0 < D := add_pos_of_pos_of_nonneg hJp (Nat.cast_nonneg _)
  have hgap : (Real.exp 1 + 1) * (K : ℝ) < D * (Real.exp 1 * (u : ℝ) - v) := by
    have h := (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hJ)
    exact h.trans_le (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Nat.cast_nonneg K)) hmargin.le)
  let lo := D * u - K
  let hi := D * v + K
  have hlo : 0 < lo := by
    have h := mul_le_mul_of_nonneg_left huR hD.le
    dsimp [lo, D] at *
    linarith
  have hhi : lo ≤ hi := by
    have h := mul_le_mul_of_nonneg_left huvR hD.le
    dsimp [lo, hi]
    linarith [Nat.cast_nonneg (α := ℝ) K]
  have hratio : hi < Real.exp 1 * lo := by
    dsimp [lo, hi]
    nlinarith only [hgap]
  let z (i : ℕ) := i + J * (i / K)
  have hz : StrictMono z := by
    intro i j hij
    exact Nat.add_lt_add_of_lt_of_le hij
      (Nat.mul_le_mul_left J (Nat.div_le_div_right hij.le))
  have hzval (s j : ℕ) (hj : j < K) : z (s * K + j) = (J + K) * s + j := by
    have hdiv : (s * K + j) / K = s := by
      rw [Nat.mul_comm s K, Nat.mul_add_div hK, Nat.div_eq_of_lt hj, add_zero]
    dsimp [z]
    rw [hdiv]
    ring
  obtain ⟨a, L, U, hL, hLU, hU, hap, hpair⟩ :=
    Erdos287.compatible_slopes_realize_distance_band (N * K) z hz lo hi hlo hhi hratio
  let B := ∑ i ∈ range (N * K), a i
  let b (s j : ℕ) := a (s * K + j)
  have hflat (s j : ℕ) (hj : j < K) : s * K + j < (s + 1) * K := by
    rw [Nat.add_mul, one_mul]
    omega
  have hidx (s j : ℕ) (hs : s < N) (hj : j < K) : s * K + j < N * K :=
    (hflat s j hj).trans_le (Nat.mul_le_mul_right K (by omega))
  have horder (s r i j : ℕ) (hsr : s < r) (hi : i < K) : s * K + i < r * K + j :=
    (hflat s i hi).trans_le ((Nat.mul_le_mul_right K (by omega)).trans (Nat.le_add_right _ _))
  have hb (s j : ℕ) (hs : s < N) (hj : j < K) :
      0 < b s j ∧ b s j ≤ B := by
    have h := hidx s j hs hj
    exact ⟨hap _ h, single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (mem_range.mpr h)⟩
  have hwin (s r i j : ℕ) (hs : s < N) (hr : r < N) (hiK : i < K) (hjK : j < K)
      (hl : u ≤ r - s) (hh : r - s ≤ v) :
      b s i < b r j ∧ (b r j - b s i) ∣ b s i ∧
        L ≤ ((b s i / (b r j - b s i) : ℕ) : ℝ) * b r j ∧
        ((b s i / (b r j - b s i) : ℕ) : ℝ) * b r j ≤ U := by
    have hsr : s < r := by omega
    obtain ⟨hlt, hdvd, hband⟩ :=
      hpair _ _ (horder s r i j hsr hiK) (hidx r j hr hjK)
    have heq : (z (r * K + j) : ℝ) - z (s * K + i) =
        D * ((r - s : ℕ) : ℝ) + (j : ℝ) - i := by
      rw [hzval r j hjK, hzval s i hiK, Nat.cast_sub hsr.le]
      push_cast
      dsimp [D]
      ring
    refine ⟨hlt, hdvd, hband ?_ ?_⟩
    · rw [heq]
      have h := mul_le_mul_of_nonneg_left (show (u : ℝ) ≤ (r - s : ℕ) by exact_mod_cast hl) hD.le
      have hik : (i : ℝ) ≤ K := by exact_mod_cast hiK.le
      dsimp [lo]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    · rw [heq]
      have h := mul_le_mul_of_nonneg_left (show ((r - s : ℕ) : ℝ) ≤ v by exact_mod_cast hh) hD.le
      have hjk : (j : ℝ) ≤ K := by exact_mod_cast hjK.le
      dsimp [hi]
      linarith [Nat.cast_nonneg (α := ℝ) i]
  obtain ⟨α, β, hα, hβ, M₀, htransfer⟩ :=
    Erdos287.gap_from_uniform_prime_window B L U hL hLU hU
  refine ⟨b, α, β, M₀, hα, hβ, (fun s hs j hj => (hb s j hs hj).1), ?_, ?_⟩
  · intro s r i j hs hr hiK hjK heq
    change a (s * K + i) = a (r * K + j) at heq
    have hidx_eq : s * K + i = r * K + j := by
      rcases lt_trichotomy (s * K + i) (r * K + j) with hl | he | hl
      · exact ((hpair _ _ hl (hidx r j hr hjK)).1.ne heq).elim
      · exact he
      · exact ((hpair _ _ hl (hidx s i hs hiK)).1.ne heq.symm).elim
    have hsr : s = r := by
      rcases lt_trichotomy s r with hl | he | hl
      · exact ((horder s r i j hl hiK).ne hidx_eq).elim
      · exact he
      · exact ((horder r s j i hl hjK).ne hidx_eq.symm).elim
    exact ⟨hsr, by rw [hsr] at hidx_eq; omega⟩
  · intro k f hk hf hmono hsum hM t htlo hthi hdensity
    let S := (range N).filter fun s => ∃ j : Fin K, Nat.Prime (b s j * t + 1)
    have hS (s : ℕ) (hs : s ∈ S) : s < N ∧ ∃ j : Fin K, Nat.Prime (b s j * t + 1) :=
      ⟨mem_range.mp (mem_filter.mp hs).1, (mem_filter.mp hs).2⟩
    let select (s : ℕ) := if hs : s ∈ S then (hS s hs).2.choose.val else 0
    have hselect (s : ℕ) (hs : s ∈ S) :
        select s < K ∧ Nat.Prime (b s (select s) * t + 1) := by
      simp only [select, dif_pos hs]
      exact ⟨(hS s hs).2.choose.isLt, (hS s hs).2.choose_spec⟩
    refine htransfer k f hk hf hmono hsum hM N u v t S (fun s => b s (select s))
      hu hv (fun s hs => (hS s hs).1) hdensity htlo hthi ?_ ?_
    · intro s hs
      obtain ⟨hpos, hbd⟩ := hb s (select s) (hS s hs).1 (hselect s hs).1
      exact ⟨hpos, hbd, (hselect s hs).2⟩
    · intro s hs r hr hl hh
      exact hwin s r (select s) (select r) (hS s hs).1 (hS r hr).1
        (hselect s hs).1 (hselect r hr).1 hl hh

