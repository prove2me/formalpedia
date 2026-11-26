-- Prove2me | solution 1 for Erdos266.growth_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:44:18.211381+00:00
-- url     : https://prove2.me/submissions/dfa0e80d-1fa3-4b18-b877-934f99c27dc1

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_bigN_succ
public import Theorems.Thm_Erdos266_bigM_sq_le
public import Theorems.Thm_Erdos266_succ_le_two_pow
public import Theorems.Thm_Erdos266_one_le_bigM
public import Theorems.Thm_Erdos266_quad_dom

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (d : ℕ) (Dc εc : ℝ) (hD : 0 < Dc) (hε : 0 < εc) :
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k, K₀ ≤ k → ∀ i : ℕ, i < d →
      Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ εc * (bigM (k + 1) : ℝ) / (bigN (k + 1) : ℝ) ^ (i + 2) := by
  -- a power of two absorbing the ratio of the constants
  obtain ⟨r₀, hr₀⟩ := pow_unbounded_of_one_lt (2 * Dc / εc) (by norm_num : (1:ℝ) < 2)
  set K₀ : ℕ := (2 * (d + 1) + 2 * r₀ + (d + 1) + r₀ + 3) + (4 * (d + 1) + 2 * (d + 1) + 1) + 4
    with hK₀def
  refine ⟨K₀, by omega, ?_⟩
  intro k hk i hi
  have hNpos : (0:ℝ) < (bigN k : ℝ) := by exact_mod_cast bigN_pos k
  have hNpos' : (0:ℝ) < (bigN (k+1) : ℝ) := by exact_mod_cast bigN_pos (k+1)
  have hMpos' : (1:ℝ) ≤ (bigM (k+1) : ℝ) := by
    exact_mod_cast one_le_bigM (show 2 ≤ k + 1 by omega)
  -- Step 1: the error is at most `2Dc/N_k^(i+2)` because `M_k² ≤ N_k`
  have hstep1 : Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
      ≤ 2 * Dc / (bigN k : ℝ) ^ (i + 2) := by
    have hM2 : (bigM k : ℝ) ^ 2 ≤ (bigN k : ℝ) := by
      have := bigM_sq_le k
      have h := this
      rw [pow_two]
      exact_mod_cast h
    have h2 : (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3) ≤ 1 / (bigN k : ℝ) ^ (i + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (bigM k : ℝ) ^ 2 * (bigN k : ℝ) ^ (i + 2)
          ≤ (bigN k : ℝ) * (bigN k : ℝ) ^ (i + 2) :=
            mul_le_mul_of_nonneg_right hM2 (by positivity)
      _ = (bigN k : ℝ) ^ (i + 3) := by
            rw [← pow_succ']
    have h3 : Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ Dc * (1 / (bigN k : ℝ) ^ (i + 2) + 1 / (bigN k : ℝ) ^ (i + 2)) := by
      refine mul_le_mul_of_nonneg_left (by linarith) hD.le
    calc Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ Dc * (1 / (bigN k : ℝ) ^ (i + 2) + 1 / (bigN k : ℝ) ^ (i + 2)) := h3
    _ = 2 * Dc / (bigN k : ℝ) ^ (i + 2) := by ring
  refine hstep1.trans ?_
  -- Step 2: reduce to an inequality about `M (k+1)` and powers of two
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `2Dc · N_(k+1)^(i+2) ≤ εc · M_(k+1) · N_k^(i+2)`
  have hNratio : (bigN (k+1) : ℝ) ^ (i + 2)
      = (2:ℝ) ^ ((2 * k + 1) * (i + 2)) * (bigN k : ℝ) ^ (i + 2) := by
    rw [show bigN (k+1) = 2 ^ (2 * k + 1) * bigN k from bigN_succ k]
    push_cast
    rw [mul_pow, ← pow_mul]
  rw [hNratio]
  -- key: `2Dc · 2^((2k+1)(i+2)) ≤ εc · M_(k+1)`
  have hkey : 2 * Dc * (2:ℝ) ^ ((2 * k + 1) * (i + 2)) ≤ εc * (bigM (k+1) : ℝ) := by
    set E : ℕ := (2 * k + 1) * (d + 1) + r₀ with hEdef
    -- `M (k+1) ≥ 2^E` for `k ≥ K₀`
    have hMlow : (2:ℕ) ^ E ≤ bigM (k + 1) := by
      rw [bigM, le_min_iff]
      have hsq : (k + 2) * (k + 2) ≤ (k + 1) ^ 2 * 2 := by nlinarith
      constructor
      · -- division branch: `2^E · 4(k+1) ≤ N (k+1)`
        rw [Nat.le_div_iff_mul_le (by omega)]
        have h4k : 4 * (k + 1) ≤ 2 ^ (k + 3) := by
          have := succ_le_two_pow k
          calc 4 * (k + 1) ≤ 4 * 2 ^ k := by omega
          _ = 2 ^ (k + 2) := by ring
          _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 2 ^ E * (4 * (k + 1)) ≤ 2 ^ E * 2 ^ (k + 3) :=
              Nat.mul_le_mul_left _ h4k
        _ = 2 ^ (E + (k + 3)) := by rw [← pow_add]
        _ ≤ 2 ^ ((k + 1) ^ 2) := by
              apply Nat.pow_le_pow_right (by norm_num)
              have := quad_dom ((d + 1) + r₀ + 3 + 2 * (d + 1))
                (2 * (d + 1) + 1) k (by omega)
              nlinarith
        _ = bigN (k + 1) := rfl
      · -- square-root branch: `(2^E)² ≤ N (k+1)`
        rw [Nat.le_sqrt]
        calc 2 ^ E * 2 ^ E = 2 ^ (E + E) := by rw [← pow_add]
        _ ≤ 2 ^ ((k + 1) ^ 2) := by
              apply Nat.pow_le_pow_right (by norm_num)
              have := quad_dom (2 * ((d + 1) + r₀))
                (2 * (2 * (d + 1))) k (by omega)
              nlinarith
        _ = bigN (k + 1) := rfl
    have hMlowR : (2:ℝ) ^ E ≤ (bigM (k+1) : ℝ) := by
      have : ((2:ℕ) ^ E : ℝ) ≤ (bigM (k+1) : ℝ) := by exact_mod_cast hMlow
      push_cast at this
      exact this
    -- `2Dc ≤ εc·2^(r₀)` and `(2k+1)(i+2) + r₀ ≤ E`... assemble
    have hexp : (2 * k + 1) * (i + 2) + r₀ ≤ E := by
      rw [hEdef]
      have : (2 * k + 1) * (i + 2) ≤ (2 * k + 1) * (d + 1) := by
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    have hpow_split : (2:ℝ) ^ E
        = (2:ℝ) ^ ((2 * k + 1) * (i + 2)) * 2 ^ (E - (2 * k + 1) * (i + 2)) := by
      rw [← pow_add]
      congr 1
      omega
    have hr₀' : 2 * Dc ≤ εc * 2 ^ r₀ := by
      rw [div_lt_iff₀ hε] at hr₀
      -- hr₀ : 2 * Dc / εc < 2 ^ r₀ — after rw: 2 * Dc < 2 ^ r₀ * εc
      linarith
    have hr₀E : (2:ℝ) ^ r₀ ≤ 2 ^ (E - (2 * k + 1) * (i + 2)) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    calc 2 * Dc * (2:ℝ) ^ ((2 * k + 1) * (i + 2))
        ≤ (εc * 2 ^ r₀) * (2:ℝ) ^ ((2 * k + 1) * (i + 2)) :=
          mul_le_mul_of_nonneg_right hr₀' (by positivity)
    _ ≤ (εc * 2 ^ (E - (2 * k + 1) * (i + 2))) * (2:ℝ) ^ ((2 * k + 1) * (i + 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hr₀E hε.le
    _ = εc * (2:ℝ) ^ E := by
          rw [hpow_split]
          ring
    _ ≤ εc * (bigM (k+1) : ℝ) := mul_le_mul_of_nonneg_left hMlowR hε.le
  calc 2 * Dc * ((2:ℝ) ^ ((2 * k + 1) * (i + 2)) * (bigN k : ℝ) ^ (i + 2))
      = (2 * Dc * (2:ℝ) ^ ((2 * k + 1) * (i + 2))) * (bigN k : ℝ) ^ (i + 2) := by ring
  _ ≤ (εc * (bigM (k+1) : ℝ)) * (bigN k : ℝ) ^ (i + 2) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)
  _ = εc * (bigM (k+1) : ℝ) * (bigN k : ℝ) ^ (i + 2) := by ring
end Erdos266
