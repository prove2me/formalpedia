-- Prove2me | solution 1 for Erdos266.summable_blockAnchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:51:10.13688+00:00
-- url     : https://prove2.me/submissions/1e7804bb-b2b4-4b0c-9454-154b814bd7ac

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_blockAnchor_nonneg
public import Theorems.Thm_Erdos266_blockAnchor_le
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_succ_le_two_pow


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i : ℕ} (hi : 1 ≤ i) :
    Summable (fun l => blockAnchor i l) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = 2 * i + 2 := ⟨_, rfl⟩
  refine (summable_nat_add_iff L).mp ?_
  have hgeom : Summable (fun l : ℕ => 2 * ((l + L : ℝ) * (1 / 2) ^ (l + L))) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖(1/2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; rw [abs_of_pos] <;> norm_num)
    have h2 := ((summable_nat_add_iff L).mpr h).mul_left 2
    refine h2.congr fun l => ?_
    push_cast
    rw [pow_one]
  have hLpow : ∀ l : ℕ, (2:ℕ) ^ (l + L) ≤ bigN (l + L) := by
    intro l
    rw [bigN]
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.le_self_pow (by norm_num) _)
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hgeom
  · apply blockAnchor_nonneg
    have h1 : 2 * i ≤ 2 ^ (l + L) := by
      have h2 := succ_le_two_pow (l + L)
      omega
    exact_mod_cast le_trans h1 (hLpow l)
  · have hpowR : ((2:ℝ)) ^ (l + L) ≤ (bigN (l + L) : ℝ) := by
      calc ((2:ℝ)) ^ (l + L) = ((2 ^ (l + L) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (bigN (l + L) : ℝ) := by exact_mod_cast hLpow l
    have hNpos : (0:ℝ) < (bigN (l + L) : ℝ) := by exact_mod_cast bigN_pos (l + L)
    have h2N : (2 : ℝ) ≤ (bigN (l + L) : ℝ) := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (l + L) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
      _ ≤ (bigN (l + L) : ℝ) := hpowR
    have h2i : (2 * i : ℝ) ≤ (bigN (l + L) : ℝ) := by
      have h1 : (2 * i : ℕ) ≤ 2 ^ (l + L) := by
        have h2 := succ_le_two_pow (l + L)
        omega
      calc (2 * i : ℝ) = ((2 * i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (l + L) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ (bigN (l + L) : ℝ) := by exact_mod_cast hLpow l
    calc blockAnchor i (l + L) ≤ ((l + L : ℕ) : ℝ) * (2 / (bigN (l + L) : ℝ)) :=
          blockAnchor_le h2i hi h2N
    _ ≤ ((l + L : ℕ) : ℝ) * (2 / (2:ℝ) ^ (l + L)) := by
          apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hpowR
    _ = 2 * ((l + L : ℝ) * (1 / 2) ^ (l + L)) := by
          push_cast
          rw [div_pow, one_pow]
          field_simp
end Erdos266
