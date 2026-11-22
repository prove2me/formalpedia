-- Prove2me | solution 1 for CriticalPortraits.Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:35:04.326898+00:00
-- url     : https://prove2.me/submissions/231cbbce-2a69-4a05-aa78-dbcd517a88be

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Theorems.Thm_CriticalPortraits_Scount_antitone_left
public import Theorems.Thm_CriticalPortraits_Scount_split
public import Theorems.Thm_CriticalPortraits_GPRE
public import Theorems.Thm_CriticalPortraits_sep_master


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u s : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) (hs : s ∈ U)
    (hslo : (betaParent U u).val < s.val) (hshi : s.val < u.val) {ly : ℕ}
    (hwlo : (betaParent U u).val ≤ s.val % m + ly * m)
    (hwhi : s.val % m + ly * m < (betaParent U u).val + m) :
    Defc U (s.val % m) (s.val / m) s.val ly ≤ 0 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set φ := u.val % m with hφdef
  set ψ := s.val % m with hψdef
  set lu := u.val / m with hludef
  set ls := s.val / m with hlsdef
  set K := betaK U u with hKdef
  have hφlt : φ < m := Nat.mod_lt _ hm
  have hψlt : ψ < m := Nat.mod_lt _ hm
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  have hsval : ψ + ls * m = s.val := by rw [hψdef, hlsdef]; exact Nat.mod_add_div' s.val m
  have huval : φ + lu * m = u.val := by rw [hφdef, hludef]; exact Nat.mod_add_div' u.val m
  set yVal := ψ + ly * m with hyVal
  -- window: v ≤ yVal < v + m
  rw [hpval] at hwlo hwhi
  -- ly ∈ {K, K+1}
  have hlyK : K ≤ ly := by
    by_contra hc; push Not at hc
    have := sep_master (m := m) (p := ψ) (q := φ) hψlt hφlt hc
    omega
  have hlyK1 : ly ≤ K + 1 := by
    by_contra hc; push Not at hc
    have hlt : K + 1 < ly := by omega
    have hsm := sep_master (m := m) (p := φ) (q := ψ) hφlt hψlt hlt
    have he : (K + 1) * m = K * m + m := by ring
    omega
  -- choose w' = φ + j*m, j ∈ {ls, ls+1}
  set j := if φ < ψ then ls + 1 else ls with hjdef
  -- s.val ≤ w' < s.val + m
  have hsW : s.val ≤ φ + j * m := by
    rw [hjdef]; split
    · rename_i h
      have hsm := sep_master (m := m) (p := ψ) (q := φ) hψlt hφlt (show ls < ls + 1 by omega)
      omega
    · rename_i h
      push Not at h
      have hle : ψ + ls * m ≤ φ + ls * m := by omega
      omega
  have hWs : φ + j * m < s.val + m := by
    rw [hjdef]; split
    · rename_i h
      -- φ + (ls+1)*m < ψ + ls*m + m  ↔ φ < ψ
      have he : (ls + 1) * m = ls * m + m := by ring
      omega
    · rename_i h; push Not at h
      -- ¬(φ < ψ) ⟹ ψ ≤ φ; goal φ + ls*m < ψ + ls*m + m ↔ φ < ψ + m, from φ < m
      omega
  -- K < j ≤ lu
  have hKj : K < j := by
    by_contra hc; push Not at hc
    -- j ≤ K ⟹ φ + j*m ≤ φ + K*m = v < s.val ≤ w', contradiction
    have h1 : φ + j * m ≤ φ + K * m := by
      have := Nat.mul_le_mul_right m hc; omega
    omega
  have hjlu : j ≤ lu := by
    by_contra hc; push Not at hc
    have h1 : φ + (lu + 1) * m ≤ φ + j * m := by
      have := Nat.mul_le_mul_right m (show lu + 1 ≤ j by omega); omega
    have h2 : φ + (lu + 1) * m = u.val + m := by
      have : φ + (lu + 1) * m = (φ + lu * m) + m := by ring
      rw [this, huval]
    omega
  -- GPRE bound on Scount(v, w')
  have hgpre := GPRE hd hm hcanon hu hlu hKj hjlu
  rw [hpval] at hgpre
  -- Scount(yVal, s.val) ≤ Scount(v, s.val) (antitone in lower endpoint; yVal ≥ v)
  have hanti : Scount U yVal s.val ≤ Scount U (φ + K * m) s.val := by
    apply Scount_antitone_left; rw [hyVal]; omega
  -- the key Defc inequality, split on ψ = φ
  unfold Defc
  rw [← hyVal]
  by_cases hψφ : ψ = φ
  · -- ψ = φ ⟹ ly = K (window forces yVal = v) and j = ls
    -- (φ ≤ ψ false here? φ=ψ so φ≤ψ true ⟹ j=ls+1)
    -- recompute: with ψ=φ, w' = φ + (ls+1)*m but s.val = φ + ls*m, so s.val < w', use split anyway.
    -- yVal: from window with ψ=φ: φ + ly*m in [φ+K*m, φ+K*m+m) ⟹ ly = K
    have hlyEq : ly = K := by
      rcases (lt_or_eq_of_le hlyK1) with h | h
      · omega
      · -- ly = K+1: yVal = ψ+(K+1)*m ≥ φ+K*m+m, contradicts hwhi (ψ=φ)
        exfalso
        have he : (K + 1) * m = K * m + m := by ring
        rw [hyVal, h] at hwhi
        omega
    simp_all
  · -- ψ ≠ φ ⟹ s.val < w' strictly, use Scount_split for the -1, then case ly/j
    have hsltw : s.val < φ + j * m := by
      rcases lt_or_eq_of_le hsW with h | h
      · exact h
      · -- s.val = w' = φ+j*m ⟹ ψ + ls*m = φ + j*m, same fiber ⟹ ψ=φ via mod
        exfalso
        have : (ψ + ls * m) % m = (φ + j * m) % m := by rw [hsval, h]
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hψlt, Nat.mod_eq_of_lt hφlt] at this
        exact hψφ this
    have hsplit : Scount U (φ + K * m) (φ + j * m)
        = Scount U (φ + K * m) s.val + 1 + Scount U s.val (φ + j * m) := by
      apply Scount_split hs
      · rw [← hpval] at *; omega
      · exact hsltw
    have hsplitZ : (Scount U (φ + K * m) (φ + j * m) : ℤ)
        = (Scount U (φ + K * m) s.val : ℤ) + 1 + (Scount U s.val (φ + j * m) : ℤ) := by
      exact_mod_cast hsplit
    have hge0 : (0 : ℤ) ≤ (Scount U s.val (φ + j * m) : ℤ) := by exact_mod_cast Nat.zero_le _
    have hantiZ : (Scount U yVal s.val : ℤ) ≤ (Scount U (φ + K * m) s.val : ℤ) := by
      exact_mod_cast hanti
    -- pin j and ly
    have hjcase : j = ls ∨ j = ls + 1 := by rw [hjdef]; split <;> [right; left] <;> rfl
    -- We need: Scount(yVal, s.val) - (ls - ly - 1) ≤ 0, i.e. Scount(yVal,s.val) ≤ ls - ly - 1.
    -- have: Scount(yVal,s) ≤ Scount(v,s); Scount(v,s)+1 ≤ Scount(v,w') ≤ j-K-1.
    -- ⟹ Scount(yVal,s) ≤ j - K - 2. Need j+ly ≤ ls+K+1.
    have hbound : (Scount U yVal s.val : ℤ) ≤ (j : ℤ) - K - 2 := by linarith
    have hjly : (j : ℤ) + ly ≤ ls + K + 1 := by
      -- enumerate ly∈{K,K+1}, j∈{ls,ls+1}; exclude (ly=K+1 ∧ j=ls+1)
      rcases (lt_or_eq_of_le hlyK1) with hlylt | hlyeq
      · -- ly = K
        have : ly = K := by omega
        subst this
        rcases hjcase with hj | hj <;> rw [hj] <;> push_cast <;> omega
      · -- ly = K+1 ⟹ ψ < φ (from hwhi)
        -- hwhi : ψ + ly*m < φ + K*m + m, with ly = K+1
        have hψφlt : ψ < φ := by
          rw [hyVal, hlyeq] at hwhi
          have he2 : (K + 1) * m = K * m + m := by ring
          omega
        -- then j = ls (else j=ls+1 ⟹ φ<ψ, contra)
        have hjeq : j = ls := by
          rw [hjdef]; rw [if_neg (by omega)]
        rw [hlyeq, hjeq]; push_cast; omega
    linarith
end CriticalPortraits
