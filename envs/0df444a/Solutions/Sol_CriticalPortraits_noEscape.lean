-- Prove2me | solution 1 for CriticalPortraits.noEscape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:35:50.706432+00:00
-- url     : https://prove2.me/submissions/4eab7163-9787-4861-8a45-449a2c83cebe

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
public import Theorems.Thm_CriticalPortraits_discrete_ivt
public import Theorems.Thm_CriticalPortraits_Defc_step
public import Theorems.Thm_CriticalPortraits_Defc_top_nonneg
public import Theorems.Thm_CriticalPortraits_betaK_ge
public import Theorems.Thm_CriticalPortraits_N0
public import Theorems.Thm_CriticalPortraits_Q

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
    {u s : ZMod (d * m)} (hu : u ∈ U) (hs : s ∈ U)
    (hslo : (betaParent U u).val < s.val) (hshi : s.val < u.val) :
    (betaParent U u).val ≤ (betaParent U s).val := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  have hlu : 1 ≤ u.val / m := survivor_level_pos hd hcanon hu
  have hls : 1 ≤ s.val / m := survivor_level_pos hd hcanon hs
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
  -- ly and window
  set ly := if ψ < φ then K + 1 else K with hlydef
  have hwlo : (betaParent U u).val ≤ ψ + ly * m := by
    rw [hpval, hlydef]; split
    · rename_i h
      have he : (K + 1) * m = K * m + m := by ring
      omega
    · rename_i h; push Not at h; omega
  have hwhi : ψ + ly * m < (betaParent U u).val + m := by
    rw [hpval, hlydef]; split
    · rename_i h
      have he : (K + 1) * m = K * m + m := by ring
      omega
    · rename_i h; push Not at h; omega
  -- Q gives the start bound; build the shifted IVT
  have hQ := Q hd hm hcanon hu hlu hs hslo hshi (ly := ly) hwlo hwhi
  -- N0: s.val ≥ v + m, so ly < ls
  have hsge : (betaParent U u).val + m ≤ s.val := by
    by_contra hc; push Not at hc
    exact N0 hd hm hcanon hu hlu hs hslo hc
  have hwhi' : ψ + ly * m < φ + K * m + m := by rw [← hpval]; exact hwhi
  have hlyls : ly < ls := by
    -- yVal = ψ+ly*m < v+m ≤ s.val = ψ+ls*m ⟹ ly < ls
    have h1 : ψ + ly * m < ψ + ls * m := by
      rw [hsval]; rw [hpval] at hsge; omega
    by_contra hc; push Not at hc
    have : ψ + ls * m ≤ ψ + ly * m := by
      have := Nat.mul_le_mul_right m hc; omega
    omega
  -- E i := Defc U ψ ls s.val (ly + i), L = (ls - 1) - ly
  set L := (ls - 1) - ly with hLdef
  set E : ℕ → ℤ := fun i => Defc U ψ ls s.val (ly + i) with hEdef
  have hE0 : E 0 ≤ 0 := by
    simp_all
  have hEL : 0 ≤ E L := by
    have hjL : ly + L = ls - 1 := by omega
    simp only [hEdef]
    rw [hjL]
    rw [hlsdef] at *
    exact Defc_top_nonneg U ψ (s.val / m) s.val hls
  have hEstep : ∀ i, i < L → E (i + 1) ≤ E i + 1 := by
    intro i _
    simp only [hEdef]
    have : ly + (i + 1) = (ly + i) + 1 := by omega
    rw [this]
    rw [hlsdef] at *
    exact Defc_step hm U ψ (s.val / m) s.val (ly + i)
  obtain ⟨i, hiL, hEi⟩ := discrete_ivt E L hE0 hEL hEstep
  have hzero : Defc U ψ ls s.val (ly + i) = 0 := by simpa [hEdef] using hEi
  -- betaK s ≥ ly + i ≥ ly
  have hkle : ly + i ≤ s.val / m - 1 := by rw [← hlsdef]; omega
  have hge : ly + i ≤ betaK U s := by
    apply betaK_ge (k := ly + i)
    · rw [hψdef, hlsdef] at hzero; exact hzero
    · exact hkle
  have hbetaKge : ly ≤ betaK U s := by omega
  -- (betaParent U s).val = ψ + betaK s * m ≥ ψ + ly*m ≥ v
  have hspval : (betaParent U s).val = ψ + betaK U s * m := by
    rw [betaParent_val hd hm hls]; rw [hψdef]; rfl
  rw [hspval, hpval]
  -- goal: φ + K*m ≤ ψ + betaK s * m; from φ+K*m ≤ ψ+ly*m (hwlo) and ly ≤ betaK s
  have hmm : ψ + ly * m ≤ ψ + betaK U s * m := by
    have := Nat.mul_le_mul_right m hbetaKge; omega
  rw [hpval] at hwlo
  omega
end CriticalPortraits
