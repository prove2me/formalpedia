-- Prove2me | solution 1 for ContinuumHypothesis.koenig_aleph0_lt_cof_two_pow_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:16:48.397562+00:00
-- url     : https://prove2.me/submissions/b6d1af60-5248-43c8-ad1d-205a050d4d89

import Mathlib
import Definitions.Def_CH_CardinalArithmetic

open Cardinal Ordinal Order
universe u

namespace CHA
open ContinuumHypothesis

theorem int_rat : #ℤ = #ℚ ∧ #ℤ < #ℝ := by
  refine ⟨by rw [mk_int, Cardinal.mkRat], ?_⟩
  rw [mk_int, mk_real]; exact aleph0_lt_continuum

theorem ch_iff : CH ↔ (2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1 := by
  have h1 : ℵ_ 1 = succ ℵ₀ := by
    rw [← aleph_zero, succ_aleph, zero_add]
  rw [h1]
  have hc : (2 : Cardinal.{0}) ^ ℵ₀ = #ℝ := by rw [mk_real, two_power_aleph0]
  constructor
  · intro hCH
    apply le_antisymm _ (succ_le_of_lt (by rw [two_power_aleph0]; exact aleph0_lt_continuum))
    by_contra hlt
    push Not at hlt
    obtain ⟨S, hS⟩ := (le_mk_iff_exists_set (c := succ ℵ₀) (α := ℝ)).mp (by rw [← hc]; exact hlt.le)
    exact hCH S ⟨by rw [hS]; exact lt_succ _, by rw [hS]; exact hlt⟩
  · intro h S ⟨h1, h2⟩
    rw [h] at h2
    exact absurd (le_of_lt_succ h2) (not_le.mpr h1)

theorem koenig_cof : ℵ₀ < ((2 : Cardinal.{0}) ^ ℵ₀).ord.cof :=
  lt_cof_ord_power le_rfl one_lt_two

theorem koenig_ne (α : Ordinal.{0}) (hα : α.cof = ℵ₀) : (2 : Cardinal.{0}) ^ ℵ₀ ≠ ℵ_ α := by
  intro h
  have hlim : IsSuccLimit α := Ordinal.one_lt_cof_iff.mp (by rw [hα]; exact one_lt_aleph0)
  have := koenig_cof
  rw [h, Cardinal.ord_aleph, cof_omega hlim, hα] at this
  exact lt_irrefl _ this

/-- under GCH, `2 ^ κ = succ κ` for infinite `κ` -/
lemma gch_two_pow (h : GCH.{u}) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) : (2 : Cardinal.{u}) ^ κ = succ κ := by
  apply le_antisymm _ (succ_le_of_lt (cantor κ))
  by_contra hlt
  push Not at hlt
  exact h κ hκ ⟨succ κ, lt_succ_of_not_isMax (not_isMax κ), hlt⟩

theorem gch_iff_succ : GCH.{u} ↔ ∀ α : Ordinal.{u}, (2 : Cardinal.{u}) ^ ℵ_ α = ℵ_ (α + 1) := by
  constructor
  · intro h α
    rw [gch_two_pow h _ (aleph0_le_aleph α), succ_aleph]
  · intro h κ hκ ⟨μ, h1, h2⟩
    obtain ⟨α, rfl⟩ := mem_range_aleph_iff.mpr hκ
    rw [h α, ← succ_aleph] at h2
    exact absurd (le_of_lt_succ h2) (not_le.mpr h1)

theorem gch_iff_beth : GCH.{u} ↔ ∀ α : Ordinal.{u}, ℵ_ α = ℶ_ α := by
  rw [gch_iff_succ]
  constructor
  · intro h α
    induction α using Ordinal.limitRecOn with
    | zero => rw [aleph_zero, beth_zero]
    | add_one o ih => rw [← Order.succ_eq_add_one, beth_succ, ← ih, h o, Order.succ_eq_add_one]
    | limit o ho ih =>
      rw [aleph_limit ho, beth_limit ho]
      congr 1; funext a; exact ih a a.2
  · intro h α
    rw [h, h, ← Order.succ_eq_add_one, beth_succ]

theorem gch_strictMono (h : GCH.{u}) (A B : Cardinal.{u}) (hA : ℵ₀ ≤ A) (hAB : A < B) :
    (2 : Cardinal.{u}) ^ A < 2 ^ B := by
  rw [gch_two_pow h A hA]
  exact lt_of_le_of_lt (succ_le_of_lt hAB) (cantor B)

end CHA

open ContinuumHypothesis in
theorem solution : ℵ₀ < ((2 : Cardinal.{0}) ^ ℵ₀).ord.cof := CHA.koenig_cof
