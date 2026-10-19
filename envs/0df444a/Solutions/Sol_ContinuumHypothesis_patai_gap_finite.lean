-- Prove2me | solution 1 for ContinuumHypothesis.patai_gap_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:25:07.973847+00:00
-- url     : https://prove2.me/submissions/158e1dd2-2c05-4d78-aae6-3a1081bccf1c

import Mathlib
import Definitions.Def_CH_CardinalArithmetic

open Cardinal Ordinal Order
universe u

namespace CHP

theorem patai (γ : Ordinal.{u})
    (h : ∀ α : Ordinal.{u}, (2 : Cardinal.{u}) ^ ℵ_ α = ℵ_ (α + γ)) : γ < ω := by
  by_contra hγ
  push Not at hγ
  have hγ0 : γ ≠ 0 := (omega0_pos.trans_le hγ).ne'
  set e := log ω γ with he
  set δ := ω ^ e with hδ
  have hδγ : δ ≤ γ := opow_log_le_self ω hγ0
  have he1 : 1 ≤ e := by
    have := log_mono_right ω hγ
    have h1 : log ω ω = 1 := by simpa using log_opow one_lt_omega0 1
    rwa [h1] at this
  have he0 : e ≠ 0 := (zero_lt_one.trans_le he1).ne'
  have hδω : ω ≤ δ := by
    calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
      _ ≤ ω ^ e := opow_le_opow_right omega0_pos he1
  have hδ0 : δ ≠ 0 := (omega0_pos.trans_le hδω).ne'
  have hγlt : γ < ω ^ succ e := lt_opow_succ_log_self one_lt_omega0 γ
  have hδlt : δ < ω ^ succ e := (opow_lt_opow_iff_right one_lt_omega0).mpr (lt_succ e)
  have habs : ∀ ν < δ, ν + γ = γ := fun ν hν => add_of_omega0_opow_le hν hδγ
  set c := δ + γ with hc
  have hconst : ∀ ν < δ, δ + ν + γ = c := fun ν hν => by rw [add_assoc, habs ν hν]
  have hcl : c < δ * ω := by
    rw [hδ, ← opow_succ]
    exact isPrincipal_add_omega0_opow (succ e) hδlt hγlt
  have hne : c < δ + c := by
    rcases (le_add_self : c ≤ δ + c).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hq : c / δ < ω := (div_lt hδ0).mpr hcl
      obtain ⟨n, hn⟩ := lt_omega0.mp hq
      have e1 : δ * (c / δ) + c % δ = c := div_add_mod c δ
      have e2 : (δ + c) / δ = 1 + c / δ := by
        conv_lhs => rw [← e1]
        rw [← add_assoc, show δ + δ * (c / δ) = δ * (1 + c / δ) by rw [mul_add, mul_one],
          mul_add_div _ hδ0, div_eq_zero_of_lt (mod_lt c hδ0), add_zero]
      rw [← h1, hn] at e2
      have : ((n : Ordinal) + 1 : Ordinal) = (1 : Ordinal) + n := by
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, add_comm]
      rw [← this] at e2
      exact absurd e2 (ne_of_lt (lt_add_one _))
  -- cardinal part
  let I := δ.ToType
  have hI : #I = δ.card := mk_toType δ
  let t : I → Ordinal.{u} := fun i => typein (α := I) (· < ·) i
  have ht : ∀ i, t i < δ := fun i => typein_lt_self i
  have hlimδ : IsSuccLimit δ := isSuccLimit_opow_left isSuccLimit_omega0 he0
  have hlim : IsSuccLimit (δ + δ) := isSuccLimit_add δ hlimδ
  have hsum : ℵ_ (δ + δ) ≤ sum (fun i : I => ℵ_ (δ + t i)) := by
    rw [aleph_limit hlim]
    apply ciSup_le'
    rintro ⟨a, ha⟩
    by_cases had : a < δ
    · let i0 : I := enum (α := I) (· < ·) ⟨0, by rw [type_toType]; exact pos_iff_ne_zero.mpr hδ0⟩
      have hi0 : t i0 = 0 := typein_enum _ _
      calc ℵ_ a ≤ ℵ_ (δ + t i0) := aleph_le_aleph.mpr (by rw [hi0, add_zero]; exact had.le)
        _ ≤ sum _ := le_sum _ i0
    · push Not at had
      have hν : a - δ < δ := by
        have h2 : δ + (a - δ) < δ + δ := by rw [Ordinal.add_sub_cancel_of_le had]; exact ha
        exact (add_lt_add_iff_left δ).mp h2
      let i : I := enum (α := I) (· < ·) ⟨a - δ, by rw [type_toType]; exact hν⟩
      have hi : t i = a - δ := typein_enum _ _
      calc ℵ_ a = ℵ_ (δ + t i) := by rw [hi, Ordinal.add_sub_cancel_of_le had]
        _ ≤ sum _ := le_sum _ i
  have key : (2 : Cardinal.{u}) ^ ℵ_ (δ + δ) ≤ ℵ_ c := by
    calc (2 : Cardinal.{u}) ^ ℵ_ (δ + δ) ≤ 2 ^ sum (fun i : I => ℵ_ (δ + t i)) :=
          power_le_power_left two_ne_zero hsum
      _ = prod (fun i : I => (2 : Cardinal.{u}) ^ ℵ_ (δ + t i)) := power_sum _ _
      _ = prod (fun _ : I => ℵ_ c) := by
          congr 1; funext i; rw [h, hconst _ (ht i)]
      _ = ℵ_ c ^ #I := prod_const' _ _
      _ ≤ ℵ_ c ^ ℵ_ δ := power_le_power_left (aleph_pos c).ne' (by rw [hI]; exact card_le_aleph δ)
      _ = (2 ^ ℵ_ δ) ^ ℵ_ δ := by rw [h δ]
      _ = 2 ^ ℵ_ δ := by rw [← power_mul, mul_eq_self (aleph0_le_aleph δ)]
      _ = ℵ_ c := h δ
  rw [h, add_assoc] at key
  exact absurd (aleph_le_aleph.mp key) (not_le.mpr hne)

end CHP

open ContinuumHypothesis in
theorem solution (γ : Ordinal.{u})
    (h : ∀ α : Ordinal.{u}, (2 : Cardinal.{u}) ^ ℵ_ α = ℵ_ (α + γ)) :
    γ < Ordinal.omega0 := CHP.patai γ h
