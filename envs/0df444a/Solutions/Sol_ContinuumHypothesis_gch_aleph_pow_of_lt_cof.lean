-- Prove2me | solution 1 for ContinuumHypothesis.gch_aleph_pow_of_lt_cof
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:21:14.202643+00:00
-- url     : https://prove2.me/submissions/7ec6bed6-620a-416c-ae9d-c7a471fe3a62

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


open Cardinal Ordinal Order

namespace CHB
open ContinuumHypothesis CHA

theorem pow_le_succ (h : GCH.{u}) (α β : Ordinal.{u}) (hαβ : α ≤ β + 1) :
    ℵ_ α ^ ℵ_ β = ℵ_ (β + 1) := by
  have e : ℵ_ (β + 1) = 2 ^ ℵ_ β := by rw [gch_two_pow h _ (aleph0_le_aleph β), succ_aleph]
  rw [e]
  apply le_antisymm
  · calc ℵ_ α ^ ℵ_ β ≤ (2 ^ ℵ_ β) ^ ℵ_ β := by
          apply power_le_power_right; rw [← e]; exact aleph_le_aleph.mpr hαβ
      _ = 2 ^ ℵ_ β := by rw [← power_mul, mul_eq_self (aleph0_le_aleph β)]
  · apply power_le_power_right
    have h2 : (2 : Cardinal.{u}) ≤ ℵ₀ := by exact_mod_cast (natCast_lt_aleph0 (n := 2)).le
    exact le_trans h2 (aleph0_le_aleph α)

theorem pow_cof_le (h : GCH.{u}) (α β : Ordinal.{u}) (hβα : β + 1 < α)
    (hcof : (ℵ_ α).ord.cof ≤ ℵ_ β) : ℵ_ α ^ ℵ_ β = ℵ_ (α + 1) := by
  have hβα' : β < α := lt_of_le_of_lt le_self_add hβα
  apply le_antisymm
  · have e : ℵ_ (α + 1) = 2 ^ ℵ_ α := by rw [gch_two_pow h _ (aleph0_le_aleph α), succ_aleph]
    rw [e]
    calc ℵ_ α ^ ℵ_ β ≤ (2 ^ ℵ_ α) ^ ℵ_ β := power_le_power_right (cantor _).le
      _ = 2 ^ ℵ_ α := by
          rw [← power_mul, mul_eq_left (aleph0_le_aleph α) (aleph_le_aleph.mpr hβα'.le)
            (aleph_pos β).ne']
  · rw [← succ_aleph]
    apply succ_le_of_lt
    calc ℵ_ α < ℵ_ α ^ (ℵ_ α).ord.cof := lt_power_cof_ord (aleph0_le_aleph α)
      _ ≤ ℵ_ α ^ ℵ_ β := power_le_power_left (aleph_pos α).ne' hcof

theorem pow_lt_cof (h : GCH.{u}) (α β : Ordinal.{u}) (hβα : β + 1 < α)
    (hcof : ℵ_ β < (ℵ_ α).ord.cof) : ℵ_ α ^ ℵ_ β = ℵ_ α := by
  have hβα' : β < α := lt_of_le_of_lt le_self_add hβα
  apply le_antisymm _ (self_le_power _ (one_lt_aleph0.le.trans (aleph0_le_aleph β)))
  set κ := ℵ_ α with hκ
  set lam := ℵ_ β with hlam
  have hκ0 : ℵ₀ < κ := by
    rw [hκ, ← aleph_zero, aleph_lt_aleph]; exact lt_of_le_of_lt zero_le hβα'
  have hlk : lam < κ := aleph_lt_aleph.mpr hβα'
  let T := κ.ord.ToType
  have hT : #T = κ := by simp [T]
  have hTo : ord #T = typeLT T := by rw [hT, type_toType]
  let X := lam.out
  have hX : #X = lam := mk_out lam
  have hbound : ∀ f : X → T, ∃ y : T, ∀ x, f x ≤ y := by
    intro f
    by_contra hne
    push Not at hne
    have hcf : IsCofinal (Set.range f) := by
      intro a
      obtain ⟨x, hx⟩ := hne a
      exact ⟨f x, ⟨x, rfl⟩, hx.le⟩
    have h1 := Order.cof_le hcf
    have h2 : Order.cof T = κ.ord.cof := by rw [← Ordinal.cof_type, type_toType]
    rw [h2] at h1
    have h3 := mk_range_le (f := f)
    rw [hX] at h3
    exact absurd (lt_of_le_of_lt (h1.trans h3) hcof) (lt_irrefl _)
  choose b hb using hbound
  let F : (X → T) → (Σ y : T, X → Set.Iic y) := fun f => ⟨b f, fun x => ⟨f x, hb f x⟩⟩
  have hF : Function.Injective F := by
    intro f g hfg
    have := congrArg (fun p : (Σ y : T, X → Set.Iic y) => fun x => ((p.2 x : Set.Iic p.1) : T)) hfg
    exact this
  have hterm : ∀ y : T, #(Set.Iic y) ^ #X ≤ κ := by
    intro y
    have hIio : #(Set.Iio y) < κ := lt_of_lt_of_eq (mk_Iio_lt y hTo) hT
    have hIic : #(Set.Iic y) < κ := by
      rw [← Set.Iio_insert]
      exact lt_of_le_of_lt (mk_insert_le) (add_lt_of_lt hκ0.le hIio (lt_of_lt_of_le one_lt_aleph0 hκ0.le))
    set μ := max (max #(Set.Iic y) lam) ℵ₀ with hμ
    have hμκ : μ < κ := max_lt (max_lt hIic hlk) hκ0
    have hμ0 : ℵ₀ ≤ μ := le_max_right _ _
    calc #(Set.Iic y) ^ #X ≤ μ ^ μ := by
          rw [hX]
          calc #(Set.Iic y) ^ lam ≤ μ ^ lam :=
                power_le_power_right (le_trans (le_max_left _ _) (le_max_left _ _))
            _ ≤ μ ^ μ := power_le_power_left (ne_of_gt (lt_of_lt_of_le aleph0_pos hμ0))
                (le_trans (le_max_right _ _) (le_max_left _ _))
      _ = 2 ^ μ := power_self_eq hμ0
      _ = succ μ := gch_two_pow h μ hμ0
      _ ≤ κ := succ_le_of_lt hμκ
  rw [← hT, ← hX, power_def]
  calc #(X → T) ≤ #(Σ y : T, X → Set.Iic y) := mk_le_of_injective hF
    _ = sum (fun y : T => #(Set.Iic y) ^ #X) := by rw [mk_sigma]; simp only [power_def]
    _ ≤ #T * ⨆ y : T, #(Set.Iic y) ^ #X := sum_le_mk_mul_iSup _
    _ ≤ #T * #T := by
        gcongr
        exact ciSup_le' fun y => by rw [hT]; exact hterm y
    _ = #T := mul_eq_self (by rw [hT]; exact hκ0.le)

end CHB

open ContinuumHypothesis in
theorem solution (h : GCH.{u}) (α β : Ordinal.{u}) (hβα : β + 1 < α)
    (hcof : ℵ_ β < (ℵ_ α).ord.cof) :
    ℵ_ α ^ ℵ_ β = ℵ_ α := CHB.pow_lt_cof h α β hβα hcof
