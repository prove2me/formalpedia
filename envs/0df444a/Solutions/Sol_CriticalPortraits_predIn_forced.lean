-- Prove2me | solution 1 for CriticalPortraits.predIn_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:37:33.581921+00:00
-- url     : https://prove2.me/submissions/0ec3a038-58bd-4b22-b14d-a83db02eace4

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_CriticalPortraits_level_lt_of_val_lt
public import Theorems.Thm_CriticalPortraits_spanning_edge

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {x : ZMod (d * m)} (hx₁ : x ∈ T P₁) (hx₂ : x ∈ T P₂) :
    predIn P₁ x hx₁ = predIn P₂ x hx₂ := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  subst hn
  -- IH: equality for strictly-lower survivors.
  have IH : ∀ y : ZMod (d*m), y.val < x.val → ∀ (hy₁ : y ∈ T P₁) (hy₂ : y ∈ T P₂),
      predIn P₁ y hy₁ = predIn P₂ y hy₂ := by
    intro y hyv hy₁ hy₂
    exact ih y.val hyv hy₁ hy₂ rfl
  -- one-directional WLOG, generic in the ordered pair of portraits.
  have noLt : ∀ (Q₁ Q₂ : Finset (Finset (ZMod (d*m)))), Portrait d m Q₁ → Portrait d m Q₂ →
      T Q₁ = T Q₂ → (∀ y : ZMod (d*m), y.val < x.val → ∀ (hy₁ : y ∈ T Q₁) (hy₂ : y ∈ T Q₂),
        predIn Q₁ y hy₁ = predIn Q₂ y hy₂) →
      ∀ (hq₁ : x ∈ T Q₁) (hq₂ : x ∈ T Q₂),
        ¬ ((predIn Q₁ x hq₁).val < (predIn Q₂ x hq₂).val) := by
    intro Q₁ Q₂ hQ₁ hQ₂ hTQ IHQ hq₁ hq₂ hlt
    set w₁ := predIn Q₁ x hq₁ with hw₁
    set w₂ := predIn Q₂ x hq₂ with hw₂
    have hfib₁ : w₁.val % m = x.val % m := predIn_sameFiber hQ₁ hq₁
    have hfib₂ : w₂.val % m = x.val % m := predIn_sameFiber hQ₂ hq₂
    have hfib12 : w₁.val % m = w₂.val % m := by rw [hfib₁, hfib₂]
    have hw1lt : w₁.val < x.val := predIn_val_lt hq₁
    have hw2lt : w₂.val < x.val := predIn_val_lt hq₂
    have hcolw₂x : colV w₂ = colV x := by unfold colV; rw [hfib₂]
    -- levels
    have hlevel_w1 : loV Q₁ x = w₁.val / m := loV_eq hq₁
    have hlevel_w2 : loV Q₂ x = w₂.val / m := loV_eq hq₂
    set ℓ := w₂.val / m with hℓdef
    have hℓ_eq_lo2 : loV Q₂ x = ℓ := by rw [hlevel_w2]
    have hlt_lev_12 : w₁.val / m < ℓ := level_lt_of_val_lt hfib12 hlt
    have hℓ_gt_lo1 : loV Q₁ x < ℓ := by rw [hlevel_w1]; exact hlt_lev_12
    have hℓ_lt_hi : ℓ < hiV x := by
      have := level_lt_of_val_lt hfib₂ hw2lt
      simpa [hℓdef, hiV] using this
    have hw2val : w₂.val = colV x + ℓ * m := by
      have h := top_val_eq (x := w₂)
      rw [hcolw₂x] at h
      have hhi : hiV w₂ = ℓ := rfl
      rw [hhi] at h; exact h
    -- The spanning edge over v₀ = colV x + ℓ*m, in Q₁.
    obtain ⟨b, hb₁, hbcol, hbpred, hbgt, hblt⟩ :=
      spanning_edge hd hm hQ₁ hq₁ hℓ_gt_lo1 hℓ_lt_hi
    -- transfer b's edge to Q₂ via IH.
    have hb₂ : b ∈ T Q₂ := hTQ ▸ hb₁
    have hbforce : predIn Q₁ b hb₁ = predIn Q₂ b hb₂ := IHQ b hblt hb₁ hb₂
    -- the crossing in Q₂: predIn b < w₂ < b < x.
    have o1 : (predIn Q₂ b hb₂).val < w₂.val := by
      rw [← hbforce, hw2val]; exact hbpred
    have o2 : w₂.val < b.val := by rw [hw2val]; exact hbgt
    have o3 : b.val < x.val := hblt
    exact no_alt hQ₂ hb₂ hq₂ o1 o2 o3
  have h12 := noLt P₁ P₂ h₁ h₂ hT IH hx₁ hx₂
  have h21 := noLt P₂ P₁ h₂ h₁ hT.symm (fun y hyv hy₂ hy₁ => (IH y hyv hy₁ hy₂).symm) hx₂ hx₁
  exact ZMod.val_injective _ (le_antisymm (not_lt.mp h21) (not_lt.mp h12))
end CriticalPortraits
