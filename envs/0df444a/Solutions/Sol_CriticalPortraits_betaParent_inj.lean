-- Prove2me | solution 1 for CriticalPortraits.betaParent_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:27.000935+00:00
-- url     : https://prove2.me/submissions/352c4aa3-4cb1-4967-8161-659162d4b2ca

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
public import Theorems.Thm_CriticalPortraits_betaK_max
public import Theorems.Thm_CriticalPortraits_betaParent_fiber
public import Theorems.Thm_CriticalPortraits_Scount_split
public import Theorems.Thm_CriticalPortraits_betaParent_balance
public import Theorems.Thm_CriticalPortraits_level_injOn_fiber
public import Theorems.Thm_CriticalPortraits_val_le_iff_level_le_of_sameFiber


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
    {u1 u2 : ZMod (d * m)} (hu1 : u1 ∈ U) (hu2 : u2 ∈ U)
    (heq : betaParent U u1 = betaParent U u2) : u1 = u2 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  have hlu1 : 1 ≤ u1.val / m := survivor_level_pos hd hcanon hu1
  have hlu2 : 1 ≤ u2.val / m := survivor_level_pos hd hcanon hu2
  -- same fiber
  have hfib : u1.val % m = u2.val % m := by
    have h1 : (betaParent U u1).val % m = u1.val % m := betaParent_fiber hd hm hlu1
    have h2 : (betaParent U u2).val % m = u2.val % m := betaParent_fiber hd hm hlu2
    rw [heq] at h1; rw [← h1, h2]
  -- WLOG handle by symmetry: prove for u1.val < u2.val a contradiction; equal vals ⇒ equal
  by_contra hne
  -- val inequality
  have hvalne : u1.val ≠ u2.val := fun h => hne (ZMod.val_injective _ h)
  -- the shared parent's val
  have hpv : (betaParent U u1).val = (betaParent U u2).val := by rw [heq]
  -- a symmetric core: if a.val < b.val then contradiction
  have core : ∀ a b : ZMod (d*m), a ∈ U → b ∈ U → 1 ≤ a.val / m → 1 ≤ b.val / m →
      a.val % m = b.val % m → (betaParent U a).val = (betaParent U b).val →
      a.val < b.val → False := by
    intro a b haU hbU hla hlb hfibab hpvab hab
    -- shared parent val = φ + K*m, same K for both (since fiber same)
    -- betaParent a level = betaK a, betaParent b level = betaK b
    have hlevA : (betaParent U a).val / m = betaK U a := betaParent_level hd hm hla
    have hlevB : (betaParent U b).val / m = betaK U b := betaParent_level hd hm hlb
    have hKeq : betaK U a = betaK U b := by rw [← hlevA, ← hlevB, hpvab]
    -- parent val < a.val (parent strictly below a)
    have hpa_lt : (betaParent U a).val < a.val := betaParent_val_lt hd hm hla
    have hpb_lt : (betaParent U b).val < b.val := betaParent_val_lt hd hm hlb
    -- a.val = φ + (level a)*m, with level a > betaK a
    have hlevAa : betaK U a < a.val / m := by
      have hll : (betaParent U a).val / m < a.val / m := betaParent_level_lt hd hm hla
      rw [hlevA] at hll; exact hll
    -- a.val < b.val, same fiber ⇒ level a < level b
    have hlevab : a.val / m < b.val / m := by
      rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hfibab).mp hab.le) with h | h
      · exact h
      · exact absurd (level_injOn_fiber hfibab h) (fun heq2 => by rw [heq2] at hab; omega)
    -- the balance identities
    have hbalA := betaParent_balance hd hm hcanon haU hla
    have hbalB := betaParent_balance hd hm hcanon hbU hlb
    -- Scount split: Scount p b = Scount p a + 1 + Scount a b  (a interior, in U, p < a < b)
    have hpab : (betaParent U b).val < a.val := by rw [← hpvab]; exact hpa_lt
    have hsplit : Scount U (betaParent U b).val b.val
        = Scount U (betaParent U b).val a.val + 1 + Scount U a.val b.val :=
      Scount_split haU hpab hab
    -- rewrite Scount p_b a using p_b = p_a
    have hScpaa : Scount U (betaParent U b).val a.val = Scount U (betaParent U a).val a.val := by
      rw [hpvab]
    -- Now the deficiency of b at index (level a) is 0
    have hDef_b_la : Defc U (b.val % m) (b.val / m) b.val (a.val / m) = 0 := by
      unfold Defc
      -- φ + (level a)*m = a.val
      have haval : b.val % m + (a.val / m) * m = a.val := by
        rw [← hfibab]
        have := Nat.mod_add_div' a.val m; omega
      rw [haval]
      -- Scount a.val b.val = (lb - la - 1)
      have hScab : (Scount U a.val b.val : ℤ)
          = ((b.val / m : ℕ) : ℤ) - ((a.val / m : ℕ) : ℤ) - 1 := by
        have e1 : (Scount U (betaParent U b).val b.val : ℤ)
            = (Scount U (betaParent U a).val a.val : ℤ) + 1 + (Scount U a.val b.val : ℤ) := by
          rw [hsplit, hScpaa]; push_cast; ring
        rw [hbalB, hbalA, hKeq] at e1
        linarith
      rw [hScab]; ring
    -- contradiction with maximality: betaK b < level a ≤ level b - 1
    have hlt1 : betaK U b < a.val / m := by rw [← hKeq]; exact hlevAa
    have hlt2 : a.val / m ≤ b.val / m - 1 := by omega
    exact betaK_max hlt1 hlt2 hDef_b_la
  rcases lt_trichotomy u1.val u2.val with h | h | h
  · exact core u1 u2 hu1 hu2 hlu1 hlu2 hfib hpv h
  · exact hvalne h
  · exact core u2 u1 hu2 hu1 hlu2 hlu1 hfib.symm hpv.symm h
end CriticalPortraits
