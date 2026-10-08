-- Prove2me | solution 1 for DoubleGreedyUSM.Fractional.eq4_eq5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:42:30.994704+00:00
-- url     : https://prove2.me/submissions/e52ce857-27d7-4b9a-b857-71ad545c9ba9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

set_option autoImplicit false

namespace E09b7c13Aux

open DoubleGreedyUSM.Fractional

/-- Each product term of the multilinear extension is affine along the direction `indicator {u}`. -/
lemma term_affine {X : Type} [Fintype X] [DecidableEq X] (S : Finset X)
    (x : X → ℝ) (u : X) (t : ℝ) :
    (∏ i : X, (if i ∈ S then (x + t • indicator {u}) i else 1 - (x + t • indicator {u}) i))
      = (∏ i : X, (if i ∈ S then x i else 1 - x i))
        + t * ((∏ i : X, (if i ∈ S then (x + indicator {u}) i else 1 - (x + indicator {u}) i))
              - (∏ i : X, (if i ∈ S then x i else 1 - x i))) := by
  rw [Fintype.prod_eq_mul_prod_compl u
      (fun i => if i ∈ S then (x + t • indicator {u}) i else 1 - (x + t • indicator {u}) i),
    Fintype.prod_eq_mul_prod_compl u (fun i => if i ∈ S then x i else 1 - x i),
    Fintype.prod_eq_mul_prod_compl u
      (fun i => if i ∈ S then (x + indicator {u}) i else 1 - (x + indicator {u}) i)]
  have h1 : (∏ i ∈ ({u}ᶜ : Finset X),
      (if i ∈ S then (x + t • indicator {u}) i else 1 - (x + t • indicator {u}) i))
      = ∏ i ∈ ({u}ᶜ : Finset X), (if i ∈ S then x i else 1 - x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiu : i ≠ u := by simpa using hi
    simp [indicator, hiu]
  have h2 : (∏ i ∈ ({u}ᶜ : Finset X),
      (if i ∈ S then (x + indicator {u}) i else 1 - (x + indicator {u}) i))
      = ∏ i ∈ ({u}ᶜ : Finset X), (if i ∈ S then x i else 1 - x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiu : i ≠ u := by simpa using hi
    simp [indicator, hiu]
  rw [h1, h2]
  by_cases hu : u ∈ S
  · simp only [hu, Pi.add_apply, Pi.smul_apply, indicator, Finset.mem_singleton,
      smul_eq_mul, eq_self_iff_true, if_true, ↓reduceIte, mul_one]
    ring
  · simp only [hu, Pi.add_apply, Pi.smul_apply, indicator, Finset.mem_singleton,
      smul_eq_mul, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one]
    ring

lemma F_affine {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (x : X → ℝ) (u : X) (t : ℝ) :
    NonmonotoneSubmod.Shared.F f (x + t • indicator {u}) - NonmonotoneSubmod.Shared.F f x
      = t * (NonmonotoneSubmod.Shared.F f (x + indicator {u}) - NonmonotoneSubmod.Shared.F f x) := by
  unfold NonmonotoneSubmod.Shared.F
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [term_affine S x u t]
  ring

lemma F_affine_sub {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (y : X → ℝ) (u : X) (r : ℝ) :
    NonmonotoneSubmod.Shared.F f (y - r • indicator {u}) - NonmonotoneSubmod.Shared.F f y
      = r * (NonmonotoneSubmod.Shared.F f (y - indicator {u}) - NonmonotoneSubmod.Shared.F f y) := by
  have e1 : y - r • indicator {u} = y + (-r) • indicator {u} := by
    rw [neg_smul, ← sub_eq_add_neg]
  have e2 : y - indicator {u} = y + (-1 : ℝ) • indicator {u} := by
    rw [neg_smul, one_smul, ← sub_eq_add_neg]
  rw [e1, e2, F_affine, F_affine]
  ring

lemma state_succ {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (l : List X) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    state f l i = step f (state f l (i - 1)) (l[i - 1]'(by omega)) := by
  unfold state
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append]
  rfl

end E09b7c13Aux

open DoubleGreedyUSM.Fractional in
theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (l : List X) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length)
    (ha : 0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)))
    (hb : 0 < bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) :
    NonmonotoneSubmod.Shared.F f (state f l i).1 - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).1
        = aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)) ^ 2
          / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
              + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) ∧
    NonmonotoneSubmod.Shared.F f (state f l i).2 - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).2
        = bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega)) ^ 2
          / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
              + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) := by
  rw [E09b7c13Aux.state_succ f l i hi1 hin]
  set s := state f l (i - 1) with hs
  set u := l[i - 1]'(by omega) with hu
  set a := aGain f s.1 u with ha_def
  set b := bGain f s.2 u with hb_def
  have hab : a + b ≠ 0 := by linarith
  have hma : max a 0 = a := max_eq_left ha
  have hmb : max b 0 = b := max_eq_left hb.le
  have hstep : step f s u = (s.1 + (a / (a + b)) • indicator {u},
      s.2 - (b / (a + b)) • indicator {u}) := by
    simp only [step, ← ha_def, ← hb_def, hma, hmb, hab, if_false]
  rw [hstep]
  constructor
  · show NonmonotoneSubmod.Shared.F f (s.1 + (a / (a + b)) • indicator {u})
        - NonmonotoneSubmod.Shared.F f s.1 = a ^ 2 / (a + b)
    rw [E09b7c13Aux.F_affine]
    have : NonmonotoneSubmod.Shared.F f (s.1 + indicator {u}) - NonmonotoneSubmod.Shared.F f s.1
        = a := rfl
    rw [this]
    field_simp
  · show NonmonotoneSubmod.Shared.F f (s.2 - (b / (a + b)) • indicator {u})
        - NonmonotoneSubmod.Shared.F f s.2 = b ^ 2 / (a + b)
    rw [E09b7c13Aux.F_affine_sub]
    have : NonmonotoneSubmod.Shared.F f (s.2 - indicator {u}) - NonmonotoneSubmod.Shared.F f s.2
        = b := rfl
    rw [this]
    field_simp
