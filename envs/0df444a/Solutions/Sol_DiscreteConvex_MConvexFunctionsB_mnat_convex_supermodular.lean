-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mnat_convex_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:45:49.577563+00:00
-- url     : https://prove2.me/submissions/96846709-59a0-4d5f-808a-0883833cdb86

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsB

namespace Supermod

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lift of a point of `ℤ^V` into the hyperplane of `ℤ^(Option V)`. -/
def lift (z : V → ℤ) : Option V → ℤ := fun o => o.elim (-(∑ v, z v)) z

theorem lift_eval (f : (V → ℤ) → WithTop ℝ) (z : V → ℤ) : LiftedFunction f (lift z) = f z := by
  unfold LiftedFunction lift
  simp

theorem sum_sub_char (z : V → ℤ) (u : V) : ∑ v, (z v - CharVec u v) = (∑ v, z v) - 1 := by
  rw [Finset.sum_sub_distrib]
  simp [CharVec]

theorem sum_add_char (z : V → ℤ) (u : V) : ∑ v, (z v + CharVec u v) = (∑ v, z v) + 1 := by
  rw [Finset.sum_add_distrib]
  simp [CharVec]

/-- The comparable-pair exchange: for `P ≥ Q` with `P u > Q u`,
`f(P - χ_u) + f(Q + χ_u) ≤ f(P) + f(Q)`. -/
theorem star (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (P Q : V → ℤ)
    (hPQ : ∀ w, Q w ≤ P w) (u : V) (hu : Q u < P u) (hP : f P ≠ ⊤) (hQ : f Q ≠ ⊤) :
    f (fun w => P w - CharVec u w) + f (fun w => Q w + CharVec u w) ≤ f P + f Q := by
  have hPd : lift P ∈ DomZ (LiftedFunction f) := by
    show LiftedFunction f (lift P) ≠ ⊤; rw [lift_eval]; exact hP
  have hQd : lift Q ∈ DomZ (LiftedFunction f) := by
    show LiftedFunction f (lift Q) ≠ ⊤; rw [lift_eval]; exact hQ
  obtain ⟨v, hv, hineq⟩ := hf (lift P) hPd (lift Q) hQd (some u)
    (by simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and]; exact hu)
  cases v with
  | some w =>
    simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    change P w < Q w at hv
    exact absurd (hPQ w) (not_le.mpr hv)
  | none =>
    have e1 : (fun o => lift P o - CharVec (some u) o + CharVec none o) =
        lift (fun w => P w - CharVec u w) := by
      funext o
      cases o with
      | none =>
        show -(∑ v, P v) - CharVec (some u) none + CharVec none none =
          -(∑ v, (P v - CharVec u v))
        rw [sum_sub_char]; simp [CharVec]; ring
      | some w => simp [lift, CharVec]
    have e2 : (fun o => lift Q o + CharVec (some u) o - CharVec none o) =
        lift (fun w => Q w + CharVec u w) := by
      funext o
      cases o with
      | none =>
        show -(∑ v, Q v) + CharVec (some u) none - CharVec none none =
          -(∑ v, (Q v + CharVec u v))
        rw [sum_add_char]; simp [CharVec]; ring
      | some w => simp [lift, CharVec]
    rw [e1, e2, lift_eval, lift_eval, lift_eval, lift_eval] at hineq
    exact hineq

/-- The box between two points of the domain lies in the domain. -/
theorem box (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (a b : V → ℤ)
    (ha : f a ≠ ⊤) (hb : f b ≠ ⊤) :
    ∀ n : ℕ, ∀ z : V → ℤ, (∀ w, a w ≤ z w) → (∀ w, z w ≤ b w) →
      ∑ w, (b w - z w) < n → f z ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
    intro z _ hzb hn
    have : 0 ≤ ∑ w, (b w - z w) := Finset.sum_nonneg (fun w _ => by linarith [hzb w])
    push_cast at hn; omega
  | succ n ih =>
    intro z haz hzb hn
    by_cases hzeq : z = b
    · rw [hzeq]; exact hb
    · obtain ⟨u, hu⟩ : ∃ u, z u < b u := by
        by_contra h; push Not at h
        exact hzeq (funext fun w => le_antisymm (hzb w) (h w))
      set z' : V → ℤ := fun w => z w + CharVec u w with hz'
      have hz'b : ∀ w, z' w ≤ b w := by
        intro w; simp only [hz', CharVec]; split_ifs with h
        · subst h; omega
        · linarith [hzb w]
      have haz' : ∀ w, a w ≤ z' w := by
        intro w; simp only [hz', CharVec]; split_ifs <;> linarith [haz w]
      have hmeas : ∑ w, (b w - z' w) < n := by
        have : ∑ w, (b w - z' w) = ∑ w, (b w - z w) - 1 := by
          simp only [hz']
          rw [show (∑ w, (b w - (z w + CharVec u w))) = ∑ w, ((b w - z w) - CharVec u w) by
            congr 1; funext w; ring, sum_sub_char]
        rw [this]; push_cast at hn; omega
      have hz'd := ih z' haz' hz'b hmeas
      have hs := star f hf z' a haz' u (by simp [hz', CharVec]; linarith [haz u]) hz'd ha
      have e : (fun w => z' w - CharVec u w) = z := by funext w; simp [hz']
      rw [e] at hs
      intro hz
      rw [hz, top_add] at hs
      exact (WithTop.add_ne_top.mpr ⟨hz'd, ha⟩) (top_le_iff.mp hs)

/-- Pointwise facts about `max`, `min` and `|·|`. -/
theorem abs_split (a b : ℤ) : |a - b| = (max a b - a) + (a - min a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem main (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    ∀ n : ℕ, ∀ x y : V → ℤ, ∑ v, |x v - y v| < n →
      f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v)) := by
  intro n
  induction n with
  | zero =>
    intro x y hn
    have : 0 ≤ ∑ v, |x v - y v| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    push_cast at hn; omega
  | succ n ih =>
    intro x y hn
    set M : V → ℤ := fun v => max (x v) (y v) with hM
    set m : V → ℤ := fun v => min (x v) (y v) with hm
    by_cases hle : ∀ v, x v ≤ y v
    · have e1 : M = y := funext fun v => max_eq_right (hle v)
      have e2 : m = x := funext fun v => min_eq_left (hle v)
      rw [e1, e2, add_comm]
    by_cases hge : ∀ v, y v ≤ x v
    · have e1 : M = x := funext fun v => max_eq_left (hge v)
      have e2 : m = y := funext fun v => min_eq_right (hge v)
      rw [e1, e2]
    push Not at hle hge
    obtain ⟨i, hi⟩ := hle
    by_cases hfin : f M = ⊤ ∨ f m = ⊤
    · rcases hfin with h | h <;> rw [h] <;> simp
    push Not at hfin
    obtain ⟨hMf, hmf⟩ := hfin
    have hmM : ∀ v, m v ≤ M v := fun v => by simp only [hm, hM]; exact min_le_max
    have inbox : ∀ z : V → ℤ, (∀ w, m w ≤ z w) → (∀ w, z w ≤ M w) → f z ≠ ⊤ := by
      intro z h1 h2
      exact box f hf m M hmf hMf ((∑ w, (M w - z w)).toNat + 1) z h1 h2 (by
        have : 0 ≤ ∑ w, (M w - z w) := Finset.sum_nonneg (fun w _ => by linarith [h2 w])
        push_cast; omega)
    have hti : 1 ≤ x i - m i := by simp only [hm]; rw [min_eq_right hi.le]; omega
    have tnn : ∀ v, 0 ≤ x v - m v := fun v => by simp only [hm]; linarith [min_le_left (x v) (y v)]
    set N := ∑ v, (x v - m v) with hN
    have htot : ∑ v, |x v - y v| = ∑ v, (M v - x v) + N := by
      rw [hN, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => by simp only [hM, hm]; rw [abs_split])
    have hsplit := Finset.add_sum_erase Finset.univ (fun v => x v - m v) (Finset.mem_univ i)
    have hrest : 0 ≤ ∑ v ∈ Finset.univ.erase i, (x v - m v) :=
      Finset.sum_nonneg (fun v _ => tnn v)
    by_cases hN1 : N = 1
    · -- `x = m + χ_i` and `y = M - χ_i`: the comparable-pair exchange applies directly
      have hti1 : x i - m i = 1 := by omega
      have hzero : ∀ v ∈ Finset.univ.erase i, x v - m v = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => tnn v)).mp (by omega)
      have ex : (fun w => m w + CharVec i w) = x := by
        funext w
        by_cases hw : w = i
        · subst hw; simp [CharVec]; omega
        · have := hzero w (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩)
          simp [CharVec, hw]; omega
      have ey : (fun w => M w - CharVec i w) = y := by
        funext w
        by_cases hw : w = i
        · subst hw; simp only [CharVec, if_true, hM]; simp only [hm] at hti1
          rw [max_eq_left hi.le]; rw [min_eq_right hi.le] at hti1; omega
        · have := hzero w (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩)
          simp only [hm] at this
          simp only [CharVec, hw, if_false, sub_zero, hM]
          have hxy : x w ≤ y w := by
            by_contra hc; push Not at hc; rw [min_eq_right hc.le] at this; omega
          exact max_eq_right hxy
      have hmi : m i < M i := by
        simp only [hM, hm]; rw [max_eq_left hi.le, min_eq_right hi.le]; exact hi
      have hs := star f hf M m hmM i hmi hMf hmf
      rw [ex, ey, add_comm] at hs
      exact hs
    · -- split off one unit at coordinate `i`
      have hN2 : 2 ≤ N := by omega
      set x' : V → ℤ := fun w => x w - CharVec i w with hx'
      set M' : V → ℤ := fun w => M w - CharVec i w with hM'
      have e1 : (fun v => max (x' v) (y v)) = M' := by
        funext w; simp only [hx', hM', hM, CharVec]
        by_cases hw : w = i
        · subst hw; simp only [if_true]; rw [max_eq_left (by omega), max_eq_left hi.le]
        · simp [hw]
      have e2 : (fun v => min (x' v) (y v)) = m := by
        funext w; simp only [hx', hm, CharVec]
        by_cases hw : w = i
        · subst hw; simp only [if_true]; rw [min_eq_right (by omega), min_eq_right hi.le]
        · simp [hw]
      have e3 : (fun v => max (x v) (M' v)) = M := by
        funext w; simp only [hM', hM, CharVec]
        by_cases hw : w = i
        · subst hw; simp only [if_true]; rw [max_eq_left hi.le, max_eq_left (by omega)]
        · simp only [hw, if_false, sub_zero]; exact max_eq_right (le_max_left _ _)
      have e4 : (fun v => min (x v) (M' v)) = x' := by
        funext w; simp only [hM', hM, hx', CharVec]
        by_cases hw : w = i
        · subst hw; simp only [if_true]; rw [max_eq_left hi.le, min_eq_right (by omega)]
        · simp only [hw, if_false, sub_zero]; exact min_eq_left (le_max_left _ _)
      have m1 : ∑ v, |x' v - y v| < n := by
        have : ∑ v, |x' v - y v| = ∑ v, (|x v - y v| - CharVec i v) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          simp only [hx', CharVec]
          by_cases hw : w = i
          · subst hw; simp only [if_true]
            rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; ring
          · simp [hw]
        rw [this, sum_sub_char]; push_cast at hn; omega
      have m2 : ∑ v, |x v - M' v| < n := by
        have : ∑ v, |x v - M' v| = ∑ v, ((M v - x v) + CharVec i v) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          simp only [hM', hM, CharVec]
          by_cases hw : w = i
          · subst hw; simp only [if_true]; rw [max_eq_left hi.le]
            rw [abs_of_nonneg (by omega)]; ring
          · simp only [hw, if_false, sub_zero, add_zero]
            rw [abs_of_nonpos (by linarith [le_max_left (x w) (y w)])]; ring
        rw [this, sum_add_char]; push_cast at hn; omega
      have IH1 := ih x' y m1
      have IH2 := ih x M' m2
      rw [e1, e2] at IH1
      rw [e3, e4] at IH2
      have hx'f : f x' ≠ ⊤ := inbox x' (fun w => by
          simp only [hx', hm, CharVec]; by_cases hw : w = i
          · subst hw; simp only [if_true]; rw [min_eq_right hi.le]; omega
          · simp only [hw, if_false, sub_zero]; exact min_le_left _ _)
        (fun w => by
          simp only [hx', hM, CharVec]; split_ifs <;> linarith [le_max_left (x w) (y w)])
      have hM'f : f M' ≠ ⊤ := inbox M' (fun w => by
          simp only [hM', hm, hM, CharVec]; by_cases hw : w = i
          · subst hw; simp only [if_true]; rw [min_eq_right hi.le, max_eq_left hi.le]; omega
          · simp only [hw, if_false, sub_zero]; exact min_le_max)
        (fun w => by simp only [hM', CharVec]; split_ifs <;> omega)
      have hsum := add_le_add IH1 IH2
      have hC : f x' + f M' ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hx'f, hM'f⟩
      have : (f x + f y) + (f x' + f M') ≤ (f M + f m) + (f x' + f M') := by
        calc (f x + f y) + (f x' + f M') = (f x' + f y) + (f x + f M') := by ac_rfl
          _ ≤ (f M' + f m) + (f M + f x') := hsum
          _ = (f M + f m) + (f x' + f M') := by ac_rfl
      exact (WithTop.add_le_add_iff_right hC).mp this

end Supermod

open Supermod in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    ∀ x y : V → ℤ, f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v)) := by
  intro x y
  exact main f hf ((∑ v, |x v - y v|).toNat + 1) x y (by
    have : 0 ≤ ∑ v, |x v - y v| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    push_cast; omega)

#print axioms solution
