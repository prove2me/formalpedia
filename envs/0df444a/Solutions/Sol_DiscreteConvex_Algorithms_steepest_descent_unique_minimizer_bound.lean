-- Prove2me | solution 1 for DiscreteConvex.Algorithms.steepest_descent_unique_minimizer_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T05:39:30.704987+00:00
-- url     : https://prove2.me/submissions/51a14ad7-a8c9-4d06-adb0-bc7702f3a042

import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentRun
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_DiscreteConvex_Algorithms_L1Dist
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Mathlib.Tactic.Linarith

open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace SteepestUniqueCore

variable {V C : Type*} [Fintype V] [DecidableEq V]
variable [LinearOrderedAddCommMonoidWithTop C]

def move (x : V → ℤ) (u v : V) : V → ℤ :=
  fun w => x w - CharVec u w + CharVec v w

def Exchange (F : (V → ℤ) → C) : Prop :=
  ∀ x, F x ≠ ⊤ → ∀ y, F y ≠ ⊤ → ∀ u, y u < x u →
    ∃ v, x v < y v ∧ F (move x u v) + F (move y v u) ≤ F x + F y

def Selected (F : (V → ℤ) → C) (x : V → ℤ) (u v : V) : Prop :=
  u ≠ v ∧ ∀ a b, a ≠ b → F (move x u v) ≤ F (move x a b)

lemma move_ne (x : V → ℤ) {u v : V} (huv : u ≠ v) : move x u v ≠ x := by
  intro h
  have := congrFun h u
  simp [move, CharVec, huv] at this

lemma move_self (x : V → ℤ) (u : V) : move x u u = x := by
  funext w
  simp [move]

lemma move_reverse (x : V → ℤ) (u v w : V) :
    move (move x u v) w u = move x w v := by
  funext a
  simp only [move]
  omega

lemma move_forward (x : V → ℤ) (u v w : V) :
    move (move x u v) v w = move x u w := by
  funext a
  simp only [move]
  omega

/-- Every genuinely improving steepest step moves both coordinates toward the unique minimum. -/
theorem step_toward (F : (V → ℤ) → C) (hF : Exchange F)
    (z x : V → ℤ) (hz : F z ≠ ⊤)
    (hmin : ∀ w, w ≠ z → F z < F w)
    (hx : F x ≠ ⊤) (u v : V) (hsel : Selected F x u v)
    (hdec : F (move x u v) < F x) : z u < x u ∧ x v < z v := by
  have hy : F (move x u v) ≠ ⊤ := ne_top_of_lt hdec
  constructor
  · by_contra h
    have hu : move x u v u < z u := by
      simp [move, CharVec, hsel.1, hsel.1.symm]
      omega
    obtain ⟨w, hw, he⟩ := hF z hz (move x u v) hy u hu
    have huw : u ≠ w := by intro e; subst w; omega
    have hstrict := hmin (move z u w) (move_ne z huw)
    have hc : F (move x u v) ≤ F (move (move x u v) w u) := by
      rw [move_reverse]
      by_cases hwv : w = v
      · subst w
        simpa [move_self] using hdec.le
      · exact hsel.2 w v hwv
    have hl : F z + F (move x u v) < F (move z u w) + F (move x u v) :=
      (add_lt_add_iff_left_of_ne_top hy).2 hstrict
    exact (not_lt_of_ge he) (hl.trans_le (add_le_add le_rfl hc))
  · by_contra h
    have hv : z v < move x u v v := by
      simp [move, CharVec, hsel.1, hsel.1.symm]
      omega
    obtain ⟨w, hw, he⟩ := hF (move x u v) hy z hz v hv
    have hvw : v ≠ w := by intro e; subst w; omega
    have hstrict := hmin (move z w v) (move_ne z hvw.symm)
    have hc : F (move x u v) ≤ F (move (move x u v) v w) := by
      rw [move_forward]
      by_cases huw : u = w
      · subst w
        simpa [move_self] using hdec.le
      · exact hsel.2 u w huw
    have hl : F (move x u v) + F z < F (move x u v) + F (move z w v) :=
      (add_lt_add_iff_right_of_ne_top hy).2 hstrict
    exact (not_lt_of_ge he) (hl.trans_le (add_le_add hc le_rfl))

lemma distance_drop (x z : V → ℤ) (u v : V) (huv : u ≠ v)
    (hu : z u < x u) (hv : x v < z v) :
    L1Dist (move x u v) z + 2 = L1Dist x z := by
  have hcoord (i : V) : (x i - z i).natAbs =
      (move x u v i - z i).natAbs + (if i = u then 1 else 0) +
        (if i = v then 1 else 0) := by
    by_cases hiu : i = u
    · subst i
      simp [move, CharVec, huv, huv.symm]
      omega
    · by_cases hiv : i = v
      · subst i
        simp [move, CharVec, huv, huv.symm]
        omega
      · simp [move, CharVec, hiu, hiv]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hcoord i)
  simpa [L1Dist, Finset.sum_add_distrib, Finset.sum_ite_eq', add_assoc] using hh.symm

/-- Prefix bound; final terminality is intentionally unnecessary. -/
theorem prefix_bound (F : (V → ℤ) → C) (hF : Exchange F)
    (z : V → ℤ) (hz : F z ≠ ⊤) (hmin : ∀ w, w ≠ z → F z < F w)
    (x : ℕ → V → ℤ) (N : ℕ) (hx : F (x 0) ≠ ⊤)
    (hsteps : ∀ i < N, ∃ u v, Selected F (x i) u v ∧
      x (i + 1) = move (x i) u v ∧ F (x (i + 1)) < F (x i)) :
    2 * N + L1Dist (x N) z ≤ L1Dist (x 0) z := by
  have haux : ∀ n ≤ N, F (x n) ≠ ⊤ ∧
      2 * n + L1Dist (x n) z = L1Dist (x 0) z := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hx, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨hfin, hd⟩ := ih (by omega)
      obtain ⟨u, v, hs, he, hl⟩ := hsteps n (by omega)
      have ht := step_toward F hF z (x n) hz hmin hfin u v hs (he ▸ hl)
      have hd' := distance_drop (x n) z u v hs.1 ht.1 ht.2
      refine ⟨ne_top_of_lt hl, ?_⟩
      rw [← he] at hd'
      omega
  exact (haux N le_rfl).2.le

end SteepestUniqueCore

#print axioms SteepestUniqueCore.step_toward
#print axioms SteepestUniqueCore.distance_drop
#print axioms SteepestUniqueCore.prefix_bound

open SteepestUniqueCore DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (xstar : V → ℤ)
    (hxstar : ArgMin f = {xstar}) (x0 : V → ℤ) (hx0 : x0 ∈ DomZ f)
    (x : ℕ → V → ℤ) (N : ℕ) (hrun : IsSteepestDescentRun f x0 x N) :
    2 * N ≤ L1Dist x0 xstar := by
  have hglobal : ∀ y, f xstar ≤ f y := by
    have hm : xstar ∈ ArgMin f := by rw [hxstar]; simp
    exact hm
  have hstrict (y : V → ℤ) (hy : y ≠ xstar) : f xstar < f y := by
    by_contra h
    have hm : y ∈ ArgMin f := fun w => (le_of_not_gt h).trans (hglobal w)
    rw [hxstar] at hm
    exact hy (Set.mem_singleton_iff.mp hm)
  have hfinite : f xstar ≠ ⊤ := ne_top_of_le_ne_top hx0 (hglobal x0)
  have hexc : Exchange f := by
    intro a ha b hb u hu
    obtain ⟨v, hv, hh⟩ := hf a ha b hb u (by simpa [SuppPos] using hu)
    refine ⟨v, by simpa [SuppNeg] using hv, ?_⟩
    have he : (fun w => b w + CharVec u w - CharVec v w) = move b v u := by
      funext w
      simp only [move]
      omega
    rw [he] at hh
    exact hh
  have hs : ∀ i < N, ∃ u v, Selected f (x i) u v ∧
      x (i + 1) = move (x i) u v ∧ f (x (i + 1)) < f (x i) := by
    intro i hi
    obtain ⟨u, v, huv, hstep⟩ := hrun.2.1 i hi
    have hn := hrun.2.2.1 i hi
    simp only [IsSteepestDescentTerminal, not_forall, _root_.not_imp, not_le] at hn
    obtain ⟨a, b, hab, hbetter⟩ := hn
    refine ⟨u, v, huv, hstep, ?_⟩
    rw [hstep]
    exact (huv.2 a b hab).trans_lt hbetter
  have hb := prefix_bound f hexc xstar hfinite hstrict x N
    (by simpa only [hrun.1, DomZ, Set.mem_setOf_eq] using hx0) hs
  rw [hrun.1] at hb
  omega

#print axioms solution
