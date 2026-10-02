-- Prove2me | solution 1 for DiscreteConvex.Algorithms.steepest_descent_K1_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T05:40:52.370292+00:00
-- url     : https://prove2.me/submissions/b0b12cee-dba3-43e7-82bc-18ad1dd2f9d8

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_DiscreteConvex_Algorithms_L1Dist
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Mathlib.Tactic.Linarith
import Definitions.Def_DiscreteConvex_Algorithms_Phi
import Definitions.Def_DiscreteConvex_Algorithms_PhiLE
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_DiscreteConvex_Algorithms_IsK1
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestPairTieBreak
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Data.Finset.Max
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentRunTieBreak

set_option autoImplicit false

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace SteepestK1UniqueCore

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

end SteepestK1UniqueCore

#print axioms SteepestK1UniqueCore.step_toward
#print axioms SteepestK1UniqueCore.distance_drop
#print axioms SteepestK1UniqueCore.prefix_bound
end

section
open DiscreteConvex.Algorithms
namespace SteepestLexOrder

def move (a b : ℕ) : ℕ → ℤ := fun n =>
  (if n = b then 1 else 0) - (if n = a then 1 else 0)

private theorem move_lt_zero (a b : ℕ) (hab : a < b) :
    toLex (move a b) < (0 : Lex (ℕ → ℤ)) := by
  refine ⟨a, ?_, ?_⟩
  · intro n hn
    change move a b n = 0
    simp only [move]
    split_ifs <;> omega
  · change move a b a < 0
    simp only [move]
    split_ifs <;> omega

private theorem zero_lt_move (a b : ℕ) (hba : b < a) :
    (0 : Lex (ℕ → ℤ)) < toLex (move a b) := by
  refine ⟨b, ?_, ?_⟩
  · intro n hn
    change 0 = move a b n
    simp only [move]
    split_ifs <;> omega
  · change 0 < move a b b
    simp only [move]
    split_ifs <;> omega

private theorem negative_source_lt (a b c d : ℕ) (hab : a < b) (hcd : c < d)
    (hac : a < c) : toLex (move a b) < toLex (move c d) := by
  refine ⟨a, ?_, ?_⟩
  · intro n hn
    change move a b n = move c d n
    simp only [move]
    split_ifs <;> omega
  · change move a b a < move c d a
    simp only [move]
    split_ifs <;> omega

private theorem same_source_le (a b d : ℕ) (hab : a < b) (had : a < d)
    (hdb : d ≤ b) : toLex (move a b) ≤ toLex (move a d) := by
  rcases eq_or_lt_of_le hdb with rfl | hdb
  · exact le_rfl
  apply le_of_lt
  refine ⟨d, ?_, ?_⟩
  · intro n hn
    change move a b n = move a d n
    simp only [move]
    split_ifs <;> omega
  · change move a b d < move a d d
    simp only [move]
    split_ifs <;> omega

private theorem positive_dest_lt (a b c d : ℕ) (hba : b < a) (hdc : d < c)
    (hdb : d < b) : toLex (move a b) < toLex (move c d) := by
  refine ⟨d, ?_, ?_⟩
  · intro n hn
    change move a b n = move c d n
    simp only [move]
    split_ifs <;> omega
  · change move a b d < move c d d
    simp only [move]
    split_ifs <;> omega

private theorem same_dest_le (a c b : ℕ) (hba : b < a) (hbc : b < c)
    (hac : a ≤ c) : toLex (move a b) ≤ toLex (move c b) := by
  rcases eq_or_lt_of_le hac with rfl | hac
  · exact le_rfl
  apply le_of_lt
  refine ⟨a, ?_, ?_⟩
  · intro n hn
    change move a b n = move c b n
    simp only [move]
    split_ifs <;> omega
  · change move a b a < move c b a
    simp only [move]
    split_ifs <;> omega

theorem move_le_of_phiLE (a b c d : ℕ) (hab : a ≠ b) (hcd : c ≠ d)
    (h : PhiLE (Phi id a b) (Phi id c d)) :
    toLex (move a b) ≤ toLex (move c d) := by
  by_cases hablt : a < b
  · by_cases hcdlt : c < d
    · have hcomp : a < c ∨ (a = c ∧ d ≤ b) := by
        simp [Phi, PhiLE, hablt, hcdlt] at h
        omega
      rcases hcomp with hac | ⟨rfl, hdb⟩
      · exact (negative_source_lt a b c d hablt hcdlt hac).le
      · exact same_source_le a b d hablt hcdlt hdb
    · have hdc : d < c := by omega
      exact (lt_trans (move_lt_zero a b hablt) (zero_lt_move c d hdc)).le
  · have hba : b < a := by omega
    by_cases hcdlt : c < d
    · simp [Phi, PhiLE, hablt, hcdlt] at h
    · have hdc : d < c := by omega
      have hcomp : d < b ∨ (d = b ∧ a ≤ c) := by
        simp [Phi, PhiLE, hablt, hcdlt] at h
        omega
      rcases hcomp with hdb | ⟨rfl, hac⟩
      · exact (positive_dest_lt a b c d hba hdc hdb).le
      · exact same_dest_le a c d hba hdc hac

abbrev Cost := ℝ ×ₗ Lex (ℕ → ℤ)

#print axioms move_le_of_phiLE
end SteepestLexOrder
end

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms
namespace SteepestLexEmbedding
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def rankVector (φ : V → ℕ) : (V → ℤ) →+ (ℕ → ℤ) where
  toFun x n := ∑ v, if φ v = n then x v else 0
  map_zero' := by ext n; simp
  map_add' x y := by
    ext n
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp

@[simp] theorem rankVector_apply (φ : V → ℕ) (x : V → ℤ) (n : ℕ) :
    rankVector φ x n = ∑ v, if φ v = n then x v else 0 := rfl

theorem rankVector_at (φ : V → ℕ) (hφ : Function.Injective φ) (x : V → ℤ) (u : V) :
    rankVector φ x (φ u) = x u := by
  classical
  simp [rankVector_apply, hφ.eq_iff]

theorem rankVector_injective (φ : V → ℕ) (hφ : Function.Injective φ) :
    Function.Injective (rankVector φ) := by
  intro x y h
  funext u
  have hh := congrFun h (φ u)
  simpa only [rankVector_at φ hφ] using hh

theorem rankVector_charVec (φ : V → ℕ) (u : V) (n : ℕ) :
    rankVector φ (CharVec u) n = if n = φ u then 1 else 0 := by
  classical
  rw [rankVector_apply, Finset.sum_eq_single u]
  · simp [CharVec, eq_comm]
  · intro v _ hv
    simp [CharVec, hv]
  · simp

theorem rankVector_exchange (φ : V → ℕ) (x : V → ℤ) (u v : V) :
    rankVector φ (fun w => x w-CharVec u w+CharVec v w) =
      rankVector φ x + SteepestLexOrder.move (φ u) (φ v) := by
  change rankVector φ (x - CharVec u + CharVec v) = _
  rw [map_add, map_sub]
  ext n
  simp only [Pi.add_apply, Pi.sub_apply, rankVector_charVec, SteepestLexOrder.move]
  ring

theorem domain_finite_of_K1 (f : (V → ℤ) → WithTop ℝ) (k : ℕ)
    (hk : IsK1 f k) (x0 : V → ℤ) (hx0 : x0 ∈ DomZ f) :
    (DomZ f).Finite := by
  classical
  let S := Fintype.piFinset (fun v : V => Finset.Icc (x0 v-(k : ℤ)) (x0 v+(k : ℤ)))
  apply (Finset.finite_toSet S).subset
  intro x hx
  apply Fintype.mem_piFinset.mpr
  intro v
  have hdist := hk.1 x hx x0 hx0
  have hv : (x v-x0 v).natAbs ≤ k :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans hdist
  have hupper := Int.le_natAbs (a := x v-x0 v)
  have hlower := Int.le_natAbs (a := -(x v-x0 v))
  simp only [Int.natAbs_neg] at hlower
  rw [Finset.mem_Icc]
  omega

#print axioms rankVector_exchange
#print axioms domain_finite_of_K1
end SteepestLexEmbedding
end

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms
open SteepestLexOrder SteepestLexEmbedding
namespace SteepestLexLift
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def liftCost (φ : V → ℕ) (f : (V → ℤ) → WithTop ℝ)
    (x : V → ℤ) : WithTop Cost :=
  (f x).map (fun r => toLex (r, toLex (rankVector φ x)))

@[simp] theorem liftCost_ne_top (φ : V → ℕ) (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) :
    liftCost φ f x ≠ ⊤ ↔ f x ≠ ⊤ := by simp [liftCost]

@[simp] theorem liftCost_of_coe (φ : V → ℕ) (f : (V → ℤ) → WithTop ℝ)
    (x : V → ℤ) (r : ℝ) (hr : f x = (r : WithTop ℝ)) :
    liftCost φ f x = (toLex (r, toLex (rankVector φ x)) : Cost) := by
  simp [liftCost, hr]

theorem liftCost_le_of_lt (φ : V → ℕ) (f : (V → ℤ) → WithTop ℝ)
    (x y : V → ℤ) (hxy : f x < f y) : liftCost φ f x < liftCost φ f y := by
  have hx : f x ≠ ⊤ := ne_top_of_lt hxy
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  by_cases hy : f y = ⊤
  · simp [liftCost, hy, ← hr]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  rw [← hr, ← hs, WithTop.coe_lt_coe] at hxy
  rw [liftCost_of_coe φ f x r hr.symm, liftCost_of_coe φ f y s hs.symm, WithTop.coe_lt_coe]
  exact Prod.Lex.left _ _ hxy

theorem liftCost_injOn (φ : V → ℕ) (hφ : Function.Injective φ)
    (f : (V → ℤ) → WithTop ℝ) : Set.InjOn (liftCost φ f) (DomZ f) := by
  intro x hx y hy hxy
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  rw [liftCost_of_coe φ f x r hr.symm, liftCost_of_coe φ f y s hs.symm,
    WithTop.coe_inj] at hxy
  have hv := congrArg (fun z : Cost => ofLex (ofLex z).2) hxy
  exact rankVector_injective φ hφ hv

theorem liftCost_exchange (φ : V → ℕ) (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) (x y : V → ℤ)
    (hx : liftCost φ f x ≠ ⊤) (hy : liftCost φ f y ≠ ⊤)
    (u : V) (hu : y u < x u) :
    ∃ v : V, x v < y v ∧
      liftCost φ f (fun w => x w-CharVec u w+CharVec v w) +
      liftCost φ f (fun w => y w+CharVec u w-CharVec v w) ≤
      liftCost φ f x + liftCost φ f y := by
  classical
  have hx0 : f x ≠ ⊤ := (liftCost_ne_top φ f x).mp hx
  have hy0 : f y ≠ ⊤ := (liftCost_ne_top φ f y).mp hy
  obtain ⟨v, hv, he⟩ := hf x hx0 y hy0 u (by simpa [SuppPos] using hu)
  refine ⟨v, by simpa [SuppNeg] using hv, ?_⟩
  let x' : V → ℤ := fun w => x w-CharVec u w+CharVec v w
  let y' : V → ℤ := fun w => y w+CharVec u w-CharVec v w
  have hsumfin : f x' + f y' ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hx0,hy0⟩) he
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy0
  obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.mp (WithTop.add_ne_top.mp hsumfin).1
  obtain ⟨s', hs'⟩ := WithTop.ne_top_iff_exists.mp (WithTop.add_ne_top.mp hsumfin).2
  have he0 : r'+s' ≤ r+s := by
    change f x' + f y' ≤ f x+f y at he
    rw [← hr, ← hs, ← hr', ← hs', ← WithTop.coe_add, ← WithTop.coe_add,
      WithTop.coe_le_coe] at he
    exact he
  change liftCost φ f x' + liftCost φ f y' ≤ liftCost φ f x + liftCost φ f y
  rw [liftCost_of_coe φ f x r hr.symm, liftCost_of_coe φ f y s hs.symm,
    liftCost_of_coe φ f x' r' hr'.symm, liftCost_of_coe φ f y' s' hs'.symm,
    ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  have hconserve : rankVector φ x' + rankVector φ y' = rankVector φ x + rankVector φ y := by
    rw [← map_add, ← map_add]
    congr 1
    ext w
    simp only [Pi.add_apply, x', y']
    ring
  apply Prod.Lex.le_iff.mpr
  rcases lt_or_eq_of_le he0 with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, le_of_eq (congrArg toLex hconserve)⟩

theorem liftCost_le_of_primary_and_secondary (φ : V → ℕ)
    (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) (hxy : f x ≤ f y)
    (hsecondary : f x = f y → toLex (rankVector φ x) ≤ toLex (rankVector φ y)) :
    liftCost φ f x ≤ liftCost φ f y := by
  by_cases hy : f y = ⊤
  · simp [liftCost, hy]
  have hx : f x ≠ ⊤ := ne_top_of_le_ne_top hy hxy
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  have hle : r ≤ s := by simpa only [← hr, ← hs, WithTop.coe_le_coe] using hxy
  rw [liftCost_of_coe φ f x r hr.symm, liftCost_of_coe φ f y s hs.symm,
    WithTop.coe_le_coe, Prod.Lex.le_iff]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hsecondary (hr.symm.trans ((congrArg (fun t : ℝ => (t : WithTop ℝ)) heq).trans hs))⟩

theorem lifted_steepest_pair (φ : V → ℕ) (hφ : Function.Injective φ)
    (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (u v : V)
    (hpair : IsSteepestPairTieBreak f φ x u v) :
    u ≠ v ∧ ∀ u' v' : V, u' ≠ v' →
      liftCost φ f (fun w => x w-CharVec u w+CharVec v w) ≤
      liftCost φ f (fun w => x w-CharVec u' w+CharVec v' w) := by
  refine ⟨hpair.1, ?_⟩
  intro u' v' huv'
  obtain ⟨hle, htie⟩ := hpair.2 u' v' huv'
  apply liftCost_le_of_primary_and_secondary φ f _ _ hle
  intro heq
  have hkey : PhiLE (Phi id (φ u) (φ v)) (Phi id (φ u') (φ v')) := htie heq
  have hmove := SteepestLexOrder.move_le_of_phiLE (φ u) (φ v) (φ u') (φ v')
    (fun h => hpair.1 (hφ h)) (fun h => huv' (hφ h)) hkey
  rw [rankVector_exchange, rankVector_exchange]
  change toLex (rankVector φ x) + toLex (SteepestLexOrder.move (φ u) (φ v)) ≤
    toLex (rankVector φ x) + toLex (SteepestLexOrder.move (φ u') (φ v'))
  exact add_le_add le_rfl hmove

theorem exists_unique_lifted_minimum (φ : V → ℕ) (hφ : Function.Injective φ)
    (f : (V → ℤ) → WithTop ℝ) (hfin : (DomZ f).Finite)
    (hne : (DomZ f).Nonempty) :
    ∃ z : V → ℤ, z ∈ DomZ f ∧
      (∀ y, liftCost φ f z ≤ liftCost φ f y) ∧
      (∀ y, liftCost φ f y ≤ liftCost φ f z → y = z) := by
  classical
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image hfin.toFinset (liftCost φ f)
    (by simpa using hne)
  have hzdom : z ∈ DomZ f := by simpa using hz
  have hglobal (y : V → ℤ) : liftCost φ f z ≤ liftCost φ f y := by
    by_cases hy : y ∈ DomZ f
    · exact hmin y (by simpa using hy)
    · have htop : f y = ⊤ := by simpa [DomZ] using hy
      simp [liftCost, htop]
  refine ⟨z, hzdom, hglobal, ?_⟩
  intro y hy
  have hyfin : liftCost φ f y ≠ ⊤ :=
    ne_top_of_le_ne_top ((liftCost_ne_top φ f z).mpr hzdom) hy
  exact liftCost_injOn φ hφ f ((liftCost_ne_top φ f y).mp hyfin) hzdom
    (le_antisymm hy (hglobal y))

#print axioms liftCost_exchange
#print axioms lifted_steepest_pair
#print axioms exists_unique_lifted_minimum
end SteepestLexLift
end

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms
open SteepestK1UniqueCore SteepestLexOrder SteepestLexEmbedding SteepestLexLift
namespace SteepestK1Assembly

theorem bound {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (φ : V → ℕ)
    (hφ : Function.Injective φ) (k1 : ℕ) (hK1 : IsK1 f k1)
    (x0 : V → ℤ) (hx0 : x0 ∈ DomZ f) (x : ℕ → V → ℤ) (N : ℕ)
    (hrun : IsSteepestDescentRunTieBreak f φ x0 x N) : 2*N ≤ k1 := by
  classical
  let F := liftCost φ f
  have hF : Exchange F := by
    intro a ha b hb u hu
    obtain ⟨v, hv, he⟩ := liftCost_exchange φ f hf a b ha hb u hu
    refine ⟨v, hv, ?_⟩
    have hrev : (fun w => b w+CharVec u w-CharVec v w) =
        SteepestK1UniqueCore.move b v u := by
      funext w
      dsimp [SteepestK1UniqueCore.move]
      omega
    rw [hrev] at he
    exact he
  obtain ⟨z, hz, hglobal, hunique⟩ := exists_unique_lifted_minimum φ hφ f
    (domain_finite_of_K1 f k1 hK1 x0 hx0) ⟨x0,hx0⟩
  have hzfin : F z ≠ ⊤ := (liftCost_ne_top φ f z).mpr hz
  have hstrict (w : V → ℤ) (hw : w ≠ z) : F z < F w :=
    lt_of_not_ge (fun h => hw (hunique w h))
  have hxfin : F (x 0) ≠ ⊤ := by
    rw [hrun.1]
    exact (liftCost_ne_top φ f x0).mpr hx0
  have hsteps : ∀ i < N, ∃ u v, Selected F (x i) u v ∧
      x (i+1) = SteepestK1UniqueCore.move (x i) u v ∧ F (x (i+1)) < F (x i) := by
    intro i hi
    obtain ⟨u, v, hpair, hstep⟩ := hrun.2.1 i hi
    have hdec : f (SteepestK1UniqueCore.move (x i) u v) < f (x i) := by
      apply lt_of_not_ge
      intro hle
      apply hrun.2.2.1 i hi
      intro a b hab
      exact hle.trans (hpair.2 a b hab).1
    refine ⟨u,v,lifted_steepest_pair φ hφ f (x i) u v hpair,hstep,?_⟩
    rw [hstep]
    exact liftCost_le_of_lt φ f _ _ hdec
  have hbound := prefix_bound F hF z hzfin hstrict x N hxfin hsteps
  rw [hrun.1] at hbound
  have hdiam := hK1.1 x0 hx0 z hz
  omega

#print axioms bound
end SteepestK1Assembly
end

open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (φ : V → ℕ) (hphi : Function.Injective φ)
    (k1 : ℕ) (hK1 : IsK1 f k1) (x0 : V → ℤ) (hx0 : x0 ∈ DomZ f) (x : ℕ → V → ℤ) (N : ℕ)
    (hrun : IsSteepestDescentRunTieBreak f φ x0 x N) :
    2 * N ≤ k1 := by
  exact SteepestK1Assembly.bound f hf φ hphi k1 hK1 x0 hx0 x N hrun

#print axioms solution
