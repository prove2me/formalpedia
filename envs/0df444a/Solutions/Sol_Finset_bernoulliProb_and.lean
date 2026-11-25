-- Prove2me | solution 1 for Finset.bernoulliProb_and
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:28.655799+00:00
-- url     : https://prove2.me/submissions/9711e366-668c-41ab-a50d-957d52bd7157

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_sum_bernoulliWeight
section
@[expose] public section
open Finset
namespace Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
private theorem bernoulliWeight_union {T : Finset α} (hT : T ⊆ U) {a b : Finset α} (ha : a ⊆ T)
    (hb : b ⊆ U \ T) :
    U.bernoulliWeight p (a ∪ b) = T.bernoulliWeight p a * (U \ T).bernoulliWeight p b := by
  have hab : Disjoint a b := disjoint_of_subset_left ha (disjoint_of_subset_right hb
    disjoint_sdiff)
  have hsplit : U \ (a ∪ b) = (T \ a) ∪ ((U \ T) \ b) := by
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx, hxab⟩
      by_cases hxT : x ∈ T
      · exact .inl ⟨hxT, fun h => hxab (.inl h)⟩
      · exact .inr ⟨⟨hx, hxT⟩, fun h => hxab (.inr h)⟩
    · rintro (⟨hxT, hxa⟩ | ⟨⟨hx, hxT⟩, hxb⟩)
      · exact ⟨hT hxT, by rintro (h | h); exacts [hxa h, (mem_sdiff.mp (hb h)).2 hxT]⟩
      · exact ⟨hx, by rintro (h | h); exacts [hxT (ha h), hxb h]⟩
  have hdisj : Disjoint (T \ a) ((U \ T) \ b) :=
    disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset disjoint_sdiff)
  rw [bernoulliWeight, bernoulliWeight, bernoulliWeight, hsplit, card_union_of_disjoint hab,
    card_union_of_disjoint hdisj, pow_add, pow_add]
  ring
private theorem sum_powerset_split {T : Finset α} (hT : T ⊆ U) (f : Finset α → ℝ) :
    ∑ A ∈ U.powerset, f A = ∑ a ∈ T.powerset, ∑ b ∈ (U \ T).powerset, f (a ∪ b) := by
  rw [← sum_product']
  refine sum_nbij' (fun A => (A ∩ T, A \ T)) (fun x => x.1 ∪ x.2) (fun A hA => ?_)
    (fun x hx => ?_) (fun A _ => ?_) (fun x hx => ?_) fun A _ => ?_
  · rw [mem_product, mem_powerset, mem_powerset]
    exact ⟨inter_subset_right, sdiff_subset_sdiff (mem_powerset.mp hA) (Subset.refl T)⟩
  · rw [mem_product, mem_powerset, mem_powerset] at hx
    exact mem_powerset.mpr (union_subset (hx.1.trans hT) (hx.2.trans sdiff_subset))
  · rw [union_comm, sdiff_union_inter]
  · rw [mem_product, mem_powerset, mem_powerset] at hx
    have hdisj : Disjoint x.1 x.2 :=
      disjoint_of_subset_left hx.1 (disjoint_of_subset_right hx.2 disjoint_sdiff)
    ext1
    · simp only
      rw [union_inter_distrib_right, inter_eq_left.mpr hx.1,
        disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_right hx.2 disjoint_sdiff).symm,
        union_empty]
    · simp only
      rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr hx.1, empty_union,
        sdiff_eq_self_of_disjoint (disjoint_of_subset_left hx.2 disjoint_sdiff_self_left)]
  · simp only
    rw [union_comm, sdiff_union_inter]
end Finset
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution {T T' : Finset α} (hT : T ⊆ U) (hT' : T' ⊆ U) (hTT' : Disjoint T T')
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q] (hP : DependsOnCoords P T)
    (hQ : DependsOnCoords Q T') :
    U.bernoulliProb p (fun A => P A ∧ Q A) = U.bernoulliProb p P * U.bernoulliProb p Q := by
  have hT'U : T' ⊆ U \ T := fun x hx => mem_sdiff.mpr ⟨hT' hx, disjoint_right.mp hTT' hx⟩
  -- on `a ∪ b` with `a ⊆ T` and `b ⊆ U \ T`, `P` sees only `a` and `Q` only `b`
  have hPa : ∀ a ⊆ T, ∀ b ⊆ U \ T, (P (a ∪ b) ↔ P a) := fun a ha b hb => hP _ _ (by
    rw [union_inter_distrib_right, inter_eq_left.mpr ha,
      disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hb disjoint_sdiff_self_left),
      union_empty])
  have hQb : ∀ a ⊆ T, ∀ b ⊆ U \ T, (Q (a ∪ b) ↔ Q b) := fun a ha b hb => hQ _ _ (by
    rw [union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left ha hTT'), empty_union])
  have hsplit : ∀ R : Finset α → Prop, [DecidablePred R] →
      U.bernoulliProb p R = ∑ a ∈ T.powerset, ∑ b ∈ (U \ T).powerset,
        if R (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0 := by
    intro R _
    rw [bernoulliProb, sum_filter, sum_powerset_split hT]
    refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    rw [bernoulliWeight_union hT (mem_powerset.mp ha) (mem_powerset.mp hb)]
  rw [hsplit, hsplit P, hsplit Q]
  have e1 : ∀ a ∈ T.powerset, ∀ b ∈ (U \ T).powerset,
      (if P (a ∪ b) ∧ Q (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0) =
        (if P a then T.bernoulliWeight p a else 0) *
          (if Q b then (U \ T).bernoulliWeight p b else 0) := fun a ha b hb => by
    have h1 := hPa a (mem_powerset.mp ha) b (mem_powerset.mp hb)
    have h2 := hQb a (mem_powerset.mp ha) b (mem_powerset.mp hb)
    by_cases hp : P a <;> by_cases hq : Q b <;> simp [h1, h2, hp, hq]
  have e2 : ∀ a ∈ T.powerset, ∀ b ∈ (U \ T).powerset,
      (if P (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0) =
        (if P a then T.bernoulliWeight p a else 0) * (U \ T).bernoulliWeight p b :=
    fun a ha b hb => by
      have h1 := hPa a (mem_powerset.mp ha) b (mem_powerset.mp hb)
      by_cases hp : P a <;> simp [h1, hp]
  have e3 : ∀ a ∈ T.powerset, ∀ b ∈ (U \ T).powerset,
      (if Q (a ∪ b) then T.bernoulliWeight p a * (U \ T).bernoulliWeight p b else 0) =
        T.bernoulliWeight p a * (if Q b then (U \ T).bernoulliWeight p b else 0) :=
    fun a ha b hb => by
      have h2 := hQb a (mem_powerset.mp ha) b (mem_powerset.mp hb)
      by_cases hq : Q b <;> simp [h2, hq]
  rw [sum_congr rfl fun a ha => sum_congr rfl (e1 a ha), sum_congr rfl fun a ha =>
    sum_congr rfl (e2 a ha), sum_congr rfl fun a ha => sum_congr rfl (e3 a ha)]
  simp_rw [← mul_sum, ← sum_mul, sum_bernoulliWeight, mul_one, one_mul]
end Finset
