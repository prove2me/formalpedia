-- Prove2me | solution 1 for Conway99.edge_local_C4_or_C8_forces_indep_14
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-27T18:31:01.762986+00:00
-- url     : https://prove2.me/submissions/15be4161-c28a-4023-9d4b-b37c045f39f5

import Mathlib
open Finset SimpleGraph

namespace Conway99Helpers
open Finset

def F (q s t : ℤ) : ℤ := 6 * (q - 1) ^ 2 + 6 - 3 * (s ^ 2 + t ^ 2)

lemma F_linear (q s t : ℤ) :
    F q s t = 6 * q ^ 2 - 12 * q + 12 - 3 * s ^ 2 - 3 * t ^ 2 := by
  simp only [F]; ring

lemma sum_F {V : Type*} [DecidableEq V] (R : Finset V) (q s t : V → ℤ) :
    ∑ v ∈ R, F (q v) (s v) (t v) =
      6 * ∑ v ∈ R, (q v) ^ 2 - 12 * ∑ v ∈ R, q v + 12 * (#R : ℤ) -
        3 * ∑ v ∈ R, (s v) ^ 2 - 3 * ∑ v ∈ R, (t v) ^ 2 := by
  have hpt : ∀ v ∈ R,
      F (q v) (s v) (t v) =
        6 * (q v) ^ 2 - 12 * q v + 12 - 3 * (s v) ^ 2 - 3 * (t v) ^ 2 :=
    fun v _ => F_linear _ _ _
  rw [sum_congr rfl hpt]
  have e1 : ∑ v ∈ R, (6 * (q v) ^ 2) = 6 * ∑ v ∈ R, (q v) ^ 2 := (mul_sum R _ 6).symm
  have e2 : ∑ v ∈ R, (12 * q v) = 12 * ∑ v ∈ R, q v := (mul_sum R _ 12).symm
  have e3 : ∑ v ∈ R, (3 * (s v) ^ 2) = 3 * ∑ v ∈ R, (s v) ^ 2 := (mul_sum R _ 3).symm
  have e4 : ∑ v ∈ R, (3 * (t v) ^ 2) = 3 * ∑ v ∈ R, (t v) ^ 2 := (mul_sum R _ 3).symm
  have e5 : ∑ v ∈ R, (12 : ℤ) = 12 * (#R : ℤ) := by simp [sum_const]; ring
  calc ∑ v ∈ R, (6 * (q v) ^ 2 - 12 * q v + 12 - 3 * (s v) ^ 2 - 3 * (t v) ^ 2)
      = ∑ v ∈ R, (6 * (q v) ^ 2) + ∑ v ∈ R, (-(12 * q v)) + ∑ v ∈ R, (12 : ℤ) +
          ∑ v ∈ R, (-(3 * (s v) ^ 2)) + ∑ v ∈ R, (-(3 * (t v) ^ 2)) := by
            simp [sub_eq_add_neg, sum_add_distrib]
    _ = 6 * ∑ v ∈ R, (q v) ^ 2 + (-(12 * ∑ v ∈ R, q v)) + 12 * (#R : ℤ) +
          (-(3 * ∑ v ∈ R, (s v) ^ 2)) + (-(3 * ∑ v ∈ R, (t v) ^ 2)) := by
            simp only [sum_neg_distrib, e1, e2, e3, e4, e5]
    _ = 6 * ∑ v ∈ R, (q v) ^ 2 - 12 * ∑ v ∈ R, q v + 12 * (#R : ℤ) -
          3 * ∑ v ∈ R, (s v) ^ 2 - 3 * ∑ v ∈ R, (t v) ^ 2 := by
            ring

lemma sum_F_id {V : Type*} [DecidableEq V]
    (R : Finset V) (m : ℕ) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1)) :
    ∑ v ∈ R, F (q v) (s v) (t v) =
      48 * (3 * (m : ℤ) ^ 2 - 8 * (m : ℤ) + 3) := by
  rw [sum_F R q s t, hs2, ht2, hq, hq2, hR]; ring

lemma sum_F_neg {V : Type*} [DecidableEq V]
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1)) :
    ∑ v ∈ R, F (q v) (s v) (t v) < 0 := by
  rw [sum_F_id R m q s t hR hs2 ht2 hq hq2]
  rcases hm with rfl | rfl <;> norm_num

lemma contradiction {V : Type*} [DecidableEq V]
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (hF : ∀ v ∈ R, (0 : ℤ) ≤ F (q v) (s v) (t v)) :
    False := by
  have hneg := sum_F_neg R m hm q s t hR hs2 ht2 hq hq2
  have hnonneg : (0 : ℤ) ≤ ∑ v ∈ R, F (q v) (s v) (t v) :=
    sum_nonneg fun v hv => hF v hv
  exact (not_le_of_gt hneg) hnonneg

lemma extending_bound {V : Type*} [DecidableEq V]
    (R Z : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (extV : V → Prop) [DecidablePred extV]
    (hZR : Z ⊆ R) (_hZcard : #Z = 12) (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (hFZ : ∀ v ∈ Z, (0 : ℤ) ≤ F (q v) (s v) (t v))
    (hFWnon : ∀ v ∈ R \ Z, ¬ extV v → (0 : ℤ) ≤ F (q v) (s v) (t v))
    (hFWlow : ∀ v ∈ R \ Z, (-36 : ℤ) ≤ F (q v) (s v) (t v)) :
    (m = 1 → 3 ≤ #{v ∈ R \ Z | extV v}) ∧
      (m = 2 → 2 ≤ #{v ∈ R \ Z | extV v}) := by
  set W := R \ Z
  set E := filter extV W
  set N := filter (fun v => ¬ extV v) W
  have hsumEq := sum_F_id R m q s t hR hs2 ht2 hq hq2
  have hsplit : R = Z ∪ W := by
    ext v; constructor
    · intro hv; by_cases hz : v ∈ Z
      · exact mem_union_left _ hz
      · exact mem_union_right _ (mem_sdiff.2 ⟨hv, hz⟩)
    · intro hv; rw [mem_union] at hv
      rcases hv with hz | hw
      · exact hZR hz
      · exact (mem_sdiff.1 hw).1
  have hZW : Disjoint Z W := disjoint_sdiff
  have hEN : E ∪ N = W := by
    ext v; constructor
    · intro hv
      rw [mem_union, mem_filter, mem_filter] at hv
      rcases hv with h | h <;> exact h.1
    · intro hv; by_cases he : extV v
      · exact mem_union_left _ (mem_filter.2 ⟨hv, he⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hv, he⟩)
  have hdisj : Disjoint E N := by
    refine disjoint_left.2 fun v hvE hvN => ?_
    rw [mem_filter] at hvE hvN
    exact hvN.2 hvE.2
  have hsumsplit :
      ∑ v ∈ R, F (q v) (s v) (t v) =
        ∑ v ∈ Z, F (q v) (s v) (t v) +
          ∑ v ∈ E, F (q v) (s v) (t v) +
          ∑ v ∈ N, F (q v) (s v) (t v) := by
    have h1 : ∑ v ∈ R, F (q v) (s v) (t v) =
        ∑ v ∈ Z, F (q v) (s v) (t v) + ∑ v ∈ W, F (q v) (s v) (t v) := by
      rw [hsplit, sum_union hZW]
    rw [h1, ← hEN, sum_union hdisj, add_assoc]
  have hZge : (0 : ℤ) ≤ ∑ v ∈ Z, F (q v) (s v) (t v) :=
    sum_nonneg fun v hv => hFZ v hv
  have hNge : (0 : ℤ) ≤ ∑ v ∈ N, F (q v) (s v) (t v) := by
    refine sum_nonneg fun v hv => ?_
    have hvN : v ∈ W ∧ ¬ extV v := mem_filter.1 hv
    exact hFWnon v hvN.1 hvN.2
  have hElow : (-36 : ℤ) * (#E : ℤ) ≤ ∑ v ∈ E, F (q v) (s v) (t v) := by
    have hpt : ∀ v ∈ E, (-36 : ℤ) ≤ F (q v) (s v) (t v) := fun v hv =>
      hFWlow v (mem_filter.1 hv).1
    calc (-36 : ℤ) * (#E : ℤ)
        = ∑ _v ∈ E, (-36 : ℤ) := by simp [sum_const, mul_comm]
      _ ≤ _ := sum_le_sum hpt
  have hlower : (-36 : ℤ) * (#E : ℤ) ≤ ∑ v ∈ R, F (q v) (s v) (t v) := by
    rw [hsumsplit]; linarith
  rw [hsumEq] at hlower
  constructor
  · intro hm1; subst hm1
    have hnum : (-36 : ℤ) * (#E : ℤ) ≤ -96 := by convert hlower using 1; norm_num
    have : (3 : ℤ) ≤ (#E : ℤ) := by linarith
    exact_mod_cast this
  · intro hm2; subst hm2
    have hnum : (-36 : ℤ) * (#E : ℤ) ≤ -48 := by convert hlower using 1; norm_num
    have : (2 : ℤ) ≤ (#E : ℤ) := by linarith
    exact_mod_cast this

lemma forces_extension {V : Type*} [DecidableEq V]
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (extV : V → Prop) [DecidablePred extV]
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (hFnon : ∀ v ∈ R, ¬ extV v → (0 : ℤ) ≤ F (q v) (s v) (t v)) :
    ∃ v ∈ R, extV v := by
  by_contra hnone
  have hnone' : ∀ v ∈ R, ¬ extV v := fun v hv he => hnone ⟨v, hv, he⟩
  exact contradiction R m hm q s t hR hs2 ht2 hq hq2
    fun v hv => hFnon v hv (hnone' v hv)

end Conway99Helpers

namespace Conway99

theorem edge_local_C4_or_C8_forces_indep_14 {V : Type*}
    [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj]
    (_hSRG : g.IsSRGWith 99 14 1 2)
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (K : Bool → Bool → Finset V)
    (_hK : ∀ ε η, g.IsNIndepSet 13 (K ε η))
    (extV : V → Prop) [DecidablePred extV]
    (hFnon : ∀ v ∈ R, ¬ extV v →
      (0 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2))
    (hExt : ∀ v ∈ R, extV v → ∃ ε η, g.IsNIndepSet 14 (insert v (K ε η))) :
    ∃ s : Finset V, g.IsNIndepSet 14 s := by
  have hFnon' : ∀ v ∈ R, ¬ extV v → (0 : ℤ) ≤ Conway99Helpers.F (q v) (s v) (t v) := by
    intro v hv hne; simpa [Conway99Helpers.F] using hFnon v hv hne
  obtain ⟨v, hvR, hvExt⟩ :=
    Conway99Helpers.forces_extension R m hm q s t extV hR hs2 ht2 hq hq2 hFnon'
  obtain ⟨ε, η, h14⟩ := hExt v hvR hvExt
  exact ⟨insert v (K ε η), h14⟩

end Conway99

open Finset SimpleGraph

theorem solution {V : Type*}
    [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj]
    (_hSRG : g.IsSRGWith 99 14 1 2)
    (R : Finset V) (m : ℕ) (hm : m = 1 ∨ m = 2) (q s t : V → ℤ)
    (hR : #R = 72)
    (hs2 : ∑ v ∈ R, (s v) ^ 2 = (40 : ℤ) * m)
    (ht2 : ∑ v ∈ R, (t v) ^ 2 = (40 : ℤ) * (6 - m))
    (hq : ∑ v ∈ R, q v = (44 : ℤ) * m)
    (hq2 : ∑ v ∈ R, (q v) ^ 2 = (24 : ℤ) * m * (m + 1))
    (K : Bool → Bool → Finset V)
    (_hK : ∀ ε η, g.IsNIndepSet 13 (K ε η))
    (extV : V → Prop) [DecidablePred extV]
    (hFnon : ∀ v ∈ R, ¬ extV v →
      (0 : ℤ) ≤ 6 * ((q v) - 1) ^ 2 + 6 - 3 * ((s v) ^ 2 + (t v) ^ 2))
    (hExt : ∀ v ∈ R, extV v → ∃ ε η, g.IsNIndepSet 14 (insert v (K ε η))) :
    ∃ s : Finset V, g.IsNIndepSet 14 s :=
  Conway99.edge_local_C4_or_C8_forces_indep_14 _hSRG R m hm q s t hR hs2 ht2 hq hq2
    K _hK extV hFnon hExt
