-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.mconvex_intersection_hull
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:12:23.094998+00:00
-- url     : https://prove2.me/submissions/cfaf863b-520e-4d98-852e-7b7fa5e52c4c

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts

open scoped Pointwise

namespace DiscreteConvex.MConvexSetsB
namespace MK

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### WithTop helpers -/

lemma coe_untopD (t : WithTop ℝ) (h : t ≠ ⊤) : ((WithTop.untopD 0 t : ℝ) : WithTop ℝ) = t := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
  rw [← hr, WithTop.untopD_coe]

lemma coe_le_add_coe_iff (a b : ℝ) (t : WithTop ℝ) :
    ((a : WithTop ℝ) ≤ t + (b : WithTop ℝ)) ↔ ((a - b : ℝ) : WithTop ℝ) ≤ t := by
  cases t with
  | top => simp
  | coe s =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

lemma coe_le_coe_add_iff (a b : ℝ) (t : WithTop ℝ) :
    ((a : WithTop ℝ) ≤ (b : WithTop ℝ) + t) ↔ ((a - b : ℝ) : WithTop ℝ) ≤ t := by
  rw [add_comm]; exact coe_le_add_coe_iff a b t

lemma int_of_ne_top (ρ : Finset V → WithTop ℝ) (hI : IsIntegerValued ρ) (X : Finset V)
    (h : ρ X ≠ ⊤) : ∃ k : ℤ, WithTop.untopD 0 (ρ X) = (k : ℝ) := by
  rcases hI X with h' | ⟨k, hk⟩
  · exact absurd h' h
  · exact ⟨k, by rw [hk, WithTop.untopD_coe]⟩

lemma wt_rearr (a b : ℝ) (t u : WithTop ℝ) :
    ((a : WithTop ℝ) + t) + ((b : WithTop ℝ) + u) = ((a + b : ℝ) : WithTop ℝ) + (t + u) := by
  rw [WithTop.coe_add]; ac_rfl

/-! ### the reduced set function -/

/-- the reduced set function after fixing `x s = α` -/
noncomputable def red (ρ : Finset V → WithTop ℝ) (s : V) (α : ℝ) : Finset V → WithTop ℝ :=
  fun X => min (ρ X) (ρ (insert s X) + ((-α : ℝ) : WithTop ℝ))

lemma red_le_left (ρ : Finset V → WithTop ℝ) (s : V) (α : ℝ) (X : Finset V) :
    red ρ s α X ≤ ρ X := min_le_left _ _

lemma red_le_right (ρ : Finset V → WithTop ℝ) (s : V) (α : ℝ) (X : Finset V) :
    red ρ s α X ≤ ρ (insert s X) + ((-α : ℝ) : WithTop ℝ) := min_le_right _ _

lemma red_int (ρ : Finset V → WithTop ℝ) (hI : IsIntegerValued ρ) (s : V) (k : ℤ) :
    IsIntegerValued (red ρ s k) := by
  intro X
  rcases min_choice (ρ X) (ρ (insert s X) + ((-(k : ℝ) : ℝ) : WithTop ℝ)) with h | h
  · unfold red; rw [h]; exact hI X
  · unfold red; rw [h]
    rcases hI (insert s X) with ht | ⟨m, hm⟩
    · left; rw [ht, WithTop.top_add]
    · right
      refine ⟨m - k, ?_⟩
      rw [hm, ← WithTop.coe_add]
      congr 1; push_cast; ring

lemma red_submod (ρ : Finset V → WithTop ℝ) (S' : Finset V) (s : V) (hs : s ∉ S') (α : ℝ)
    (hsub : ∀ X Y, X ⊆ insert s S' → Y ⊆ insert s S' →
      ρ (X ∪ Y) + ρ (X ∩ Y) ≤ ρ X + ρ Y) :
    ∀ X Y, X ⊆ S' → Y ⊆ S' →
      red ρ s α (X ∪ Y) + red ρ s α (X ∩ Y) ≤ red ρ s α X + red ρ s α Y := by
  intro X Y hX hY
  have hsX : s ∉ X := fun h => hs (hX h)
  have hsY : s ∉ Y := fun h => hs (hY h)
  have hXS : X ⊆ insert s S' := hX.trans (Finset.subset_insert _ _)
  have hYS : Y ⊆ insert s S' := hY.trans (Finset.subset_insert _ _)
  have hsXS : insert s X ⊆ insert s S' := Finset.insert_subset_insert _ hX
  have hsYS : insert s Y ⊆ insert s S' := Finset.insert_subset_insert _ hY
  have e1 : X ∪ insert s Y = insert s (X ∪ Y) := by
    ext w; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  have e2 : X ∩ insert s Y = X ∩ Y := by
    ext w; simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd (h2 ▸ h1) hsX
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
  have e3 : insert s X ∪ Y = insert s (X ∪ Y) := by
    ext w; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  have e4 : insert s X ∩ Y = X ∩ Y := by
    ext w; simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ h2) hsY
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
  have e5 : insert s X ∪ insert s Y = insert s (X ∪ Y) := by
    ext w; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  have e6 : insert s X ∩ insert s Y = insert s (X ∩ Y) := by
    ext w; simp only [Finset.mem_inter, Finset.mem_insert]; tauto
  have hU1 : red ρ s α (X ∪ Y) ≤ ρ (X ∪ Y) := red_le_left _ _ _ _
  have hU2 : red ρ s α (X ∪ Y) ≤ ρ (insert s (X ∪ Y)) + ((-α : ℝ) : WithTop ℝ) :=
    red_le_right _ _ _ _
  have hI1 : red ρ s α (X ∩ Y) ≤ ρ (X ∩ Y) := red_le_left _ _ _ _
  have hI2 : red ρ s α (X ∩ Y) ≤ ρ (insert s (X ∩ Y)) + ((-α : ℝ) : WithTop ℝ) :=
    red_le_right _ _ _ _
  rcases min_choice (ρ X) (ρ (insert s X) + ((-α : ℝ) : WithTop ℝ)) with h1 | h1 <;>
  rcases min_choice (ρ Y) (ρ (insert s Y) + ((-α : ℝ) : WithTop ℝ)) with h2 | h2 <;>
  simp only [red] <;> rw [h1, h2]
  · exact (add_le_add hU1 hI1).trans (hsub X Y hXS hYS)
  · calc _ ≤ (ρ (insert s (X ∪ Y)) + ((-α : ℝ) : WithTop ℝ)) + ρ (X ∩ Y) := add_le_add hU2 hI1
      _ = ρ (X ∪ insert s Y) + ρ (X ∩ insert s Y) + ((-α : ℝ) : WithTop ℝ) := by
          rw [e1, e2]; ac_rfl
      _ ≤ ρ X + ρ (insert s Y) + ((-α : ℝ) : WithTop ℝ) :=
          add_le_add (hsub X (insert s Y) hXS hsYS) le_rfl
      _ = _ := by ac_rfl
  · calc _ ≤ (ρ (insert s (X ∪ Y)) + ((-α : ℝ) : WithTop ℝ)) + ρ (X ∩ Y) := add_le_add hU2 hI1
      _ = ρ (insert s X ∪ Y) + ρ (insert s X ∩ Y) + ((-α : ℝ) : WithTop ℝ) := by
          rw [e3, e4]; ac_rfl
      _ ≤ ρ (insert s X) + ρ Y + ((-α : ℝ) : WithTop ℝ) :=
          add_le_add (hsub (insert s X) Y hsXS hYS) le_rfl
      _ = _ := by ac_rfl
  · calc _ ≤ (ρ (insert s (X ∪ Y)) + ((-α : ℝ) : WithTop ℝ)) +
          (ρ (insert s (X ∩ Y)) + ((-α : ℝ) : WithTop ℝ)) := add_le_add hU2 hI2
      _ = ρ (insert s X ∪ insert s Y) + ρ (insert s X ∩ insert s Y) +
          (((-α : ℝ) : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ)) := by
          rw [e5, e6]; ac_rfl
      _ ≤ ρ (insert s X) + ρ (insert s Y) + (((-α : ℝ) : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ)) :=
          add_le_add (hsub (insert s X) (insert s Y) hsXS hsYS) le_rfl
      _ = _ := by ac_rfl

/-! ### the intersection theorem -/

structure Good (S : Finset V) (ρ1 ρ2 : Finset V → WithTop ℝ) : Prop where
  z1 : ρ1 ∅ = 0
  z2 : ρ2 ∅ = 0
  sub1 : ∀ X Y, X ⊆ S → Y ⊆ S → ρ1 (X ∪ Y) + ρ1 (X ∩ Y) ≤ ρ1 X + ρ1 Y
  sub2 : ∀ X Y, X ⊆ S → Y ⊆ S → ρ2 (X ∪ Y) + ρ2 (X ∩ Y) ≤ ρ2 X + ρ2 Y
  fin : ρ1 S ≠ ⊤
  eq : ρ1 S = ρ2 S
  cross : ∀ X ⊆ S, ρ1 S ≤ ρ1 X + ρ2 (S \ X)

lemma sum_shift (x' : V → ℝ) (s : V) (α : ℝ) (X : Finset V) :
    ∑ v ∈ X, (x' v + if v = s then α else 0) = ∑ v ∈ X, x' v + if s ∈ X then α else 0 := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']

theorem inter_core (S : Finset V) : ∀ (ρ1 ρ2 : Finset V → WithTop ℝ), Good S ρ1 ρ2 →
    ∃ x : V → ℝ, (∀ X ⊆ S, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ1 X) ∧
      (∀ X ⊆ S, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ2 X) ∧
      ((∑ v ∈ S, x v : ℝ) : WithTop ℝ) = ρ1 S ∧ (∀ v, v ∉ S → x v = 0) ∧
      (IsIntegerValued ρ1 → IsIntegerValued ρ2 → ∀ v, ∃ k : ℤ, x v = k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro ρ1 ρ2 hG
    refine ⟨fun _ => 0, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ v => ⟨0, by simp⟩⟩
    · intro X hX
      rw [Finset.subset_empty.mp hX, hG.z1]; simp
    · intro X hX
      rw [Finset.subset_empty.mp hX, hG.z2]; simp
    · rw [hG.z1]; simp
  | insert s S' hs ih =>
    intro ρ1 ρ2 hG
    set T := insert s S' with hT
    have hsT : s ∈ T := Finset.mem_insert_self _ _
    have hS'T : S' ⊆ T := Finset.subset_insert _ _
    -- the finite value of `ρ1 T`
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hG.fin
    replace hr : ρ1 T = (r : WithTop ℝ) := hr.symm
    have hr2 : ρ2 T = (r : WithTop ℝ) := by rw [← hG.eq, hr]
    -- set identities
    have hTS' : T \ S' = {s} := by
      ext w; simp only [Finset.mem_sdiff, hT, Finset.mem_insert, Finset.mem_singleton]
      have hws : w = s → w ∉ S' := fun h => h ▸ hs
      tauto
    have hins_sdiff : ∀ X, X ⊆ S' → T \ X = insert s (S' \ X) := by
      intro X hX
      ext w; simp only [Finset.mem_sdiff, hT, Finset.mem_insert]
      have hwsX : w = s → w ∉ X := fun h hw => hs (h ▸ hX hw)
      tauto
    have hsdiff_ins : ∀ X, X ⊆ S' → S' \ X = T \ insert s X := by
      intro X hX
      ext w; simp only [Finset.mem_sdiff, hT, Finset.mem_insert]
      have hws : w = s → w ∉ S' := fun h => h ▸ hs
      tauto
    -- the lower and upper bounds on `α`
    set Lset : Finset ℝ := (S'.powerset.filter (fun X => ρ1 X ≠ ⊤ ∧ ρ2 (S' \ X) ≠ ⊤)).image
      (fun X => r - WithTop.untopD 0 (ρ1 X) - WithTop.untopD 0 (ρ2 (S' \ X))) with hLset
    set Uset : Finset ℝ := (S'.powerset.filter (fun Y => ρ1 (insert s Y) ≠ ⊤ ∧ ρ2 (T \ Y) ≠ ⊤)).image
      (fun Y => WithTop.untopD 0 (ρ1 (insert s Y)) + WithTop.untopD 0 (ρ2 (T \ Y)) - r) with hUset
    have hLU : ∀ l ∈ Lset, ∀ u ∈ Uset, l ≤ u := by
      intro l hl u hu
      rw [hLset, Finset.mem_image] at hl
      rw [hUset, Finset.mem_image] at hu
      obtain ⟨X, hX, rfl⟩ := hl
      obtain ⟨Y, hY, rfl⟩ := hu
      rw [Finset.mem_filter, Finset.mem_powerset] at hX hY
      obtain ⟨hXS, hX1, hX2⟩ := hX
      obtain ⟨hYS, hY1, hY2⟩ := hY
      have hsX : s ∉ X := fun h => hs (hXS h)
      have hsY : s ∉ Y := fun h => hs (hYS h)
      have e1 : X ∪ insert s Y = insert s (X ∪ Y) := by
        ext w; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have e2 : X ∩ insert s Y = X ∩ Y := by
        ext w; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2 | h2⟩
          · exact absurd (h2 ▸ h1) hsX
          · exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
      have e3 : (S' \ X) ∪ (T \ Y) = T \ (X ∩ Y) := by
        ext w; simp only [Finset.mem_union, Finset.mem_sdiff, hT, Finset.mem_insert, Finset.mem_inter]
        have hwsX : w = s → w ∉ X := fun h hw => hs (h ▸ hXS hw)
        have hwsY : w = s → w ∉ Y := fun h hw => hs (h ▸ hYS hw)
        tauto
      have e4 : (S' \ X) ∩ (T \ Y) = T \ insert s (X ∪ Y) := by
        ext w; simp only [Finset.mem_inter, Finset.mem_sdiff, hT, Finset.mem_insert, Finset.mem_union]
        have hws : w = s → w ∉ S' := fun h => h ▸ hs
        tauto
      have c1 := hG.sub1 X (insert s Y) (hXS.trans hS'T) (Finset.insert_subset hsT (hYS.trans hS'T))
      rw [e1, e2] at c1
      have c2 := hG.sub2 (S' \ X) (T \ Y) ((Finset.sdiff_subset).trans hS'T) Finset.sdiff_subset
      rw [e3, e4] at c2
      have c3 := hG.cross (insert s (X ∪ Y)) (Finset.insert_subset hsT ((Finset.union_subset hXS hYS).trans hS'T))
      have c4 := hG.cross (X ∩ Y) ((Finset.inter_subset_left).trans (hXS.trans hS'T))
      have big : ρ1 T + ρ1 T ≤ (ρ1 X + ρ1 (insert s Y)) + (ρ2 (S' \ X) + ρ2 (T \ Y)) := by
        calc ρ1 T + ρ1 T ≤ (ρ1 (insert s (X ∪ Y)) + ρ2 (T \ insert s (X ∪ Y))) +
              (ρ1 (X ∩ Y) + ρ2 (T \ (X ∩ Y))) := add_le_add c3 c4
          _ = (ρ1 (insert s (X ∪ Y)) + ρ1 (X ∩ Y)) +
              (ρ2 (T \ (X ∩ Y)) + ρ2 (T \ insert s (X ∪ Y))) := by ac_rfl
          _ ≤ _ := add_le_add c1 c2
      rw [hr, ← coe_untopD _ hX1, ← coe_untopD _ hX2, ← coe_untopD _ hY1, ← coe_untopD _ hY2,
        ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_le_coe] at big
      linarith
    have hLint : IsIntegerValued ρ1 → IsIntegerValued ρ2 → ∀ l ∈ Lset, ∃ k : ℤ, l = k := by
      intro hI1 hI2 l hl
      rw [hLset, Finset.mem_image] at hl
      obtain ⟨X, hX, rfl⟩ := hl
      rw [Finset.mem_filter] at hX
      obtain ⟨k1, hk1⟩ := int_of_ne_top ρ1 hI1 X hX.2.1
      obtain ⟨k2, hk2⟩ := int_of_ne_top ρ2 hI2 _ hX.2.2
      obtain ⟨k0, hk0⟩ := int_of_ne_top ρ1 hI1 T hG.fin
      have : r = WithTop.untopD 0 (ρ1 T) := by rw [hr, WithTop.untopD_coe]
      refine ⟨k0 - k1 - k2, ?_⟩
      rw [this, hk0, hk1, hk2]; push_cast; ring
    have hUint : IsIntegerValued ρ1 → IsIntegerValued ρ2 → ∀ u ∈ Uset, ∃ k : ℤ, u = k := by
      intro hI1 hI2 u hu
      rw [hUset, Finset.mem_image] at hu
      obtain ⟨Y, hY, rfl⟩ := hu
      rw [Finset.mem_filter] at hY
      obtain ⟨k1, hk1⟩ := int_of_ne_top ρ1 hI1 _ hY.2.1
      obtain ⟨k2, hk2⟩ := int_of_ne_top ρ2 hI2 _ hY.2.2
      obtain ⟨k0, hk0⟩ := int_of_ne_top ρ1 hI1 T hG.fin
      have : r = WithTop.untopD 0 (ρ1 T) := by rw [hr, WithTop.untopD_coe]
      refine ⟨k1 + k2 - k0, ?_⟩
      rw [this, hk0, hk1, hk2]; push_cast; ring
    -- choose α
    obtain ⟨α, hαL, hαU, hαint⟩ : ∃ α : ℝ, (∀ l ∈ Lset, l ≤ α) ∧ (∀ u ∈ Uset, α ≤ u) ∧
        (IsIntegerValued ρ1 → IsIntegerValued ρ2 → ∃ k : ℤ, α = k) := by
      by_cases hL : Lset.Nonempty
      · refine ⟨Lset.max' hL, fun l hl => Finset.le_max' _ _ hl, fun u hu => hLU _ (Finset.max'_mem _ _) u hu,
          fun hI1 hI2 => hLint hI1 hI2 _ (Finset.max'_mem _ _)⟩
      · by_cases hU : Uset.Nonempty
        · refine ⟨Uset.min' hU, fun l hl => absurd ⟨l, hl⟩ hL, fun u hu => Finset.min'_le _ _ hu,
            fun hI1 hI2 => hUint hI1 hI2 _ (Finset.min'_mem _ _)⟩
        · exact ⟨0, fun l hl => absurd ⟨l, hl⟩ hL, fun u hu => absurd ⟨u, hu⟩ hU, fun _ _ => ⟨0, by simp⟩⟩
    have P1 : ∀ X ⊆ S', ρ1 T ≤ (α : WithTop ℝ) + ρ1 X + ρ2 (S' \ X) := by
      intro X hX
      by_cases h1 : ρ1 X = ⊤
      · rw [h1, WithTop.add_top, WithTop.top_add]; exact le_top
      by_cases h2 : ρ2 (S' \ X) = ⊤
      · rw [h2, WithTop.add_top]; exact le_top
      have hmem : r - WithTop.untopD 0 (ρ1 X) - WithTop.untopD 0 (ρ2 (S' \ X)) ∈ Lset := by
        rw [hLset, Finset.mem_image]
        exact ⟨X, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hX, h1, h2⟩, rfl⟩
      have := hαL _ hmem
      rw [hr, ← coe_untopD _ h1, ← coe_untopD _ h2, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_le_coe]
      linarith
    have P2 : ∀ Y ⊆ S', (α : WithTop ℝ) + ρ1 T ≤ ρ1 (insert s Y) + ρ2 (T \ Y) := by
      intro Y hY
      by_cases h1 : ρ1 (insert s Y) = ⊤
      · rw [h1, WithTop.top_add]; exact le_top
      by_cases h2 : ρ2 (T \ Y) = ⊤
      · rw [h2, WithTop.add_top]; exact le_top
      have hmem : WithTop.untopD 0 (ρ1 (insert s Y)) + WithTop.untopD 0 (ρ2 (T \ Y)) - r ∈ Uset := by
        rw [hUset, Finset.mem_image]
        exact ⟨Y, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hY, h1, h2⟩, rfl⟩
      have := hαU _ hmem
      rw [hr, ← coe_untopD _ h1, ← coe_untopD _ h2, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_le_coe]
      linarith
    -- consequences
    have hα1 : (α : WithTop ℝ) ≤ ρ1 {s} := by
      have := P2 ∅ (Finset.empty_subset _)
      rw [Finset.insert_empty, Finset.sdiff_empty, hr2, hr] at this
      exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
    have hα2 : (α : WithTop ℝ) ≤ ρ2 {s} := by
      have := P2 S' (le_refl _)
      rw [hTS', ← hT, hr, add_comm (α : WithTop ℝ)] at this
      exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp this
    have hred1S : red ρ1 s α S' = ((r - α : ℝ) : WithTop ℝ) := by
      have := P1 S' (le_refl _)
      rw [Finset.sdiff_self, hG.z2, add_zero, hr, coe_le_coe_add_iff] at this
      have e : ((r - α : ℝ) : WithTop ℝ) = ρ1 T + ((-α : ℝ) : WithTop ℝ) := by
        rw [hr, ← WithTop.coe_add, sub_eq_add_neg]
      unfold red
      rw [← hT, ← e]
      exact min_eq_right this
    have hred2S : red ρ2 s α S' = ((r - α : ℝ) : WithTop ℝ) := by
      have := P1 ∅ (Finset.empty_subset _)
      rw [Finset.sdiff_empty, hG.z1, add_zero, hr, coe_le_coe_add_iff] at this
      have e : ((r - α : ℝ) : WithTop ℝ) = ρ2 T + ((-α : ℝ) : WithTop ℝ) := by
        rw [hr2, ← WithTop.coe_add, sub_eq_add_neg]
      unfold red
      rw [← hT, ← e]
      exact min_eq_right this
    have hG' : Good S' (red ρ1 s α) (red ρ2 s α) := by
      refine ⟨?_, ?_, red_submod ρ1 S' s hs α hG.sub1, red_submod ρ2 S' s hs α hG.sub2, ?_, ?_, ?_⟩
      · unfold red
        rw [Finset.insert_empty, hG.z1]
        apply min_eq_left
        cases h : ρ1 {s} with
        | top => simp
        | coe q =>
          rw [h] at hα1
          rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
          have := WithTop.coe_le_coe.mp hα1; linarith
      · unfold red
        rw [Finset.insert_empty, hG.z2]
        apply min_eq_left
        cases h : ρ2 {s} with
        | top => simp
        | coe q =>
          rw [h] at hα2
          rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
          have := WithTop.coe_le_coe.mp hα2; linarith
      · rw [hred1S]; exact WithTop.coe_ne_top
      · rw [hred1S, hred2S]
      · intro X hX
        rw [hred1S]
        have hsX : s ∉ X := fun h => hs (hX h)
        have hXT : X ⊆ T := hX.trans hS'T
        rcases min_choice (ρ1 X) (ρ1 (insert s X) + ((-α : ℝ) : WithTop ℝ)) with h1 | h1 <;>
        rcases min_choice (ρ2 (S' \ X)) (ρ2 (insert s (S' \ X)) + ((-α : ℝ) : WithTop ℝ)) with h2 | h2 <;>
        unfold red <;> rw [h1, h2]
        · have := P1 X hX
          rw [hr, add_assoc, coe_le_coe_add_iff] at this
          exact this
        · rw [← hins_sdiff X hX]
          have := hG.cross X hXT
          rw [hr] at this
          calc ((r - α : ℝ) : WithTop ℝ) = (r : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ) := by
                rw [← WithTop.coe_add]; ring_nf
            _ ≤ ρ1 X + ρ2 (T \ X) + ((-α : ℝ) : WithTop ℝ) := add_le_add this le_rfl
            _ = _ := by ac_rfl
        · rw [hsdiff_ins X hX]
          have := hG.cross (insert s X) (Finset.insert_subset hsT hXT)
          rw [hr] at this
          calc ((r - α : ℝ) : WithTop ℝ) = (r : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ) := by
                rw [← WithTop.coe_add]; ring_nf
            _ ≤ ρ1 (insert s X) + ρ2 (T \ insert s X) + ((-α : ℝ) : WithTop ℝ) := add_le_add this le_rfl
            _ = _ := by ac_rfl
        · rw [← hins_sdiff X hX]
          have := P2 X hX
          rw [hr, ← WithTop.coe_add] at this
          calc ((r - α : ℝ) : WithTop ℝ) = ((α + r : ℝ) : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ) +
                ((-α : ℝ) : WithTop ℝ) := by
                rw [← WithTop.coe_add, ← WithTop.coe_add]; ring_nf
            _ ≤ ρ1 (insert s X) + ρ2 (T \ X) + ((-α : ℝ) : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ) :=
                add_le_add (add_le_add this le_rfl) le_rfl
            _ = _ := by ac_rfl
    obtain ⟨x', hx1, hx2, hxS, hx0, hxint⟩ := ih _ _ hG'
    have hx's : x' s = 0 := hx0 s hs
    refine ⟨fun v => x' v + if v = s then α else 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro X hX
      rw [sum_shift]
      by_cases hsX : s ∈ X
      · rw [if_pos hsX]
        have hXe : X.erase s ⊆ S' := by
          intro w hw
          rw [Finset.mem_erase] at hw
          rcases Finset.mem_insert.mp (hX hw.2) with h | h
          · exact absurd h hw.1
          · exact h
        have := (hx1 _ hXe).trans (red_le_right ρ1 s α _)
        rw [Finset.insert_erase hsX, coe_le_add_coe_iff] at this
        rw [← Finset.sum_erase X hx's]
        convert this using 2; ring
      · rw [if_neg hsX, add_zero]
        have hXS : X ⊆ S' := fun w hw => by
          rcases Finset.mem_insert.mp (hX hw) with h | h
          · exact absurd (h ▸ hw) hsX
          · exact h
        exact (hx1 _ hXS).trans (red_le_left ρ1 s α _)
    · intro X hX
      rw [sum_shift]
      by_cases hsX : s ∈ X
      · rw [if_pos hsX]
        have hXe : X.erase s ⊆ S' := by
          intro w hw
          rw [Finset.mem_erase] at hw
          rcases Finset.mem_insert.mp (hX hw.2) with h | h
          · exact absurd h hw.1
          · exact h
        have := (hx2 _ hXe).trans (red_le_right ρ2 s α _)
        rw [Finset.insert_erase hsX, coe_le_add_coe_iff] at this
        rw [← Finset.sum_erase X hx's]
        convert this using 2; ring
      · rw [if_neg hsX, add_zero]
        have hXS : X ⊆ S' := fun w hw => by
          rcases Finset.mem_insert.mp (hX hw) with h | h
          · exact absurd (h ▸ hw) hsX
          · exact h
        exact (hx2 _ hXS).trans (red_le_left ρ2 s α _)
    · rw [sum_shift, if_pos hsT, hr, hT, Finset.sum_insert hs, hx's, zero_add]
      rw [hred1S] at hxS
      have := WithTop.coe_injective hxS
      rw [this]; congr 1; ring
    · intro v hv
      have hv1 : v ∉ S' := fun h => hv (hS'T h)
      have hv2 : v ≠ s := fun h => hv (h ▸ hsT)
      show x' v + (if v = s then α else 0) = 0
      rw [hx0 v hv1, if_neg hv2, add_zero]
    · intro hI1 hI2 v
      obtain ⟨k, hk⟩ := hαint hI1 hI2
      subst hk
      obtain ⟨m, hm⟩ := hxint (red_int ρ1 hI1 s k) (red_int ρ2 hI2 s k) v
      by_cases hv : v = s
      · refine ⟨m + k, ?_⟩
        show x' v + (if v = s then (k : ℝ) else 0) = ((m + k : ℤ) : ℝ)
        rw [hm, if_pos hv]; push_cast; ring
      · refine ⟨m, ?_⟩
        show x' v + (if v = s then (k : ℝ) else 0) = (m : ℝ)
        rw [hm, if_neg hv, add_zero]

theorem inter_exists (ρ1 ρ2 : Finset V → WithTop ℝ) (h1 : SubmodularSetFunction ρ1)
    (h2 : SubmodularSetFunction ρ2) (heq : ρ1 Finset.univ = ρ2 Finset.univ)
    (hcross : ∀ X, ρ1 Finset.univ ≤ ρ1 X + ρ2 (Finset.univ \ X)) :
    ∃ x : V → ℝ, x ∈ BasePolyhedron ρ1 ∧ x ∈ BasePolyhedron ρ2 ∧
      (IsIntegerValued ρ1 → IsIntegerValued ρ2 → x ∈ IntPts) := by
  have hG : Good Finset.univ ρ1 ρ2 :=
    ⟨h1.1, h2.1, fun X Y _ _ => h1.2.2 X Y, fun X Y _ _ => h2.2.2 X Y, h1.2.1, heq,
      fun X _ => hcross X⟩
  obtain ⟨x, hx1, hx2, hxS, _, hxint⟩ := inter_core Finset.univ ρ1 ρ2 hG
  refine ⟨x, ⟨fun X => hx1 X (Finset.subset_univ _), hxS⟩,
    ⟨fun X => hx2 X (Finset.subset_univ _), by rw [hxS, heq]⟩, fun hI1 hI2 => hxint hI1 hI2⟩


/-! ### Minkowski decomposition -/

lemma sum_compl (x : V → ℝ) (X : Finset V) :
    ∑ v ∈ Finset.univ \ X, x v = ∑ v, x v - ∑ v ∈ X, x v := by
  have := Finset.sum_sdiff (f := x) (Finset.subset_univ X)
  linarith

/-- the shifted set function `Z ↦ x(Z) - ρ2(V) + ρ2(V \ Z)` -/
noncomputable def sh (ρ2 : Finset V → WithTop ℝ) (x : V → ℝ) (r2 : ℝ) : Finset V → WithTop ℝ :=
  fun Z => ((∑ v ∈ Z, x v - r2 : ℝ) : WithTop ℝ) + ρ2 (Finset.univ \ Z)

lemma sh_submod (ρ2 : Finset V → WithTop ℝ) (hρ2 : SubmodularSetFunction ρ2) (x : V → ℝ) (r2 : ℝ)
    (hr2 : ρ2 Finset.univ = (r2 : WithTop ℝ)) : SubmodularSetFunction (sh ρ2 x r2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold sh
    rw [Finset.sum_empty, Finset.sdiff_empty, hr2, ← WithTop.coe_add, ← WithTop.coe_zero]
    congr 1; ring
  · unfold sh
    rw [Finset.sdiff_self, hρ2.1, add_zero]; exact WithTop.coe_ne_top
  · intro X Y
    unfold sh
    have hsum : ∑ v ∈ X ∪ Y, x v + ∑ v ∈ X ∩ Y, x v = ∑ v ∈ X, x v + ∑ v ∈ Y, x v :=
      Finset.sum_union_inter
    have h2 := hρ2.2.2 (Finset.univ \ X) (Finset.univ \ Y)
    rw [← Finset.sdiff_inter_distrib_right, ← Finset.sdiff_union_distrib] at h2
    rw [ge_iff_le, wt_rearr, wt_rearr]
    calc ((∑ v ∈ X ∪ Y, x v - r2 + (∑ v ∈ X ∩ Y, x v - r2) : ℝ) : WithTop ℝ) +
          (ρ2 (Finset.univ \ (X ∪ Y)) + ρ2 (Finset.univ \ (X ∩ Y)))
        = ((∑ v ∈ X, x v - r2 + (∑ v ∈ Y, x v - r2) : ℝ) : WithTop ℝ) +
          (ρ2 (Finset.univ \ (X ∩ Y)) + ρ2 (Finset.univ \ (X ∪ Y))) := by
          rw [add_comm (ρ2 (Finset.univ \ (X ∪ Y)))]; congr 2; linarith
      _ ≤ _ := add_le_add le_rfl h2

lemma sh_int (ρ2 : Finset V → WithTop ℝ) (hI : IsIntegerValued ρ2) (x : V → ℝ) (hx : x ∈ IntPts)
    (k2 : ℤ) : IsIntegerValued (sh ρ2 x k2) := by
  intro Z
  unfold sh
  rcases hI (Finset.univ \ Z) with ht | ⟨m, hm⟩
  · left; rw [ht, WithTop.add_top]
  · right
    choose k hk using hx
    refine ⟨∑ v ∈ Z, k v - k2 + m, ?_⟩
    rw [hm, ← WithTop.coe_add]
    congr 1
    push_cast
    congr 2
    exact Finset.sum_congr rfl (fun v _ => hk v)

theorem decomp (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1)
    (hρ2 : SubmodularSetFunction ρ2) (x : V → ℝ)
    (hx : x ∈ BasePolyhedron (fun X => ρ1 X + ρ2 X)) :
    ∃ x1 x2 : V → ℝ, x1 ∈ BasePolyhedron ρ1 ∧ x2 ∈ BasePolyhedron ρ2 ∧ x1 + x2 = x ∧
      (IsIntegerValued ρ1 → IsIntegerValued ρ2 → x ∈ IntPts → x1 ∈ IntPts ∧ x2 ∈ IntPts) := by
  obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.mp hρ1.2.1
  obtain ⟨r2, hr2⟩ := WithTop.ne_top_iff_exists.mp hρ2.2.1
  replace hr1 : ρ1 Finset.univ = (r1 : WithTop ℝ) := hr1.symm
  replace hr2 : ρ2 Finset.univ = (r2 : WithTop ℝ) := hr2.symm
  have hxV : ∑ v, x v = r1 + r2 := by
    have := hx.2
    simp only [hr1, hr2, ← WithTop.coe_add] at this
    exact WithTop.coe_injective this
  have hsh := sh_submod ρ2 hρ2 x r2 hr2
  have heq : ρ1 Finset.univ = sh ρ2 x r2 Finset.univ := by
    unfold sh
    rw [Finset.sdiff_self, hρ2.1, add_zero, hr1, hxV]; congr 1; ring
  have hcross : ∀ X, ρ1 Finset.univ ≤ ρ1 X + sh ρ2 x r2 (Finset.univ \ X) := by
    intro X
    unfold sh
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X), sum_compl, hxV, hr1]
    have h1 := hx.1 X
    simp only at h1
    calc (r1 : WithTop ℝ) = ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) +
          ((r1 + r2 - ∑ v ∈ X, x v - r2 : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; ring
      _ ≤ (ρ1 X + ρ2 X) + ((r1 + r2 - ∑ v ∈ X, x v - r2 : ℝ) : WithTop ℝ) := add_le_add h1 le_rfl
      _ = _ := by ac_rfl
  obtain ⟨x1, hx1, hx1', hint⟩ := inter_exists ρ1 (sh ρ2 x r2) hρ1 hsh heq hcross
  have hx1V : ∑ v, x1 v = r1 := by
    have := hx1.2
    rw [hr1] at this
    exact WithTop.coe_injective this
  refine ⟨x1, x - x1, hx1, ⟨fun X => ?_, ?_⟩, by abel, fun hI1 hI2 hxI => ?_⟩
  · have := hx1'.1 (Finset.univ \ X)
    unfold sh at this
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X), sum_compl, sum_compl, hxV, hx1V,
      coe_le_coe_add_iff] at this
    convert this using 2
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    ring
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hxV, hx1V, hr2]
    congr 1; ring
  · have hk2 : ∃ k2 : ℤ, r2 = k2 := by
      rcases hI2 Finset.univ with ht | ⟨k, hk⟩
      · rw [ht] at hr2; exact absurd hr2.symm WithTop.coe_ne_top
      · exact ⟨k, WithTop.coe_injective (hr2.symm.trans hk)⟩
    obtain ⟨k2, hk2⟩ := hk2
    have hx1I : x1 ∈ IntPts := hint hI1 (by rw [hk2]; exact sh_int ρ2 hI2 x hxI k2)
    refine ⟨hx1I, fun v => ?_⟩
    obtain ⟨a, ha⟩ := hxI v
    obtain ⟨b, hb⟩ := hx1I v
    exact ⟨a - b, by simp [ha, hb]⟩

lemma add_subset (ρ1 ρ2 : Finset V → WithTop ℝ) :
    BasePolyhedron ρ1 + BasePolyhedron ρ2 ⊆ BasePolyhedron (fun X => ρ1 X + ρ2 X) := by
  intro z hz
  rw [Set.mem_add] at hz
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hz
  refine ⟨fun X => ?_, ?_⟩
  · show ((∑ v ∈ X, (x1 + x2) v : ℝ) : WithTop ℝ) ≤ ρ1 X + ρ2 X
    simp only [Pi.add_apply, Finset.sum_add_distrib, WithTop.coe_add]
    exact add_le_add (hx1.1 X) (hx2.1 X)
  · show ((∑ v, (x1 + x2) v : ℝ) : WithTop ℝ) = ρ1 Finset.univ + ρ2 Finset.univ
    simp only [Pi.add_apply, Finset.sum_add_distrib, WithTop.coe_add, hx1.2, hx2.2]

lemma IntPts_add (x y : V → ℝ) (hx : x ∈ IntPts) (hy : y ∈ IntPts) : x + y ∈ IntPts := by
  intro v
  obtain ⟨a, ha⟩ := hx v
  obtain ⟨b, hb⟩ := hy v
  exact ⟨a + b, by simp [ha, hb]⟩

/-! ### exchange axiom for the integer points of a base polyhedron -/

/-- A set `X` is tight for `y`. -/
def Tight (ρ : Finset V → WithTop ℝ) (y : V → ℝ) (X : Finset V) : Prop :=
  ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) = ρ X

lemma tight_union_inter (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (y : V → ℝ)
    (hy : y ∈ BasePolyhedron ρ) {X Y : Finset V} (hX : Tight ρ y X) (hY : Tight ρ y Y) :
    Tight ρ y (X ∪ Y) ∧ Tight ρ y (X ∩ Y) := by
  obtain ⟨_, _, hsub⟩ := hρ
  have h1 := hy.1 (X ∪ Y)
  have h2 := hy.1 (X ∩ Y)
  have hs := hsub X Y
  unfold Tight at *
  rw [← hX, ← hY] at hs
  have key : ∑ v ∈ X ∪ Y, y v + ∑ v ∈ X ∩ Y, y v = ∑ v ∈ X, y v + ∑ v ∈ Y, y v :=
    Finset.sum_union_inter
  have hU : ρ (X ∪ Y) ≠ ⊤ := by
    intro h
    rw [h, WithTop.top_add] at hs
    exact (WithTop.coe_ne_top (top_le_iff.mp (by simpa only [← WithTop.coe_add] using hs)))
  have hI : ρ (X ∩ Y) ≠ ⊤ := by
    intro h
    rw [h, WithTop.add_top] at hs
    exact (WithTop.coe_ne_top (top_le_iff.mp (by simpa only [← WithTop.coe_add] using hs)))
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hU
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hI
  rw [← hp] at h1 hs ⊢
  rw [← hq] at h2 hs ⊢
  have h1' : ∑ v ∈ X ∪ Y, y v ≤ p := WithTop.coe_le_coe.mp h1
  have h2' : ∑ v ∈ X ∩ Y, y v ≤ q := WithTop.coe_le_coe.mp h2
  have hs' : p + q ≤ ∑ v ∈ X, y v + ∑ v ∈ Y, y v := by
    have : ((p + q : ℝ) : WithTop ℝ) ≤ ((∑ v ∈ X, y v + ∑ v ∈ Y, y v : ℝ) : WithTop ℝ) := by
      simpa only [WithTop.coe_add] using hs
    exact WithTop.coe_le_coe.mp this
  constructor
  · exact congrArg _ (by linarith)
  · exact congrArg _ (by linarith)

lemma tight_sup (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (y : V → ℝ)
    (hy : y ∈ BasePolyhedron ρ) (S : Finset (Finset V)) (hS : ∀ X ∈ S, Tight ρ y X) :
    Tight ρ y (S.sup id) := by
  induction S using Finset.induction_on with
  | empty => simp [Tight, hρ.1]
  | @insert a S ha ih =>
    rw [Finset.sup_insert]
    exact (tight_union_inter ρ hρ y hy (hS a (Finset.mem_insert_self _ _))
      (ih fun X hX => hS X (Finset.mem_insert_of_mem hX))).1

lemma tight_inf (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (y : V → ℝ)
    (hy : y ∈ BasePolyhedron ρ) (S : Finset (Finset V)) (hS : ∀ X ∈ S, Tight ρ y X) :
    Tight ρ y (S.inf id) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty, Finset.top_eq_univ]
    exact hy.2
  | @insert a S ha ih =>
    rw [Finset.inf_insert]
    exact (tight_union_inter ρ hρ y hy (hS a (Finset.mem_insert_self _ _))
      (ih fun X hX => hS X (Finset.mem_insert_of_mem hX))).2

lemma slack (ρ : Finset V → WithTop ℝ) (hI : IsIntegerValued ρ) (X : Finset V) (n : ℤ)
    (h : ((n : ℝ) : WithTop ℝ) ≤ ρ X) (hne : ((n : ℝ) : WithTop ℝ) ≠ ρ X) :
    (((n : ℝ) + 1 : ℝ) : WithTop ℝ) ≤ ρ X := by
  rcases hI X with ht | ⟨k, hk⟩
  · rw [ht]; exact le_top
  · rw [hk] at h hne ⊢
    rw [WithTop.coe_le_coe] at h ⊢
    have h1 : (n : ℝ) ≠ k := fun e => hne (by rw [e])
    have h2 : n < k := by exact_mod_cast lt_of_le_of_ne h h1
    exact_mod_cast h2

lemma sum_move' (x : V → ℤ) (u v : V) (X : Finset V) :
    ∑ w ∈ X, (x w - CharVec u w + CharVec v w) =
      ∑ w ∈ X, x w - (if u ∈ X then 1 else 0) + (if v ∈ X then 1 else 0) := by
  simp only [CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- moving one unit from `u` to `v` keeps an integer point in the base polyhedron provided
every `x`-tight set containing `v` contains `u`. -/
lemma move_mem (ρ : Finset V → WithTop ℝ) (hI : IsIntegerValued ρ) (x : V → ℤ)
    (hx : (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ) (u v : V)
    (hv : ∀ X, Tight ρ (fun v => (x v : ℝ)) X → v ∈ X → u ∈ X) :
    (fun w => ((x w - CharVec u w + CharVec v w : ℤ) : ℝ)) ∈ BasePolyhedron ρ := by
  have hsx : ∀ X : Finset V, ∑ w ∈ X, (x w : ℝ) = ((∑ w ∈ X, x w : ℤ) : ℝ) :=
    fun X => (Int.cast_sum X x).symm
  refine ⟨fun X => ?_, ?_⟩
  · rw [← Int.cast_sum, sum_move']
    have hxX := hx.1 X
    simp only at hxX
    rw [hsx] at hxX
    by_cases hvX : v ∈ X
    · by_cases huX : u ∈ X
      · rw [if_pos hvX, if_pos huX]; simpa using hxX
      · rw [if_pos hvX, if_neg huX, sub_zero]
        have hnt : ((∑ w ∈ X, x w : ℤ) : ℝ) ≠ ρ X := by
          intro ht
          apply huX
          apply hv X _ hvX
          unfold Tight
          simp only
          rw [hsx]; exact ht
        have := slack ρ hI X _ hxX hnt
        push_cast at this ⊢
        exact this
    · rw [if_neg hvX, add_zero]
      calc (((∑ w ∈ X, x w - if u ∈ X then 1 else 0 : ℤ) : ℝ) : WithTop ℝ)
          ≤ (((∑ w ∈ X, x w : ℤ) : ℝ) : WithTop ℝ) := by
            rw [WithTop.coe_le_coe]; split_ifs <;> push_cast <;> linarith
        _ ≤ ρ X := hxX
  · rw [← Int.cast_sum, sum_move', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    have := hx.2
    simp only at this
    rw [hsx] at this
    simpa using this

theorem exch_int (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ)
    (hI : IsIntegerValued ρ) :
    ExchangeAxiomB {x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ} := by
  classical
  intro x hx y hy u hu
  simp only [Set.mem_setOf_eq] at hx hy
  have hu' : y u < x u := hu
  set xr : V → ℝ := fun v => (x v : ℝ) with hxr
  set yr : V → ℝ := fun v => (y v : ℝ) with hyr
  set F : Finset (Finset V) := Finset.univ.filter (fun X => Tight ρ yr X ∧ u ∈ X) with hF
  set A := F.inf id with hA_def
  have hA : Tight ρ yr A :=
    tight_inf ρ hρ yr hy F (fun X hX => (Finset.mem_filter.mp hX).2.1)
  have huA : u ∈ A := by
    have : {u} ≤ F.inf id := Finset.le_inf (fun X hX =>
      Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hX).2.2)
    exact Finset.singleton_subset_iff.mp this
  have hAmin : ∀ X, Tight ρ yr X → u ∈ X → A ⊆ X := fun X hX huX =>
    Finset.inf_le (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX, huX⟩)
  set W : Finset V := Finset.univ.filter (fun v => v ∈ A ∧ x v < y v) with hW
  have key : ∃ v ∈ W, ∀ X, Tight ρ xr X → v ∈ X → u ∈ X := by
    by_contra hcon
    push_neg at hcon
    choose! f hf using hcon
    set D : Finset V := (W.image f).sup id with hD_def
    have hD : Tight ρ xr D := by
      apply tight_sup ρ hρ xr hx
      intro X hX
      rw [Finset.mem_image] at hX
      obtain ⟨v, hv, rfl⟩ := hX
      exact (hf v hv).1
    have huD : u ∉ D := by
      intro h
      rw [Finset.mem_sup] at h
      obtain ⟨X, hX, huX⟩ := h
      rw [Finset.mem_image] at hX
      obtain ⟨v, hv, rfl⟩ := hX
      exact (hf v hv).2.2 huX
    have hWD : ∀ v ∈ W, v ∈ D := fun v hv =>
      Finset.mem_sup.mpr ⟨f v, Finset.mem_image_of_mem f hv, (hf v hv).2.1⟩
    have hsub := hρ.2.2 A D
    have h1 := hx.1 (A ∪ D)
    have h2 := hy.1 (A ∩ D)
    unfold Tight at hA hD
    rw [← hA, ← hD] at hsub
    have h3 : ((∑ v ∈ A ∪ D, xr v + ∑ v ∈ A ∩ D, yr v : ℝ) : WithTop ℝ) ≤
        ((∑ v ∈ A, yr v + ∑ v ∈ D, xr v : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add, WithTop.coe_add]; exact (add_le_add h1 h2).trans hsub
    rw [WithTop.coe_le_coe] at h3
    have e1 : ∑ v ∈ A ∪ D, xr v = ∑ v ∈ A \ D, xr v + ∑ v ∈ D, xr v := by
      rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
    have e2 : ∑ v ∈ A, yr v = ∑ v ∈ A \ D, yr v + ∑ v ∈ A ∩ D, yr v := by
      rw [← Finset.sum_sdiff (Finset.inter_subset_left (s₂ := D)), Finset.sdiff_inter_self_left]
    have h5 : ∑ v ∈ A \ D, yr v < ∑ v ∈ A \ D, xr v := by
      apply Finset.sum_lt_sum
      · intro v hv
        rw [Finset.mem_sdiff] at hv
        have hvW : v ∉ W := fun hvW => hv.2 (hWD v hvW)
        simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hvW
        simp only [hxr, hyr]
        exact_mod_cast hvW hv.1
      · refine ⟨u, Finset.mem_sdiff.mpr ⟨huA, huD⟩, ?_⟩
        simp only [hxr, hyr]
        exact_mod_cast hu'
    linarith
  obtain ⟨v, hvW, hv⟩ := key
  simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hvW
  obtain ⟨hvA, hxy⟩ := hvW
  refine ⟨v, hxy, move_mem ρ hI x hx u v hv, ?_⟩
  have hvu : v ≠ u := fun h => by rw [h] at hxy; omega
  have := move_mem ρ hI y hy v u (fun X hX huX => hAmin X hX huX hvA)
  have e : (fun w => ((y w + CharVec u w - CharVec v w : ℤ) : ℝ)) =
      (fun w => ((y w - CharVec v w + CharVec u w : ℤ) : ℝ)) := by
    funext w; congr 1; ring
  show (fun w => ((y w + CharVec u w - CharVec v w : ℤ) : ℝ)) ∈ BasePolyhedron ρ
  rw [e]; exact this

/-! ### the induced set function of an M-convex set -/

/-- `ρ(X) = sup {x(X) : x ∈ B}` (the book's Eq. (4.25)). -/
noncomputable def IRho (B : Set (V → ℤ)) : Finset V → WithTop ℝ :=
  fun X => sSup ((fun x : V → ℤ => (((∑ v ∈ X, x v : ℤ) : ℝ) : WithTop ℝ)) '' B)


/-- `x + χ_u - χ_v ∈ B`. -/
def Edge (B : Set (V → ℤ)) (x : V → ℤ) (u v : V) : Prop :=
  (fun w => x w + CharVec u w - CharVec v w) ∈ B

lemma sum_move (x : V → ℤ) (u v : V) (X : Finset V) :
    ∑ w ∈ X, (x w + CharVec u w - CharVec v w) =
      ∑ w ∈ X, x w + (if u ∈ X then 1 else 0) - (if v ∈ X then 1 else 0) := by
  simp only [CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- distance decreases -/
lemma dist_lt (x z x' : V → ℤ) (a b : V) (ha : x a < z a) (hb : z b < x b)
    (hx' : ∀ w, x' w = x w + CharVec a w - CharVec b w) :
    ∑ w, (x' w - z w).natAbs < ∑ w, (x w - z w).natAbs := by
  have hab : a ≠ b := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    rw [hx']
    simp only [CharVec]
    by_cases hwa : w = a
    · subst hwa; simp [hab]; omega
    · by_cases hwb : w = b
      · subst hwb; simp [hwa]; omega
      · simp [hwa, hwb]
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [hx']
    simp only [CharVec, if_true, if_neg hab]
    omega

lemma lemG (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (L : Finset V) (x : V → ℤ) (hx : x ∈ B)
    (hloc : ∀ u v, Edge B x u v → u ∈ L → v ∈ L) :
    ∀ y ∈ B, ∑ w ∈ L, y w ≤ ∑ w ∈ L, x w := by
  suffices H : ∀ n : ℕ, ∀ y ∈ B, ∑ w, (y w - x w).natAbs = n → ∑ w ∈ L, y w ≤ ∑ w ∈ L, x w by
    intro y hy; exact H _ y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy hn
    by_contra hlt
    push_neg at hlt
    obtain ⟨u, huL, hu⟩ := Finset.exists_lt_of_sum_lt hlt
    obtain ⟨v, hv, hy', hx'⟩ := hExc y hy x hx u hu
    have hv' : y v < x v := hv
    have hvL : v ∈ L := hloc u v hx' huL
    have hlt2 := dist_lt y x (fun w => y w - CharVec u w + CharVec v w) v u hv' hu
      (fun w => by ring)
    have := ih _ (hn ▸ hlt2) _ hy' rfl
    have e : ∑ w ∈ L, (y w - CharVec u w + CharVec v w) = ∑ w ∈ L, y w := by
      have := sum_move y v u L
      rw [show (∑ w ∈ L, (y w - CharVec u w + CharVec v w)) =
        ∑ w ∈ L, (y w + CharVec v w - CharVec u w) from
          Finset.sum_congr rfl (fun w _ => by ring), this]
      simp [huL, hvL]
    rw [e] at this
    omega

lemma edge_trans (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (x : V → ℤ)
    (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : Edge B x a b) (h2 : Edge B x b c) : Edge B x a c := by
  obtain ⟨v, hv, hA, hB⟩ := hExc _ h2 _ h1 b (by
    show (x b + CharVec a b - CharVec b b) < (x b + CharVec b b - CharVec c b)
    simp [CharVec, hab.symm, hbc])
  have hv' : (x v + CharVec b v - CharVec c v) < (x v + CharVec a v - CharVec b v) := hv
  by_cases hva : v = a
  · subst hva
    unfold Edge
    convert hA using 1
    funext w
    simp only [CharVec]
    split_ifs <;> omega
  · by_cases hvc : v = c
    · subst hvc
      unfold Edge
      convert hB using 1
      funext w
      simp only [CharVec]
      split_ifs <;> omega
    · exfalso
      simp only [CharVec, if_neg hva, if_neg hvc] at hv'
      split_ifs at hv' <;> omega

/-! ### facts about `IRho` -/

lemma rho_ge (B : Set (V → ℤ)) (X : Finset V) (y : V → ℤ) (hy : y ∈ B) :
    ((((∑ v ∈ X, y v : ℤ) : ℝ)) : WithTop ℝ) ≤ IRho B X :=
  le_csSup (OrderTop.bddAbove _) ⟨y, hy, rfl⟩

lemma rho_eq (B : Set (V → ℤ)) (X : Finset V) (x : V → ℤ) (hx : x ∈ B)
    (hmax : ∀ y ∈ B, ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v) :
    IRho B X = ((((∑ v ∈ X, x v : ℤ) : ℝ)) : WithTop ℝ) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact WithTop.coe_le_coe.mpr (Int.cast_le.mpr (hmax y hy))

lemma rho_bdd (B : Set (V → ℤ)) (X : Finset V) (h : IRho B X ≠ ⊤) :
    ∃ b : ℤ, ∀ y ∈ B, ∑ v ∈ X, y v ≤ b := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
  refine ⟨⌊r⌋, fun y hy => ?_⟩
  have := rho_ge B X y hy
  rw [← hr] at this
  have h' : ((∑ v ∈ X, y v : ℤ) : ℝ) ≤ r := WithTop.coe_le_coe.mp this
  exact Int.le_floor.mpr h'

lemma max_exists (B S : Set (V → ℤ)) (hS : S ⊆ B) (hSne : S.Nonempty) (X : Finset V)
    (h : IRho B X ≠ ⊤) :
    ∃ x ∈ S, ∀ y ∈ S, ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v := by
  classical
  obtain ⟨b, hb⟩ := rho_bdd B X h
  obtain ⟨ub, ⟨x, hxS, hx⟩, hub⟩ := Int.exists_greatest_of_bdd
    (P := fun n => ∃ y ∈ S, ∑ v ∈ X, y v = n)
    ⟨b, fun n ⟨y, hy, hyn⟩ => hyn ▸ hb y (hS hy)⟩
    (by obtain ⟨y, hy⟩ := hSne; exact ⟨_, y, hy, rfl⟩)
  exact ⟨x, hxS, fun y hy => hx ▸ hub _ ⟨y, hy, rfl⟩⟩

lemma sum_const (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (x y : V → ℤ) (hx : x ∈ B)
    (hy : y ∈ B) : ∑ v, y v = ∑ v, x v := by
  apply le_antisymm
  · exact lemG B hExc Finset.univ x hx (fun _ _ _ _ => Finset.mem_univ _) y hy
  · exact lemG B hExc Finset.univ y hy (fun _ _ _ _ => Finset.mem_univ _) x hx

lemma rho_submod (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty)
    (X Y : Finset V) :
    IRho B X + IRho B Y ≥ IRho B (X ∪ Y) + IRho B (X ∩ Y) := by
  classical
  by_cases hX : IRho B X = ⊤
  · rw [hX, WithTop.top_add]; exact le_top
  by_cases hY : IRho B Y = ⊤
  · rw [hY, WithTop.add_top]; exact le_top
  obtain ⟨x1, hx1, hx1max⟩ := max_exists B B le_rfl hBne X hX
  set S2 := {x ∈ B | ∀ y ∈ B, ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v} with hS2
  obtain ⟨x, ⟨hxB, hxX⟩, hxY⟩ := max_exists B S2 (fun z hz => hz.1) ⟨x1, hx1, hx1max⟩ Y hY
  -- local conditions
  have key : ∀ u v, Edge B x u v →
      (∑ w ∈ X, (x w + CharVec u w - CharVec v w) ≤ ∑ w ∈ X, x w) ∧
      (∑ w ∈ X, (x w + CharVec u w - CharVec v w) = ∑ w ∈ X, x w →
        ∑ w ∈ Y, (x w + CharVec u w - CharVec v w) ≤ ∑ w ∈ Y, x w) := by
    intro u v huv
    refine ⟨hxX _ huv, fun heq => hxY _ ⟨huv, fun y hy => heq ▸ hxX y hy⟩⟩
  have locI : ∀ u v, Edge B x u v → u ∈ X ∩ Y → v ∈ X ∩ Y := by
    intro u v huv hu
    obtain ⟨k1, k2⟩ := key u v huv
    rw [Finset.mem_inter] at hu ⊢
    rw [sum_move] at k1 k2
    rw [sum_move] at k2
    by_cases hvX : v ∈ X
    · refine ⟨hvX, ?_⟩
      by_contra hvY
      have := k2 (by simp [hu.1, hvX])
      simp [hu.2, hvY] at this
    · simp [hu.1, hvX] at k1
  have locU : ∀ u v, Edge B x u v → u ∈ X ∪ Y → v ∈ X ∪ Y := by
    intro u v huv hu
    obtain ⟨k1, k2⟩ := key u v huv
    rw [Finset.mem_union] at hu ⊢
    rw [sum_move] at k1 k2
    rw [sum_move] at k2
    by_contra hv
    push_neg at hv
    by_cases huX : u ∈ X
    · simp [huX, hv.1] at k1
    · have hu2 : u ∈ Y := hu.resolve_left huX
      have := k2 (by simp [huX, hv.1])
      simp [hu2, hv.2] at this
  have gI := lemG B hExc (X ∩ Y) x hxB locI
  have gU := lemG B hExc (X ∪ Y) x hxB locU
  rw [rho_eq B (X ∩ Y) x hxB gI, rho_eq B (X ∪ Y) x hxB gU, rho_eq B X x hxB hxX]
  have hYge := rho_ge B Y x hxB
  have e : ((((∑ v ∈ X ∪ Y, x v : ℤ) : ℝ)) : WithTop ℝ) +
      ((((∑ v ∈ X ∩ Y, x v : ℤ) : ℝ)) : WithTop ℝ) =
      ((((∑ v ∈ X, x v : ℤ) : ℝ)) : WithTop ℝ) + ((((∑ v ∈ Y, x v : ℤ) : ℝ)) : WithTop ℝ) := by
    rw [← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    push_cast
    exact_mod_cast (Finset.sum_union_inter (s₁ := X) (s₂ := Y) (f := x))
  rw [ge_iff_le, e]
  exact add_le_add le_rfl hYge

lemma rho_int (B : Set (V → ℤ)) (hBne : B.Nonempty) : IsIntegerValued (IRho B) := by
  intro X
  by_cases h : IRho B X = ⊤
  · exact Or.inl h
  · right
    obtain ⟨x, hx, hmax⟩ := max_exists B B le_rfl hBne X h
    exact ⟨_, rho_eq B X x hx hmax⟩

/-- integer points of the base polyhedron belong to `B` -/
lemma crux (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) (z : V → ℤ)
    (hz : ∀ X : Finset V, ((((∑ v ∈ X, z v : ℤ) : ℝ)) : WithTop ℝ) ≤ IRho B X)
    (hzV : ∀ x ∈ B, ∑ v, z v = ∑ v, x v) : z ∈ B := by
  classical
  have hex : ∃ n : ℕ, ∃ x ∈ B, ∑ w, (x w - z w).natAbs = n := by
    obtain ⟨x, hx⟩ := hBne; exact ⟨_, x, hx, rfl⟩
  obtain ⟨x, hxB, hxn⟩ := Nat.find_spec hex
  have hmin := fun m (h : ∃ x ∈ B, ∑ w, (x w - z w).natAbs = m) => Nat.find_min' hex h
  by_contra hzB
  have hxz : x ≠ z := fun h => hzB (h ▸ hxB)
  set L : Finset V := Finset.univ.filter
    (fun w => x w < z w ∨ ∃ a, x a < z a ∧ Edge B x a w) with hL
  have hclosed : ∀ u v, Edge B x u v → u ∈ L → v ∈ L := by
    intro u v huv hu
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rcases hu with hu | ⟨a, ha, hau⟩
    · exact Or.inr ⟨u, hu, huv⟩
    · by_cases hva : v = a
      · exact Or.inl (hva ▸ ha)
      by_cases huv' : u = v
      · exact Or.inr ⟨a, ha, huv' ▸ hau⟩
      by_cases hau' : a = u
      · exact Or.inr ⟨a, ha, hau' ▸ huv⟩
      exact Or.inr ⟨a, ha, edge_trans B hExc x a u v hau' huv' (Ne.symm hva) hau huv⟩
  have hG := lemG B hExc L x hxB hclosed
  have hzL : ∑ w ∈ L, z w ≤ ∑ w ∈ L, x w := by
    have h1 := hz L
    rw [rho_eq B L x hxB hG] at h1
    exact_mod_cast WithTop.coe_le_coe.mp h1
  -- some coordinate with x < z
  have hA : ∃ a, x a < z a := by
    by_contra hne
    push_neg at hne
    apply hxz
    have hs := hzV x hxB
    funext w
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hne i)).mp hs
    exact (this w (Finset.mem_univ _)).symm
  obtain ⟨a, ha⟩ := hA
  have haL : a ∈ L := by simp [hL, ha]
  obtain ⟨w, hwL, hw⟩ : ∃ w ∈ L, z w < x w := by
    by_contra hne
    push_neg at hne
    have : ∑ w ∈ L, x w < ∑ w ∈ L, z w :=
      Finset.sum_lt_sum (fun i hi => hne i hi) ⟨a, haL, ha⟩
    omega
  simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hwL
  rcases hwL with hw' | ⟨b, hb, hbw⟩
  · omega
  · have hlt := dist_lt x z (fun v => x v + CharVec b v - CharVec w v) b w hb hw (fun _ => rfl)
    have := hmin _ ⟨_, hbw, rfl⟩
    rw [hxn] at hlt
    omega

theorem IRho_props (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    SubmodularSetFunction (IRho B) ∧ IsIntegerValued (IRho B) ∧
      IntEmbed B = BasePolyhedron (IRho B) ∩ IntPts := by
  classical
  obtain ⟨x0, hx0⟩ := hBne
  have hmaxV : ∀ y ∈ B, ∑ v ∈ Finset.univ, y v ≤ ∑ v ∈ Finset.univ, x0 v :=
    fun y hy => (sum_const B hExc x0 y hx0 hy).le
  have hρV : IRho B Finset.univ = ((((∑ v, x0 v : ℤ) : ℝ)) : WithTop ℝ) :=
    rho_eq B _ x0 hx0 hmaxV
  have hρV' : IRho B Finset.univ ≠ ⊤ := by rw [hρV]; exact WithTop.coe_ne_top
  have hsub : SubmodularSetFunction (IRho B) := by
    refine ⟨?_, hρV', rho_submod B hExc ⟨x0, hx0⟩⟩
    rw [rho_eq B ∅ x0 hx0 (fun y _ => by simp)]
    simp
  have hint := rho_int B ⟨x0, hx0⟩
  refine ⟨hsub, hint, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨fun X => ?_, ?_⟩, fun v => ⟨x v, rfl⟩⟩
    · have := rho_ge B X x hx
      simpa using this
    · rw [hρV, ← sum_const B hExc x0 x hx0 hx]
      simp
  · rintro z ⟨hzB, hzI⟩
    choose k hk using hzI
    have hzk : z = fun v => (k v : ℝ) := funext hk
    subst hzk
    refine ⟨k, crux B hExc ⟨x0, hx0⟩ k (fun X => ?_) (fun x hx => ?_), rfl⟩
    · have := hzB.1 X
      simpa using this
    · have h2 := hzB.2
      rw [rho_eq B _ x hx (fun y hy => (sum_const B hExc x y hx hy).le)] at h2
      have h3 : ((∑ v, k v : ℤ) : ℝ) = ((∑ v, x v : ℤ) : ℝ) := by
        have := WithTop.coe_injective h2
        beta_reduce at this
        push_cast at this ⊢; exact this
      exact_mod_cast h3

/-! ### Minkowski sums of M-convex sets -/

lemma IntEmbed_add (B1 B2 : Set (V → ℤ)) :
    IntEmbed (B1 + B2) = IntEmbed B1 + IntEmbed B2 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [Set.mem_add]
    refine ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, ?_⟩
    funext v; simp
  · intro hz
    rw [Set.mem_add] at hz
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := hz
    refine ⟨a + b, Set.add_mem_add ha hb, ?_⟩
    funext v; simp

theorem mink_mconvex (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) :
    ExchangeAxiomB (B1 + B2) ∧ (B1 + B2).Nonempty ∧
      convexHull ℝ (IntEmbed (B1 + B2)) = convexHull ℝ (IntEmbed B1) + convexHull ℝ (IntEmbed B2) := by
  obtain ⟨hs1, hi1, he1⟩ := IRho_props B1 hExc1 hB1ne
  obtain ⟨hs2, hi2, he2⟩ := IRho_props B2 hExc2 hB2ne
  refine ⟨?_, ?_, ?_⟩
  · have hsum : SubmodularSetFunction (fun X => IRho B1 X + IRho B2 X) := by
      refine ⟨by simp only [hs1.1, hs2.1, add_zero], WithTop.add_ne_top.mpr ⟨hs1.2.1, hs2.2.1⟩, ?_⟩
      intro X Y
      have h1 := hs1.2.2 X Y
      have h2 := hs2.2.2 X Y
      simp only [ge_iff_le] at h1 h2 ⊢
      calc IRho B1 (X ∪ Y) + IRho B2 (X ∪ Y) + (IRho B1 (X ∩ Y) + IRho B2 (X ∩ Y))
          = (IRho B1 (X ∪ Y) + IRho B1 (X ∩ Y)) + (IRho B2 (X ∪ Y) + IRho B2 (X ∩ Y)) := by ac_rfl
        _ ≤ (IRho B1 X + IRho B1 Y) + (IRho B2 X + IRho B2 Y) := add_le_add h1 h2
        _ = _ := by ac_rfl
    have hint : IsIntegerValued (fun X => IRho B1 X + IRho B2 X) := by
      intro X
      rcases hi1 X with h1 | ⟨k1, hk1⟩
      · left; simp only [h1, WithTop.top_add]
      rcases hi2 X with h2 | ⟨k2, hk2⟩
      · left; simp only [h2, WithTop.add_top]
      · right; refine ⟨k1 + k2, ?_⟩
        simp only [hk1, hk2, ← WithTop.coe_add]; push_cast; rfl
    have hset : B1 + B2 = {z : V → ℤ | (fun v => (z v : ℝ)) ∈
        BasePolyhedron (fun X => IRho B1 X + IRho B2 X)} := by
      ext z
      rw [Set.mem_add, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        have ha' : (fun v => (a v : ℝ)) ∈ IntEmbed B1 := ⟨a, ha, rfl⟩
        rw [he1] at ha'
        have hb' : (fun v => (b v : ℝ)) ∈ IntEmbed B2 := ⟨b, hb, rfl⟩
        rw [he2] at hb'
        replace ha' := ha'.1
        replace hb' := hb'.1
        have := add_subset (IRho B1) (IRho B2) (Set.add_mem_add ha' hb')
        convert this using 1
        funext v; simp
      · intro hz
        obtain ⟨x1, x2, h1, h2, hsum', hI⟩ := decomp _ _ hs1 hs2 _ hz
        obtain ⟨hI1, hI2⟩ := hI hi1 hi2 (fun v => ⟨z v, rfl⟩)
        have hx1 : x1 ∈ IntEmbed B1 := by rw [he1]; exact ⟨h1, hI1⟩
        have hx2 : x2 ∈ IntEmbed B2 := by rw [he2]; exact ⟨h2, hI2⟩
        obtain ⟨a, ha, rfl⟩ := hx1
        obtain ⟨b, hb, rfl⟩ := hx2
        refine ⟨a, ha, b, hb, ?_⟩
        funext v
        have := congrFun hsum' v
        simp only [Pi.add_apply] at this
        exact_mod_cast this
    rw [hset]
    exact exch_int _ hsum hint
  · obtain ⟨a, ha⟩ := hB1ne
    obtain ⟨b, hb⟩ := hB2ne
    exact ⟨a + b, Set.add_mem_add ha hb⟩
  · rw [IntEmbed_add, convexHull_add]

theorem mink_core (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1)
    (hρ2 : SubmodularSetFunction ρ2)
    (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) :
    (BasePolyhedron ρ1 + BasePolyhedron ρ2 = BasePolyhedron (fun X => ρ1 X + ρ2 X)) ∧
    (IsIntegerValued ρ1 → IsIntegerValued ρ2 →
      (BasePolyhedron ρ1 ∩ IntPts) + (BasePolyhedron ρ2 ∩ IntPts) =
        BasePolyhedron (fun X => ρ1 X + ρ2 X) ∩ IntPts) ∧
    (ExchangeAxiomB (B1 + B2) ∧ (B1 + B2).Nonempty ∧
      convexHull ℝ (IntEmbed (B1 + B2)) = convexHull ℝ (IntEmbed B1) + convexHull ℝ (IntEmbed B2)) := by
  refine ⟨?_, ?_, mink_mconvex B1 B2 hExc1 hExc2 hB1ne hB2ne⟩
  · apply Set.Subset.antisymm (add_subset ρ1 ρ2)
    intro x hx
    obtain ⟨x1, x2, h1, h2, rfl, _⟩ := decomp ρ1 ρ2 hρ1 hρ2 x hx
    exact Set.add_mem_add h1 h2
  · intro hI1 hI2
    apply Set.Subset.antisymm
    · intro z hz
      rw [Set.mem_add] at hz
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hz
      exact ⟨add_subset ρ1 ρ2 (Set.add_mem_add hx1.1 hx2.1), IntPts_add _ _ hx1.2 hx2.2⟩
    · rintro x ⟨hx, hxI⟩
      obtain ⟨x1, x2, h1, h2, rfl, hI⟩ := decomp ρ1 ρ2 hρ1 hρ2 x hx
      obtain ⟨hI1', hI2'⟩ := hI hI1 hI2 hxI
      exact Set.add_mem_add ⟨h1, hI1'⟩ ⟨h2, hI2'⟩


lemma coe_le_iff (r : ℝ) (t : WithTop ℝ) : ((r : WithTop ℝ) ≤ t) ↔ ∀ s : ℝ, t = s → r ≤ s := by
  cases t with
  | top => simp
  | coe s => simp

lemma bp_convex (ρ : Finset V → WithTop ℝ) (hV : ρ Finset.univ ≠ ⊤) :
    Convex ℝ (BasePolyhedron ρ) := by
  intro a ha b hb s t hs ht hst
  refine ⟨fun X => ?_, ?_⟩
  · have h1 := ha.1 X
    have h2 := hb.1 X
    rw [coe_le_iff] at h1 h2 ⊢
    intro r hr
    have e : ∑ v ∈ X, (s • a + t • b) v = s * ∑ v ∈ X, a v + t * ∑ v ∈ X, b v := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    rw [e]
    have ha' := h1 r hr
    have hb' := h2 r hr
    have hr' : r = s * r + t * r := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left ha' hs, mul_le_mul_of_nonneg_left hb' ht]
  · have h1 := ha.2
    have h2 := hb.2
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hV
    rw [← hr] at h1 h2 ⊢
    have h1' := WithTop.coe_injective h1
    have h2' := WithTop.coe_injective h2
    have e : ∑ v, (s • a + t • b) v = s * ∑ v, a v + t * ∑ v, b v := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    congr 1
    rw [e, h1', h2', ← add_mul, hst, one_mul]

end MK

namespace IH
open Classical
open MK

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### blocks of the tight-set lattice -/

/-- the block of `u`: all `v` lying in exactly the same tight sets as `u` -/
noncomputable def blk (ρ : Finset V → WithTop ℝ) (x : V → ℝ) (u : V) : Finset V :=
  Finset.univ.filter (fun v => ∀ X : Finset V, Tight ρ x X → (u ∈ X ↔ v ∈ X))

lemma mem_blk {ρ : Finset V → WithTop ℝ} {x : V → ℝ} {u v : V} :
    v ∈ blk ρ x u ↔ ∀ X : Finset V, Tight ρ x X → (u ∈ X ↔ v ∈ X) := by
  simp [blk]

lemma blk_self (ρ : Finset V → WithTop ℝ) (x : V → ℝ) (u : V) : u ∈ blk ρ x u :=
  mem_blk.mpr (fun _ _ => Iff.rfl)

lemma blk_eq_of_mem {ρ : Finset V → WithTop ℝ} {x : V → ℝ} {u v : V} (h : v ∈ blk ρ x u) :
    blk ρ x v = blk ρ x u := by
  ext w
  simp only [mem_blk]
  constructor
  · intro hw X hX; exact (mem_blk.mp h X hX).trans (hw X hX)
  · intro hw X hX; exact (mem_blk.mp h X hX).symm.trans (hw X hX)

lemma blk_subset {ρ : Finset V → WithTop ℝ} {x : V → ℝ} {u : V} {X : Finset V}
    (hX : Tight ρ x X) (hu : u ∈ X) : blk ρ x u ⊆ X :=
  fun v hv => (mem_blk.mp hv X hX).mp hu

lemma blk_eq_or_disjoint (ρ : Finset V → WithTop ℝ) (x : V → ℝ) (u v : V) :
    blk ρ x u = blk ρ x v ∨ Disjoint (blk ρ x u) (blk ρ x v) := by
  by_cases h : ∃ w, w ∈ blk ρ x u ∧ w ∈ blk ρ x v
  · obtain ⟨w, hwu, hwv⟩ := h
    left; rw [← blk_eq_of_mem hwu, ← blk_eq_of_mem hwv]
  · right
    rw [Finset.disjoint_left]
    intro w hwu hwv; exact h ⟨w, hwu, hwv⟩

lemma sum_over_blocks (ρ : Finset V → WithTop ℝ) (x : V → ℝ) (S : Finset V) (g : V → ℝ) :
    ∑ v ∈ (S.image (blk ρ x)).biUnion id, g v = ∑ A ∈ S.image (blk ρ x), ∑ v ∈ A, g v := by
  apply Finset.sum_biUnion
  intro A hA A' hA' hne
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hA hA'
  obtain ⟨u, _, rfl⟩ := hA
  obtain ⟨u', _, rfl⟩ := hA'
  rcases blk_eq_or_disjoint ρ x u u' with h | h
  · exact absurd h hne
  · exact h

lemma biUnion_blocks (ρ : Finset V → WithTop ℝ) (x : V → ℝ) {X : Finset V} (hX : Tight ρ x X) :
    (X.image (blk ρ x)).biUnion id = X := by
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨A, ⟨u, hu, rfl⟩, hw⟩; exact blk_subset hX hu hw
  · intro hw; exact ⟨blk ρ x w, ⟨w, hw, rfl⟩, blk_self ρ x w⟩

lemma tight_sum_zero (ρ : Finset V → WithTop ℝ) (x : V → ℝ) (d : V → ℝ)
    (hd : ∀ u, ∑ v ∈ blk ρ x u, d v = 0) (X : Finset V) (hX : Tight ρ x X) :
    ∑ v ∈ X, d v = 0 := by
  rw [← biUnion_blocks ρ x hX, sum_over_blocks]
  apply Finset.sum_eq_zero
  intro A hA
  rw [Finset.mem_image] at hA
  obtain ⟨u, _, rfl⟩ := hA
  exact hd u

lemma tight_int (ρ : Finset V → WithTop ℝ) (hI : IsIntegerValued ρ) (x : V → ℝ) (X : Finset V)
    (hX : Tight ρ x X) : ∃ k : ℤ, ∑ v ∈ X, x v = k := by
  rcases hI X with ht | ⟨k, hk⟩
  · unfold Tight at hX; rw [ht] at hX; exact absurd hX WithTop.coe_ne_top
  · unfold Tight at hX; rw [hk] at hX; exact ⟨k, WithTop.coe_injective hX⟩

lemma sum_blk_int (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hI : IsIntegerValued ρ)
    (x : V → ℝ) (hx : x ∈ BasePolyhedron ρ) (u : V) :
    ∃ k : ℤ, ∑ v ∈ blk ρ x u, x v = k := by
  set T : Finset V := (Finset.univ.filter (fun X => Tight ρ x X ∧ u ∈ X)).inf id with hT
  have hTt : Tight ρ x T := tight_inf ρ hρ x hx _ (fun X hX => (Finset.mem_filter.mp hX).2.1)
  have huT : u ∈ T := by
    have : {u} ≤ T := Finset.le_inf (fun X hX =>
      Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hX).2.2)
    exact Finset.singleton_subset_iff.mp this
  have hTmin : ∀ X, Tight ρ x X → u ∈ X → T ⊆ X := fun X hX huX =>
    Finset.inf_le (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX, huX⟩)
  set S : Finset V := (Finset.univ.filter (fun X => Tight ρ x X ∧ X ⊆ T ∧ u ∉ X)).sup id with hS
  have hSt : Tight ρ x S := tight_sup ρ hρ x hx _ (fun X hX => (Finset.mem_filter.mp hX).2.1)
  have hST : S ⊆ T := Finset.sup_le (fun X hX => (Finset.mem_filter.mp hX).2.2.1)
  have hSmax : ∀ X, Tight ρ x X → X ⊆ T → u ∉ X → X ⊆ S := fun X hX h1 h2 =>
    Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX, h1, h2⟩)
  have hblk : blk ρ x u = T \ S := by
    ext v
    rw [Finset.mem_sdiff, mem_blk]
    constructor
    · intro hv
      refine ⟨(hv T hTt).mp huT, fun hvS => ?_⟩
      rw [Finset.mem_sup] at hvS
      obtain ⟨X, hX, hvX⟩ := hvS
      have := Finset.mem_filter.mp hX
      exact this.2.2.2 ((hv X this.2.1).mpr hvX)
    · rintro ⟨hvT, hvS⟩ X hX
      constructor
      · intro huX; exact hTmin X hX huX hvT
      · intro hvX
        by_contra huX
        have hXT : Tight ρ x (X ∩ T) := (tight_union_inter ρ hρ x hx hX hTt).2
        have : X ∩ T ⊆ S := hSmax _ hXT Finset.inter_subset_right
          (fun h => huX (Finset.mem_inter.mp h).1)
        exact hvS (this (Finset.mem_inter.mpr ⟨hvX, hvT⟩))
  obtain ⟨kT, hkT⟩ := tight_int ρ hI x T hTt
  obtain ⟨kS, hkS⟩ := tight_int ρ hI x S hSt
  refine ⟨kT - kS, ?_⟩
  rw [hblk]
  have := Finset.sum_sdiff (f := x) hST
  push_cast
  linarith

/-! ### fractional coordinates and the direction -/

/-- the set of non-integral coordinates -/
noncomputable def Frac (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => ¬ ∃ k : ℤ, x v = k)

lemma mem_Frac {x : V → ℝ} {v : V} : v ∈ Frac x ↔ ¬ ∃ k : ℤ, x v = k := by simp [Frac]

lemma sum_int (y : V → ℝ) (s : Finset V) (h : ∀ x ∈ s, ∃ k : ℤ, y x = k) :
    ∃ k : ℤ, ∑ x ∈ s, y x = k := by
  refine ⟨∑ x ∈ s, ⌊y x⌋, ?_⟩
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨k, hk⟩ := h x hx
  rw [hk, Int.floor_intCast]

lemma two_le_card_inter (x : V → ℝ) (A : Finset V) (hA : ∃ k : ℤ, ∑ v ∈ A, x v = k) (u : V)
    (huA : u ∈ A) (huF : u ∈ Frac x) : 2 ≤ (A ∩ Frac x).card := by
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < (A ∩ Frac x).card :=
    Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr ⟨huA, huF⟩⟩
  have h1 : (A ∩ Frac x).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hua : u = a := by
    have : u ∈ ({a} : Finset V) := ha ▸ Finset.mem_inter.mpr ⟨huA, huF⟩
    exact Finset.mem_singleton.mp this
  subst hua
  have hrest : ∃ k : ℤ, ∑ v ∈ A.erase u, x v = k := by
    apply sum_int
    intro v hv
    rw [Finset.mem_erase] at hv
    by_contra hnot
    have : v ∈ A ∩ Frac x := Finset.mem_inter.mpr ⟨hv.2, mem_Frac.mpr hnot⟩
    rw [ha, Finset.mem_singleton] at this
    exact hv.1 this
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kR, hkR⟩ := hrest
  apply mem_Frac.mp huF
  refine ⟨kA - kR, ?_⟩
  have := Finset.sum_erase_add A x huA
  push_cast
  linarith

lemma two_mul_card_le (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ)
    (hI : IsIntegerValued ρ) (x : V → ℝ) (hx : x ∈ BasePolyhedron ρ) :
    2 * ((Frac x).image (blk ρ x)).card ≤ (Frac x).card := by
  set Bl := (Frac x).image (blk ρ x) with hBl
  have hdisj : (↑Bl : Set (Finset V)).PairwiseDisjoint (fun A => A ∩ Frac x) := by
    intro A hA A' hA' hne
    simp only [hBl, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hA hA'
    obtain ⟨u, _, rfl⟩ := hA
    obtain ⟨u', _, rfl⟩ := hA'
    rcases blk_eq_or_disjoint ρ x u u' with h | h
    · exact absurd h hne
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left h)
  have hcover : Bl.biUnion (fun A => A ∩ Frac x) = Frac x := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_image, hBl]
    constructor
    · rintro ⟨A, _, _, hw⟩; exact hw
    · intro hw; exact ⟨blk ρ x w, ⟨w, hw, rfl⟩, blk_self ρ x w, hw⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hcover] at hcard
  have : ∑ A ∈ Bl, 2 ≤ ∑ A ∈ Bl, (A ∩ Frac x).card := by
    apply Finset.sum_le_sum
    intro A hA
    rw [hBl, Finset.mem_image] at hA
    obtain ⟨u, hu, rfl⟩ := hA
    exact two_le_card_inter x _ (sum_blk_int ρ hρ hI x hx u) u (blk_self ρ x u) hu
  rw [Finset.sum_const, smul_eq_mul] at this
  omega

theorem exists_dir (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1)
    (hρ2 : SubmodularSetFunction ρ2) (hI1 : IsIntegerValued ρ1) (hI2 : IsIntegerValued ρ2)
    (x : V → ℝ) (hx1 : x ∈ BasePolyhedron ρ1) (hx2 : x ∈ BasePolyhedron ρ2)
    (hF : (Frac x).Nonempty) :
    ∃ d : V → ℝ, d ≠ 0 ∧ (∀ v, v ∉ Frac x → d v = 0) ∧
      (∀ u, ∑ v ∈ blk ρ1 x u, d v = 0) ∧ (∀ u, ∑ v ∈ blk ρ2 x u, d v = 0) := by
  set F := Frac x with hF_def
  set Bl1 := F.image (blk ρ1 x) with hBl1
  set Bl2 := F.image (blk ρ2 x) with hBl2
  obtain ⟨u0, hu0⟩ := hF
  have hA0 : blk ρ2 x u0 ∈ Bl2 := Finset.mem_image_of_mem _ hu0
  set C := Bl1 ∪ Bl2.erase (blk ρ2 x u0) with hC
  have hC_card : C.card < F.card := by
    have h1 : 2 * Bl1.card ≤ F.card := two_mul_card_le ρ1 hρ1 hI1 x hx1
    have h2 : 2 * Bl2.card ≤ F.card := two_mul_card_le ρ2 hρ2 hI2 x hx2
    have h3 : C.card ≤ Bl1.card + (Bl2.erase (blk ρ2 x u0)).card :=
      Finset.card_union_le Bl1 (Bl2.erase (blk ρ2 x u0))
    have h4 := Finset.card_erase_of_mem hA0
    have h5 : 0 < Bl2.card := Finset.card_pos.mpr ⟨_, hA0⟩
    omega
  let M : Matrix ↥C ↥F ℝ := fun A v => if (v : V) ∈ (A : Finset V) then 1 else 0
  have hker : (Matrix.mulVecLin M).ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe]
    exact hC_card
  obtain ⟨e, he, hne⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at he
  let d : V → ℝ := fun v => if h : v ∈ F then e ⟨v, h⟩ else 0
  have hdF : ∀ v, v ∉ F → d v = 0 := fun v hv => by simp [d, hv]
  have hsum : ∀ A : Finset V, ∑ v ∈ A, d v = ∑ v : ↥F, (if (v : V) ∈ A then e v else 0) := by
    intro A
    have h1 : ∑ v : ↥F, (if (v : V) ∈ A then e v else 0) =
        ∑ v ∈ F, (if v ∈ A then d v else 0) := by
      rw [← Finset.sum_coe_sort F (fun v => if v ∈ A then d v else 0)]
      apply Finset.sum_congr rfl
      intro v _
      simp [d, v.2]
    rw [h1, Finset.sum_ite_mem]
    symm
    apply Finset.sum_subset Finset.inter_subset_right
    intro v hvA hvFA
    apply hdF
    intro hvF; exact hvFA (Finset.mem_inter.mpr ⟨hvF, hvA⟩)
  have hC0 : ∀ A ∈ C, ∑ v ∈ A, d v = 0 := by
    intro A hA
    rw [hsum]
    have := congrFun he ⟨A, hA⟩
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M] at this
    simpa [ite_mul, one_mul, zero_mul] using this
  have hpart : ∀ (ρ : Finset V → WithTop ℝ),
      ∑ A ∈ F.image (blk ρ x), ∑ v ∈ A, d v = ∑ v ∈ F, d v := by
    intro ρ
    rw [← sum_over_blocks]
    symm
    apply Finset.sum_subset
    · intro w hw
      simp only [Finset.mem_biUnion, Finset.mem_image, id]
      exact ⟨blk ρ x w, ⟨w, hw, rfl⟩, blk_self ρ x w⟩
    · intro v _ hv; exact hdF v hv
  have hBl1' : ∀ A ∈ Bl1, ∑ v ∈ A, d v = 0 := fun A hA => hC0 A (Finset.mem_union_left _ hA)
  have hBl2' : ∀ A ∈ Bl2, ∑ v ∈ A, d v = 0 := by
    intro A hA
    by_cases hAA : A = blk ρ2 x u0
    · subst hAA
      have h1 := hpart ρ1
      have h2 := hpart ρ2
      rw [← hBl1, Finset.sum_eq_zero hBl1'] at h1
      rw [← hBl2, ← Finset.add_sum_erase _ _ hA, ← h1] at h2
      have h3 : ∑ A' ∈ Bl2.erase (blk ρ2 x u0), ∑ v ∈ A', d v = 0 :=
        Finset.sum_eq_zero (fun A' hA' => hC0 A' (Finset.mem_union_right _ hA'))
      linarith
    · exact hC0 A (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hAA, hA⟩))
  have hall : ∀ (ρ : Finset V → WithTop ℝ), (∀ A ∈ F.image (blk ρ x), ∑ v ∈ A, d v = 0) →
      ∀ u, ∑ v ∈ blk ρ x u, d v = 0 := by
    intro ρ hBl u
    by_cases h : ∃ w ∈ blk ρ x u, w ∈ F
    · obtain ⟨w, hw, hwF⟩ := h
      rw [← blk_eq_of_mem hw]
      exact hBl _ (Finset.mem_image_of_mem _ hwF)
    · push_neg at h
      exact Finset.sum_eq_zero (fun v hv => hdF v (h v hv))
  refine ⟨d, ?_, hdF, hall ρ1 hBl1', hall ρ2 hBl2'⟩
  intro hd
  apply hne
  funext v
  have := congrFun hd v
  simp [d, v.2] at this
  exact this

/-! ### the moving argument -/

/-- the measure: number of tight sets plus number of integral coordinates -/
noncomputable def mu (ρ1 ρ2 : Finset V → WithTop ℝ) (y : V → ℝ) : ℕ :=
  (Finset.univ.filter (fun X => Tight ρ1 y X)).card +
    (Finset.univ.filter (fun X => Tight ρ2 y X)).card +
    (Finset.univ.filter (fun v => ∃ k : ℤ, y v = k)).card

lemma mu_le (ρ1 ρ2 : Finset V → WithTop ℝ) (y : V → ℝ) :
    mu ρ1 ρ2 y ≤ 2 * Fintype.card (Finset V) + Fintype.card V := by
  unfold mu
  have h1 := Finset.card_le_univ (Finset.univ.filter (fun X => Tight ρ1 y X))
  have h2 := Finset.card_le_univ (Finset.univ.filter (fun X => Tight ρ2 y X))
  have h3 := Finset.card_le_univ (Finset.univ.filter (fun v => ∃ k : ℤ, y v = k))
  omega

lemma sum_add_smul (x d : V → ℝ) (t : ℝ) (X : Finset V) :
    ∑ v ∈ X, (x + t • d) v = ∑ v ∈ X, x v + t * ∑ v ∈ X, d v := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

theorem step (ρ1 ρ2 : Finset V → WithTop ℝ) (x : V → ℝ)
    (hx1 : x ∈ BasePolyhedron ρ1) (hx2 : x ∈ BasePolyhedron ρ2)
    (d : V → ℝ) (hd0 : d ≠ 0) (hdF : ∀ v, (∃ k : ℤ, x v = k) → d v = 0)
    (hd1 : ∀ X, Tight ρ1 x X → ∑ v ∈ X, d v = 0) (hd2 : ∀ X, Tight ρ2 x X → ∑ v ∈ X, d v = 0) :
    ∃ t : ℝ, 0 < t ∧ (x + t • d) ∈ BasePolyhedron ρ1 ∧ (x + t • d) ∈ BasePolyhedron ρ2 ∧
      mu ρ1 ρ2 x < mu ρ1 ρ2 (x + t • d) := by
  set Cc : Finset ℝ := (Finset.univ.filter (fun v => d v ≠ 0)).image
    (fun v => if 0 < d v then ((⌈x v⌉ : ℝ) - x v) / d v else ((⌊x v⌋ : ℝ) - x v) / d v) with hCc
  set C1 : Finset ℝ := (Finset.univ.filter (fun X : Finset V => 0 < ∑ v ∈ X, d v ∧ ρ1 X ≠ ⊤)).image
    (fun X => (WithTop.untopD 0 (ρ1 X) - ∑ v ∈ X, x v) / ∑ v ∈ X, d v) with hC1
  set C2 : Finset ℝ := (Finset.univ.filter (fun X : Finset V => 0 < ∑ v ∈ X, d v ∧ ρ2 X ≠ ⊤)).image
    (fun X => (WithTop.untopD 0 (ρ2 X) - ∑ v ∈ X, x v) / ∑ v ∈ X, d v) with hC2
  set Cand := Cc ∪ C1 ∪ C2 with hCand
  have hne : Cand.Nonempty := by
    obtain ⟨v, hv⟩ : ∃ v, d v ≠ 0 := by
      by_contra h; push_neg at h; exact hd0 (funext h)
    exact ⟨_, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)))⟩
  set t := Cand.min' hne with ht
  have htmem : t ∈ Cand := Finset.min'_mem _ _
  have htle : ∀ c ∈ Cand, t ≤ c := fun c hc => Finset.min'_le _ _ hc
  have hfrac : ∀ v, d v ≠ 0 → ¬ ∃ k : ℤ, x v = k := fun v hv h => hv (hdF v h)
  have hCc_pos : ∀ c ∈ Cc, 0 < c := by
    intro c hc
    rw [hCc, Finset.mem_image] at hc
    obtain ⟨v, hv, rfl⟩ := hc
    have hv' : d v ≠ 0 := (Finset.mem_filter.mp hv).2
    have hnot := hfrac v hv'
    split_ifs with hpos
    · apply div_pos _ hpos
      rcases (Int.le_ceil (x v)).lt_or_eq with h | h
      · linarith
      · exact absurd ⟨⌈x v⌉, h⟩ hnot
    · have hneg : d v < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv'
      apply div_pos_of_neg_of_neg _ hneg
      rcases (Int.floor_le (x v)).lt_or_eq with h | h
      · linarith
      · exact absurd ⟨⌊x v⌋, h.symm⟩ hnot
  have hC_pos : ∀ (ρ : Finset V → WithTop ℝ), x ∈ BasePolyhedron ρ →
      (∀ X, Tight ρ x X → ∑ v ∈ X, d v = 0) →
      ∀ X : Finset V, 0 < ∑ v ∈ X, d v → ρ X ≠ ⊤ →
        0 < (WithTop.untopD 0 (ρ X) - ∑ v ∈ X, x v) / ∑ v ∈ X, d v := by
    intro ρ hx hd X hpos hne
    apply div_pos _ hpos
    have h1 := hx.1 X
    rw [← coe_untopD _ hne, WithTop.coe_le_coe] at h1
    rcases h1.lt_or_eq with h | h
    · linarith
    · exfalso
      have : Tight ρ x X := by unfold Tight; rw [← coe_untopD _ hne, h]
      linarith [hd X this]
  have hC1_pos : ∀ c ∈ C1, 0 < c := by
    intro c hc; rw [hC1, Finset.mem_image] at hc
    obtain ⟨X, hX, rfl⟩ := hc
    have := Finset.mem_filter.mp hX
    exact hC_pos ρ1 hx1 hd1 X this.2.1 this.2.2
  have hC2_pos : ∀ c ∈ C2, 0 < c := by
    intro c hc; rw [hC2, Finset.mem_image] at hc
    obtain ⟨X, hX, rfl⟩ := hc
    have := Finset.mem_filter.mp hX
    exact hC_pos ρ2 hx2 hd2 X this.2.1 this.2.2
  have htpos : 0 < t := by
    rcases Finset.mem_union.mp htmem with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hCc_pos _ h
      · exact hC1_pos _ h
    · exact hC2_pos _ h
  have hmem : ∀ (ρ : Finset V → WithTop ℝ), x ∈ BasePolyhedron ρ →
      (∀ X, Tight ρ x X → ∑ v ∈ X, d v = 0) →
      (∀ X : Finset V, 0 < ∑ v ∈ X, d v → ρ X ≠ ⊤ →
        t ≤ (WithTop.untopD 0 (ρ X) - ∑ v ∈ X, x v) / ∑ v ∈ X, d v) →
      (x + t • d) ∈ BasePolyhedron ρ := by
    intro ρ hx hd hle
    refine ⟨fun X => ?_, ?_⟩
    · rw [sum_add_smul]
      by_cases hne : ρ X = ⊤
      · rw [hne]; exact le_top
      rw [← coe_untopD _ hne, WithTop.coe_le_coe]
      have h1 := hx.1 X
      rw [← coe_untopD _ hne, WithTop.coe_le_coe] at h1
      by_cases hpos : 0 < ∑ v ∈ X, d v
      · have := hle X hpos hne
        rw [le_div_iff₀ hpos] at this
        linarith
      · push_neg at hpos
        nlinarith
    · rw [sum_add_smul]
      have hV : Tight ρ x Finset.univ := hx.2
      rw [hd _ hV, mul_zero, add_zero]
      exact hx.2
  set y := x + t • d with hy
  have hT : ∀ (ρ : Finset V → WithTop ℝ), (∀ X, Tight ρ x X → ∑ v ∈ X, d v = 0) →
      ∀ X, Tight ρ x X → Tight ρ y X := by
    intro ρ hd X hX
    unfold Tight at hX ⊢
    rw [hy, sum_add_smul, hd X hX, mul_zero, add_zero]; exact hX
  have hInt : ∀ v, (∃ k : ℤ, x v = k) → ∃ k : ℤ, y v = k := by
    intro v hv
    obtain ⟨k, hk⟩ := hv
    refine ⟨k, ?_⟩
    simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdF v ⟨k, hk⟩, mul_zero, add_zero, hk]
  have hsub1 : (Finset.univ.filter (fun X => Tight ρ1 x X)) ⊆
      (Finset.univ.filter (fun X => Tight ρ1 y X)) := by
    intro X hX; rw [Finset.mem_filter] at hX ⊢; exact ⟨hX.1, hT ρ1 hd1 X hX.2⟩
  have hsub2 : (Finset.univ.filter (fun X => Tight ρ2 x X)) ⊆
      (Finset.univ.filter (fun X => Tight ρ2 y X)) := by
    intro X hX; rw [Finset.mem_filter] at hX ⊢; exact ⟨hX.1, hT ρ2 hd2 X hX.2⟩
  have hsubI : (Finset.univ.filter (fun v => ∃ k : ℤ, x v = k)) ⊆
      (Finset.univ.filter (fun v => ∃ k : ℤ, y v = k)) := by
    intro v hv; rw [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, hInt v hv.2⟩
  refine ⟨t, htpos, hmem ρ1 hx1 hd1 (fun X hpos hne => htle _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, hne⟩))))),
    hmem ρ2 hx2 hd2 (fun X hpos hne => htle _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, hne⟩)))), ?_⟩
  rw [← hy]
  unfold mu
  have c1 := Finset.card_le_card hsub1
  have c2 := Finset.card_le_card hsub2
  have c3 := Finset.card_le_card hsubI
  rcases Finset.mem_union.mp htmem with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rw [hCc, Finset.mem_image] at h
      obtain ⟨v, hv, hvt⟩ := h
      have hv' : d v ≠ 0 := (Finset.mem_filter.mp hv).2
      have hnew : ∃ k : ℤ, y v = k := by
        simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs at hvt with hpos
        · refine ⟨⌈x v⌉, ?_⟩; rw [← hvt, div_mul_cancel₀ _ hv']; ring
        · refine ⟨⌊x v⌋, ?_⟩; rw [← hvt, div_mul_cancel₀ _ hv']; ring
      have hold : ¬ ∃ k : ℤ, x v = k := hfrac v hv'
      have : (Finset.univ.filter (fun v => ∃ k : ℤ, x v = k)).card <
          (Finset.univ.filter (fun v => ∃ k : ℤ, y v = k)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hsubI]
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩,
          fun h => hold (Finset.mem_filter.mp h).2⟩
      omega
    · rw [hC1, Finset.mem_image] at h
      obtain ⟨X, hX, hXt⟩ := h
      obtain ⟨hpos, hne⟩ := (Finset.mem_filter.mp hX).2
      have hnew : Tight ρ1 y X := by
        unfold Tight
        rw [hy, sum_add_smul, ← hXt, div_mul_cancel₀ _ hpos.ne']
        conv_rhs => rw [← coe_untopD _ hne]
        congr 1; ring
      have hold : ¬ Tight ρ1 x X := fun h => by linarith [hd1 X h]
      have : (Finset.univ.filter (fun X => Tight ρ1 x X)).card <
          (Finset.univ.filter (fun X => Tight ρ1 y X)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hsub1]
        exact ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩,
          fun h => hold (Finset.mem_filter.mp h).2⟩
      omega
  · rw [hC2, Finset.mem_image] at h
    obtain ⟨X, hX, hXt⟩ := h
    obtain ⟨hpos, hne⟩ := (Finset.mem_filter.mp hX).2
    have hnew : Tight ρ2 y X := by
      unfold Tight
      rw [hy, sum_add_smul, ← hXt, div_mul_cancel₀ _ hpos.ne']
      conv_rhs => rw [← coe_untopD _ hne]
      congr 1; ring
    have hold : ¬ Tight ρ2 x X := fun h => by linarith [hd2 X h]
    have : (Finset.univ.filter (fun X => Tight ρ2 x X)).card <
        (Finset.univ.filter (fun X => Tight ρ2 y X)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub2]
      exact ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩,
        fun h => hold (Finset.mem_filter.mp h).2⟩
    omega

theorem combo (ρ1 ρ2 : Finset V → WithTop ℝ) (x : V → ℝ)
    (hx1 : x ∈ BasePolyhedron ρ1) (hx2 : x ∈ BasePolyhedron ρ2)
    (d : V → ℝ) (hd0 : d ≠ 0) (hdF : ∀ v, (∃ k : ℤ, x v = k) → d v = 0)
    (hd1 : ∀ X, Tight ρ1 x X → ∑ v ∈ X, d v = 0) (hd2 : ∀ X, Tight ρ2 x X → ∑ v ∈ X, d v = 0)
    (S : Set (V → ℝ))
    (hS : ∀ y, y ∈ BasePolyhedron ρ1 → y ∈ BasePolyhedron ρ2 → mu ρ1 ρ2 x < mu ρ1 ρ2 y →
      y ∈ convexHull ℝ S) :
    x ∈ convexHull ℝ S := by
  obtain ⟨t1, ht1, h11, h12, hm1⟩ := step ρ1 ρ2 x hx1 hx2 d hd0 hdF hd1 hd2
  obtain ⟨t2, ht2, h21, h22, hm2⟩ := step ρ1 ρ2 x hx1 hx2 (-d) (neg_ne_zero.mpr hd0)
    (fun v hv => by simp [hdF v hv]) (fun X hX => by simp [hd1 X hX])
    (fun X hX => by simp [hd2 X hX])
  have hy1 := hS _ h11 h12 hm1
  have hy2 := hS _ h21 h22 hm2
  have hsum : 0 < t1 + t2 := by linarith
  have key : (t2 / (t1 + t2)) • (x + t1 • d) + (t1 / (t1 + t2)) • (x + t2 • (-d)) = x := by
    funext v
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring
  rw [← key]
  exact (convex_convexHull ℝ S) hy1 hy2 (div_nonneg ht2.le hsum.le) (div_nonneg ht1.le hsum.le)
    (by rw [← add_div, add_comm, div_self hsum.ne'])

theorem integral_core (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1)
    (hρ2 : SubmodularSetFunction ρ2) (hI1 : IsIntegerValued ρ1) (hI2 : IsIntegerValued ρ2) :
    ∀ n : ℕ, ∀ x, x ∈ BasePolyhedron ρ1 → x ∈ BasePolyhedron ρ2 →
      (2 * Fintype.card (Finset V) + Fintype.card V) - mu ρ1 ρ2 x ≤ n →
      x ∈ convexHull ℝ (BasePolyhedron ρ1 ∩ BasePolyhedron ρ2 ∩ IntPts) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx1 hx2 hn
    by_cases hF : (Frac x).Nonempty
    · obtain ⟨d, hd0, hdF, hb1, hb2⟩ := exists_dir ρ1 ρ2 hρ1 hρ2 hI1 hI2 x hx1 hx2 hF
      apply combo ρ1 ρ2 x hx1 hx2 d hd0 (fun v hv => hdF v (fun h => mem_Frac.mp h hv))
        (tight_sum_zero ρ1 x d hb1) (tight_sum_zero ρ2 x d hb2)
      intro y hy1 hy2 hmu
      have := mu_le ρ1 ρ2 y
      exact ih ((2 * Fintype.card (Finset V) + Fintype.card V) - mu ρ1 ρ2 y) (by omega) y hy1 hy2
        le_rfl
    · apply subset_convexHull
      refine ⟨⟨hx1, hx2⟩, fun v => ?_⟩
      by_contra h
      exact hF ⟨v, mem_Frac.mpr h⟩

theorem inter_hull_core (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1)
    (hExc2 : ExchangeAxiomB B2) (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) :
    convexHull ℝ (IntEmbed (B1 ∩ B2)) = convexHull ℝ (IntEmbed B1) ∩ convexHull ℝ (IntEmbed B2) := by
  obtain ⟨hs1, hi1, he1⟩ := IRho_props B1 hExc1 hB1ne
  obtain ⟨hs2, hi2, he2⟩ := IRho_props B2 hExc2 hB2ne
  apply Set.Subset.antisymm
  · apply Set.subset_inter
    · exact convexHull_mono (Set.image_mono Set.inter_subset_left)
    · exact convexHull_mono (Set.image_mono Set.inter_subset_right)
  · rintro x ⟨hx1, hx2⟩
    have hP1 : x ∈ BasePolyhedron (IRho B1) := by
      refine convexHull_min ?_ (bp_convex _ hs1.2.1) hx1
      intro z hz; rw [he1] at hz; exact hz.1
    have hP2 : x ∈ BasePolyhedron (IRho B2) := by
      refine convexHull_min ?_ (bp_convex _ hs2.2.1) hx2
      intro z hz; rw [he2] at hz; exact hz.1
    have := integral_core (IRho B1) (IRho B2) hs1 hs2 hi1 hi2 _ x hP1 hP2 le_rfl
    refine convexHull_mono ?_ this
    rintro z ⟨⟨hz1, hz2⟩, hzI⟩
    have h1 : z ∈ IntEmbed B1 := by rw [he1]; exact ⟨hz1, hzI⟩
    have h2 : z ∈ IntEmbed B2 := by rw [he2]; exact ⟨hz2, hzI⟩
    obtain ⟨a, ha, rfl⟩ := h1
    obtain ⟨b, hb, hab⟩ := h2
    have hba : b = a := by
      funext v
      have : (b v : ℝ) = a v := congrFun hab v
      exact_mod_cast this
    rw [hba] at hb
    exact ⟨a, ⟨ha, hb⟩, rfl⟩

end IH
end DiscreteConvex.MConvexSetsB

open DiscreteConvex.MConvexSetsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B1 B2 : Set (V → ℤ))
    (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2) (hB1ne : B1.Nonempty)
    (hB2ne : B2.Nonempty) :
    convexHull ℝ (IntEmbed (B1 ∩ B2)) = convexHull ℝ (IntEmbed B1) ∩ convexHull ℝ (IntEmbed B2) := by
  exact IH.inter_hull_core B1 B2 hExc1 hExc2 hB1ne hB2ne
