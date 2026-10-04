-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.ssqmnew_level_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:16:25.22025+00:00
-- url     : https://prove2.me/submissions/ed3fae0c-801a-4a6b-b7b9-b00622ceaef8

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym

set_option autoImplicit false

open DiscreteConvex.MConvexFunctionsE

namespace SSQMLevel

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem inf_witness {α : Type*} (s : Finset α) (g : α → WithTop ℝ) (c : WithTop ℝ)
    (hc : c ≠ ⊤) (h : s.inf g ≤ c) : ∃ a ∈ s, g a ≤ c := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp at h; exact absurd h hc
  · obtain ⟨a, ha, he⟩ := s.exists_mem_eq_inf hs g
    exact ⟨a, ha, he ▸ h⟩

theorem sub_nonpos_iff (b : WithTop ℝ) (a : ℝ) : b - (a : WithTop ℝ) ≤ 0 ↔ b ≤ (a : WithTop ℝ) := by
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    have e : (b : WithTop ℝ) - (a : WithTop ℝ) = ((b - a : ℝ) : WithTop ℝ) := by norm_cast
    rw [e, ← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

theorem inf_witness_lt {α : Type*} (s : Finset α) (g : α → WithTop ℝ) (c : WithTop ℝ)
    (h : s.inf g < c) : ∃ a ∈ s, g a < c := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp at h
  · obtain ⟨a, ha, he⟩ := s.exists_mem_eq_inf hs g
    exact ⟨a, ha, he ▸ h⟩

theorem sub_neg_iff' (b : WithTop ℝ) (a : ℝ) : b - (a : WithTop ℝ) < 0 ↔ b < (a : WithTop ℝ) := by
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    have e : (b : WithTop ℝ) - (a : WithTop ℝ) = ((b - a : ℝ) : WithTop ℝ) := by norm_cast
    rw [e, ← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_lt_coe]
    constructor <;> intro h <;> linarith

theorem sub_eq_zero_iff' (b : WithTop ℝ) (a : ℝ) : b - (a : WithTop ℝ) = 0 ↔ b = (a : WithTop ℝ) := by
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    have e : (b : WithTop ℝ) - (a : WithTop ℝ) = ((b - a : ℝ) : WithTop ℝ) := by norm_cast
    rw [e, ← WithTop.coe_zero, WithTop.coe_inj, WithTop.coe_inj]
    constructor <;> intro h <;> linarith

theorem mem_pos {x y : V → ℤ} {u : V} : u ∈ SuppPos x y ↔ y u < x u := by
  simp [SuppPos]

theorem mem_neg {x y : V → ℤ} {v : V} : v ∈ SuppNeg x y ↔ x v < y v := by
  simp [SuppNeg]

theorem md_le (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) (u v : V) (hu : u ∈ SuppPos x y)
    (hv : v ∈ SuppNeg x y) :
    MinDown f x y ≤ f (fun w => x w - CharVec u w + CharVec v w) :=
  (Finset.inf_le hu).trans (Finset.inf_le hv)

/-- ℓ¹ distance. -/
def d1 (x y : V → ℤ) : ℤ := ∑ w, |x w - y w|

theorem d1_nonneg (x y : V → ℤ) : 0 ≤ d1 x y := Finset.sum_nonneg (fun w _ => abs_nonneg _)

theorem step_dist (x y : V → ℤ) (u v : V) (hu : y u < x u) (hv : x v < y v) :
    d1 x (fun w => y w + CharVec u w - CharVec v w) < d1 x y := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    by_cases h1 : w = u
    · subst h1
      simp only [if_true, if_neg huv]
      rcases abs_cases (x w - y w) with ⟨h, _⟩ | ⟨h, _⟩ <;>
        rcases abs_cases (x w - (y w + 1 - 0)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · by_cases h2 : w = v
      · subst h2
        simp only [if_neg h1, if_true]
        rcases abs_cases (x w - y w) with ⟨h, _⟩ | ⟨h, _⟩ <;>
          rcases abs_cases (x w - (y w + 0 - 1)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
      · simp [h1, h2]
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [CharVec, if_true, if_neg huv]
    rcases abs_cases (x u - y u) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (x u - (y u + 1 - 0)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega

theorem shift_pos {x y : V → ℤ} {u v u' : V} (hv : x v < y v)
    (h : u' ∈ SuppPos x (fun w => y w + CharVec u w - CharVec v w)) : u' ∈ SuppPos x y := by
  rw [mem_pos] at h ⊢
  simp only [CharVec] at h
  by_cases h1 : u' = u <;> by_cases h2 : u' = v <;> simp [h1, h2] at h <;> subst_vars <;> omega

theorem shift_neg {x y : V → ℤ} {u v v' : V} (hu : y u < x u)
    (h : v' ∈ SuppNeg x (fun w => y w + CharVec u w - CharVec v w)) : v' ∈ SuppNeg x y := by
  rw [mem_neg] at h ⊢
  simp only [CharVec] at h
  by_cases h1 : v' = u <;> by_cases h2 : v' = v <;> simp [h1, h2] at h <;> subst_vars <;> omega

/-- The induction for (6.96) ⇒ (6.97). -/
theorem sym_to_down (f : (V → ℤ) → WithTop ℝ)
    (h2 : ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → max (f x) (f y) > MinDownSym f x y)
    (x : V → ℤ) (hx : x ∈ DomZ f) :
    ∀ n : ℕ, ∀ y ∈ DomZ f, d1 x y < n → f x > f y → f x > MinDown f x y := by
  intro n
  induction n with
  | zero => intro y _ hd; exact absurd hd (by have := d1_nonneg x y; push_cast; omega)
  | succ n ih =>
    intro y hy hd hgt
    have hmax : max (f x) (f y) = f x := max_eq_left hgt.le
    have hs := h2 x hx y hy (ne_of_gt hgt)
    rw [hmax] at hs
    obtain ⟨u, hu, hu'⟩ := inf_witness_lt _ _ _ hs
    obtain ⟨v, hv, hv'⟩ := inf_witness_lt _ _ _ hu'
    rcases le_total (f (fun w => x w - CharVec u w + CharVec v w))
        (f (fun w => y w + CharVec u w - CharVec v w)) with hm | hm
    · rw [min_eq_left hm] at hv'
      exact lt_of_le_of_lt (md_le f x y u v hu hv) hv'
    · rw [min_eq_right hm] at hv'
      set y' : V → ℤ := fun w => y w + CharVec u w - CharVec v w with hy'
      by_cases hxy' : x = y'
      · rw [← hxy'] at hv'; exact absurd hv' (lt_irrefl _)
      · have hy'dom : y' ∈ DomZ f := ne_top_of_lt hv'
        have hd' : d1 x y' < n := by
          have := step_dist x y u v (mem_pos.mp hu) (mem_neg.mp hv)
          rw [← hy'] at this
          push_cast at hd ⊢; omega
        have ih' := ih y' hy'dom hd' hv'
        refine lt_of_le_of_lt ?_ ih'
        refine Finset.le_inf (fun u' hu'' => Finset.le_inf (fun v' hv'' => ?_))
        exact md_le f x y u' v' (shift_pos (mem_neg.mp hv) hu'') (shift_neg (mem_pos.mp hu) hv'')

end SSQMLevel

open SSQMLevel in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    [SSQMNeW f,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → max (f x) (f y) > MinDownSym f x y,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x > f y → f x > MinDown f x y].TFAE := by
  have ex : ∀ (z : V → ℤ) (u v : V), (fun w => z w + CharVec v w - CharVec u w) =
      (fun w => z w - CharVec u w + CharVec v w) := by intro z u v; funext w; ring
  tfae_have 1 → 2 := by
    intro h x hx y hy hxy
    obtain ⟨u, hu, v, hv, hd⟩ := h x hx y hy hxy
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy
    have key : MinDownSym f x y ≤ min (f (fun w => x w - CharVec u w + CharVec v w))
        (f (fun w => y w + CharVec u w - CharVec v w)) :=
      (Finset.inf_le hu).trans (Finset.inf_le (f := fun v => min
        (f (fun w => x w - CharVec u w + CharVec v w))
        (f (fun w => y w + CharVec u w - CharVec v w))) hv)
    refine lt_of_le_of_lt key ?_
    unfold DeltaF at hd
    rw [ex x u v, ← ha, ← hb, sub_neg_iff', sub_neg_iff', sub_eq_zero_iff', sub_eq_zero_iff',
      ha, hb] at hd
    rcases hd with hd | hd | ⟨hd1, hd2⟩
    · exact (min_le_left _ _).trans_lt (hd.trans_le (le_max_left _ _))
    · exact (min_le_right _ _).trans_lt (hd.trans_le (le_max_right _ _))
    · rw [hd1, hd2]; exact min_lt_max.mpr hxy
  tfae_have 2 → 3 := by
    intro h x hx y hy hgt
    exact sym_to_down f h x hx ((d1 x y).toNat + 1) y hy (by
      have := d1_nonneg x y; push_cast; omega) hgt
  tfae_have 3 → 1 := by
    intro h x hx y hy hxy
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · have hm := h y hy x hx hlt
      obtain ⟨u, hu, hu'⟩ := inf_witness_lt _ _ _ hm
      obtain ⟨v, hv, hv'⟩ := inf_witness_lt _ _ _ hu'
      refine ⟨v, ?_, u, ?_, Or.inr (Or.inl ?_)⟩
      · rw [mem_pos]; exact mem_neg.mp hv
      · rw [mem_neg]; exact mem_pos.mp hu
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy
      unfold DeltaF
      rw [← hb, sub_neg_iff', hb, ex y u v]
      exact hv'
    · have hm := h x hx y hy hlt
      obtain ⟨u, hu, hu'⟩ := inf_witness_lt _ _ _ hm
      obtain ⟨v, hv, hv'⟩ := inf_witness_lt _ _ _ hu'
      refine ⟨u, hu, v, hv, Or.inl ?_⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
      unfold DeltaF
      rw [← ha, sub_neg_iff', ha, ex x u v]
      exact hv'
  tfae_finish

#print axioms solution
