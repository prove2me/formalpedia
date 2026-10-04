-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.quasi_m_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:17:20.09977+00:00
-- url     : https://prove2.me/submissions/df0e2b6b-254c-4401-be93-be44936556b4

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym

set_option autoImplicit false

open DiscreteConvex.MConvexFunctionsE

namespace QMwLevel

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

/-- The induction for (6.93) ⇒ (6.94). -/
theorem sym_to_down (f : (V → ℤ) → WithTop ℝ)
    (h2 : ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → max (f x) (f y) ≥ MinDownSym f x y)
    (x : V → ℤ) (hx : x ∈ DomZ f) :
    ∀ n : ℕ, ∀ y ∈ DomZ f, d1 x y < n → x ≠ y → f x ≥ f y → f x ≥ MinDown f x y := by
  intro n
  induction n with
  | zero => intro y _ hd; exact absurd hd (by have := d1_nonneg x y; push_cast; omega)
  | succ n ih =>
    intro y hy hd hxy hge
    have hmax : max (f x) (f y) = f x := max_eq_left hge
    have hs := h2 x hx y hy hxy
    rw [hmax] at hs
    obtain ⟨u, hu, hu'⟩ := inf_witness _ _ _ hx hs
    obtain ⟨v, hv, hv'⟩ := inf_witness _ _ _ hx hu'
    rcases le_total (f (fun w => x w - CharVec u w + CharVec v w))
        (f (fun w => y w + CharVec u w - CharVec v w)) with hm | hm
    · rw [min_eq_left hm] at hv'
      exact (md_le f x y u v hu hv).trans hv'
    · rw [min_eq_right hm] at hv'
      set y' : V → ℤ := fun w => y w + CharVec u w - CharVec v w with hy'
      by_cases hxy' : x = y'
      · have : (fun w => x w - CharVec u w + CharVec v w) = y := by
          funext w; rw [hxy']; simp only [hy']; ring
        have := md_le f x y u v hu hv
        rw [‹(fun w => x w - CharVec u w + CharVec v w) = y›] at this
        exact this.trans hge
      · have hy'dom : y' ∈ DomZ f := ne_top_of_le_ne_top hx hv'
        have hd' : d1 x y' < n := by
          have := step_dist x y u v (mem_pos.mp hu) (mem_neg.mp hv)
          rw [← hy'] at this
          push_cast at hd ⊢; omega
        have ih' := ih y' hy'dom hd' hxy' hv'
        refine le_trans ?_ ih'
        refine Finset.le_inf (fun u' hu'' => Finset.le_inf (fun v' hv'' => ?_))
        exact md_le f x y u' v' (shift_pos (mem_neg.mp hv) hu'') (shift_neg (mem_pos.mp hu) hv'')

end QMwLevel

open QMwLevel in
theorem qmw_tfae {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    [QMw f,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → max (f x) (f y) ≥ MinDownSym f x y,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → f x ≥ f y → f x ≥ MinDown f x y].TFAE := by
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
    refine key.trans ?_
    rcases hd with hd | hd
    · unfold DeltaF at hd
      rw [← ha, sub_nonpos_iff] at hd
      have e : (fun w => x w + CharVec v w - CharVec u w) =
          (fun w => x w - CharVec u w + CharVec v w) := by funext w; ring
      rw [e, ha] at hd
      exact (min_le_left _ _).trans (hd.trans (le_max_left _ _))
    · unfold DeltaF at hd
      rw [← hb, sub_nonpos_iff, hb] at hd
      exact (min_le_right _ _).trans (hd.trans (le_max_right _ _))
  tfae_have 2 → 3 := by
    intro h x hx y hy hxy hge
    exact sym_to_down f h x hx ((d1 x y).toNat + 1) y hy (by
      have := d1_nonneg x y; push_cast; omega) hxy hge
  tfae_have 3 → 1 := by
    intro h x hx y hy hxy
    rcases le_total (f y) (f x) with hle | hle
    · have hm := h x hx y hy hxy hle
      obtain ⟨u, hu, hu'⟩ := inf_witness _ _ _ hx hm
      obtain ⟨v, hv, hv'⟩ := inf_witness _ _ _ hx hu'
      refine ⟨u, hu, v, hv, Or.inl ?_⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
      unfold DeltaF
      rw [← ha, sub_nonpos_iff, ha]
      have e : (fun w => x w + CharVec v w - CharVec u w) =
          (fun w => x w - CharVec u w + CharVec v w) := by funext w; ring
      rw [e]; exact hv'
    · have hm := h y hy x hx (Ne.symm hxy) hle
      obtain ⟨u, hu, hu'⟩ := inf_witness _ _ _ hy hm
      obtain ⟨v, hv, hv'⟩ := inf_witness _ _ _ hy hu'
      refine ⟨v, ?_, u, ?_, Or.inr ?_⟩
      · rw [mem_pos]; exact mem_neg.mp hv
      · rw [mem_neg]; exact mem_pos.mp hu
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy
      unfold DeltaF
      rw [← hb, sub_nonpos_iff, hb]
      have e : (fun w => y w + CharVec v w - CharVec u w) =
          (fun w => y w - CharVec u w + CharVec v w) := by funext w; ring
      rw [e]; exact hv'
  tfae_finish


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
theorem ssq_tfae {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
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


open QMwLevel SSQMLevel in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    (QMw f → ∀ x ∈ DomZ f,
        ((∀ y : V → ℤ, y ≠ x → f x < f y) ↔ ∀ u v : V, u ≠ v → DeltaF f x v u > 0)) ∧
    (SSQMNeW f → ∀ x ∈ DomZ f,
        ((∀ y : V → ℤ, f x ≤ f y) ↔ ∀ u v : V, DeltaF f x v u ≥ 0)) := by
  have ex : ∀ (z : V → ℤ) (u v : V), (fun w => z w + CharVec v w - CharVec u w) =
      (fun w => z w - CharVec u w + CharVec v w) := by intro z u v; funext w; ring
  constructor
  · intro hq x hx
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
    have h3 := ((qmw_tfae f).out 0 2).mp hq
    constructor
    · intro h u v huv
      have hne : (fun w => x w + CharVec v w - CharVec u w) ≠ x := by
        intro he
        have := congrFun he v
        simp [CharVec, huv.symm] at this
      have hlt := h _ hne
      unfold DeltaF
      rw [← ha] at hlt ⊢
      by_contra hc
      rw [not_lt, QMwLevel.sub_nonpos_iff] at hc
      exact absurd (lt_of_lt_of_le hlt hc) (lt_irrefl _)
    · intro h y hyx
      by_contra hc
      rw [not_lt] at hc
      have hy : y ∈ DomZ f := ne_top_of_le_ne_top hx hc
      have hm := h3 x hx y hy (Ne.symm hyx) hc
      obtain ⟨u, hu, hu'⟩ := QMwLevel.inf_witness _ _ _ hx hm
      obtain ⟨v, hv, hv'⟩ := QMwLevel.inf_witness _ _ _ hx hu'
      have huv : u ≠ v := by
        rintro rfl
        have h1 := QMwLevel.mem_pos.mp hu
        have h2 := QMwLevel.mem_neg.mp hv
        omega
      have hd := h u v huv
      unfold DeltaF at hd
      rw [ex x u v, ← ha] at hd
      rw [← ha] at hv'
      have := (QMwLevel.sub_nonpos_iff _ a).mpr hv'
      exact absurd (lt_of_lt_of_le hd this) (lt_irrefl _)
  · intro hs x hx
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hx
    have h3 := ((ssq_tfae f).out 0 2).mp hs
    constructor
    · intro h u v
      unfold DeltaF
      rw [← ha]
      by_contra hc
      rw [not_le, SSQMLevel.sub_neg_iff'] at hc
      have := h (fun w => x w + CharVec v w - CharVec u w)
      rw [← ha] at this
      exact absurd (lt_of_lt_of_le hc this) (lt_irrefl _)
    · intro h y
      by_contra hc
      rw [not_le] at hc
      have hy : y ∈ DomZ f := ne_top_of_lt hc
      have hm := h3 x hx y hy hc
      obtain ⟨u, hu, hu'⟩ := SSQMLevel.inf_witness_lt _ _ _ hm
      obtain ⟨v, hv, hv'⟩ := SSQMLevel.inf_witness_lt _ _ _ hu'
      have hd := h u v
      unfold DeltaF at hd
      rw [ex x u v, ← ha] at hd
      rw [← ha] at hv'
      have := (SSQMLevel.sub_neg_iff' _ a).mpr hv'
      exact absurd (lt_of_lt_of_le this hd) (lt_irrefl _)

#print axioms solution
