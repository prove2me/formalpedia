-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.qmw_level_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:15:24.154526+00:00
-- url     : https://prove2.me/submissions/01269324-b867-4935-9d0f-065004caa47f

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
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
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
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

#print axioms solution
