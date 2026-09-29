-- Prove2me | solution 1 for Devaney.exists_subinterval_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T14:43:16.453404+00:00
-- url     : https://prove2.me/submissions/348dded3-56f9-4ee2-af1b-0c933f604c37

import Mathlib
import Definitions.Def_Devaney_sarkovskii

open Set Function

namespace Shk

/-! ## Part 1: covering of intervals, fixed points, and the loop lemma -/

/-- `Cov f a b c d` says that the image under `f` of the closed interval with endpoints
`a, b` contains the closed interval with endpoints `c, d`. -/
def Cov (f : ℝ → ℝ) (a b c d : ℝ) : Prop := uIcc c d ⊆ f '' uIcc a b

theorem cov_of_subset {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (h : uIcc c d ⊆ uIcc (f a) (f b)) : Cov f a b c d :=
  h.trans (intermediate_value_uIcc hf.continuousOn)

/-- The basic covering criterion: if `c` and `d` both lie between `f a` and `f b`, then
`[a,b]` covers `[c,d]`. -/
theorem cov_of_mem {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (hc : c ∈ uIcc (f a) (f b)) (hd : d ∈ uIcc (f a) (f b)) : Cov f a b c d :=
  cov_of_subset hf (uIcc_subset_uIcc hc hd)

theorem Cov.mono {f : ℝ → ℝ} {a b c d c' d' : ℝ} (h : Cov f a b c d)
    (h' : uIcc c' d' ⊆ uIcc c d) : Cov f a b c' d' := h'.trans h

/-- A closed interval that covers itself contains a fixed point. -/
theorem exists_fixed_of_cov_self {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : Cov f a b a b) : ∃ z ∈ uIcc a b, f z = z := by
  obtain ⟨p, hp, hfp⟩ := h (left_mem_uIcc)
  obtain ⟨q, hq, hfq⟩ := h (right_mem_uIcc)
  have hcont : Continuous (fun x : ℝ => f x - x) := hf.sub continuous_id
  have h0 : (0:ℝ) ∈ uIcc (f p - p) (f q - q) := by
    rw [hfp, hfq, mem_uIcc]
    rcases mem_uIcc.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases mem_uIcc.1 hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      first
        | (left; constructor <;> linarith)
        | (right; constructor <;> linarith)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (f := fun x : ℝ => f x - x)
    hcont.continuousOn h0
  have hz0' : f z - z = 0 := hz0
  exact ⟨z, uIcc_subset_uIcc hp hq hz, by linarith⟩

/-- Auxiliary form of the exact-subinterval lemma, with the two chosen preimages ordered. -/
private theorem subint_aux {f : ℝ → ℝ} (hf : Continuous f) {p q c d : ℝ} (hpq : p < q)
    (hp : f p = c) (hq : f q = d) (hcd : c ≠ d) :
    ∃ u v : ℝ, p ≤ u ∧ u < v ∧ v ≤ q ∧ f '' uIcc u v = uIcc c d := by
  classical
  obtain ⟨u, hpu, huq, hfu, hmax⟩ :
      ∃ u : ℝ, p ≤ u ∧ u ≤ q ∧ f u = c ∧ ∀ y, p ≤ y → y ≤ q → f y = c → y ≤ u := by
    have hcl : IsClosed (Icc p q ∩ f ⁻¹' {c}) :=
      isClosed_Icc.inter (isClosed_singleton.preimage hf)
    have hne : (Icc p q ∩ f ⁻¹' {c}).Nonempty := ⟨p, ⟨le_refl p, hpq.le⟩, hp⟩
    have hbdd : BddAbove (Icc p q ∩ f ⁻¹' {c}) := ⟨q, fun x hx => hx.1.2⟩
    have hmem := hcl.csSup_mem hne hbdd
    exact ⟨_, hmem.1.1, hmem.1.2, hmem.2, fun y h1 h2 h3 => le_csSup hbdd ⟨⟨h1, h2⟩, h3⟩⟩
  have huq' : u < q := by
    rcases eq_or_lt_of_le huq with h | h
    · exact absurd (by rw [← hfu, h, hq] : c = d) hcd
    · exact h
  obtain ⟨v, huv, hvq, hfv, hmin⟩ :
      ∃ v : ℝ, u ≤ v ∧ v ≤ q ∧ f v = d ∧ ∀ y, u ≤ y → y ≤ q → f y = d → v ≤ y := by
    have hcl : IsClosed (Icc u q ∩ f ⁻¹' {d}) :=
      isClosed_Icc.inter (isClosed_singleton.preimage hf)
    have hne : (Icc u q ∩ f ⁻¹' {d}).Nonempty := ⟨q, ⟨huq, le_refl q⟩, hq⟩
    have hbdd : BddBelow (Icc u q ∩ f ⁻¹' {d}) := ⟨u, fun x hx => hx.1.1⟩
    have hmem := hcl.csInf_mem hne hbdd
    exact ⟨_, hmem.1.1, hmem.1.2, hmem.2, fun y h1 h2 h3 => csInf_le hbdd ⟨⟨h1, h2⟩, h3⟩⟩
  have huv' : u < v := by
    rcases eq_or_lt_of_le huv with h | h
    · exact absurd (by rw [← hfu, h, hfv] : c = d) hcd
    · exact h
  refine ⟨u, v, hpu, huv', hvq, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [uIcc_of_le huv'.le] at hx
    by_contra hfx
    have key : (d ∈ uIcc c (f x) ∧ d ≠ f x) ∨ (c ∈ uIcc (f x) d ∧ c ≠ f x) := by
      rw [mem_uIcc] at hfx
      push_neg at hfx
      rcases le_total c d with hle | hle
      · rcases lt_or_ge (f x) c with h1 | h1
        · exact Or.inr ⟨mem_uIcc.2 (Or.inl ⟨h1.le, hle⟩), by linarith⟩
        · have h2 : d < f x := by
            by_contra h3; push_neg at h3
            exact absurd (hfx.1 h1) (by linarith)
          exact Or.inl ⟨mem_uIcc.2 (Or.inl ⟨hle, h2.le⟩), by linarith⟩
      · rcases lt_or_ge (f x) d with h1 | h1
        · exact Or.inl ⟨mem_uIcc.2 (Or.inr ⟨h1.le, hle⟩), by linarith⟩
        · have h2 : c < f x := by
            by_contra h3; push_neg at h3
            exact absurd (hfx.2 h1) (by linarith)
          exact Or.inr ⟨mem_uIcc.2 (Or.inr ⟨hle, h2.le⟩), by linarith⟩
    rcases key with ⟨hd1, hd2⟩ | ⟨hc1, hc2⟩
    · have himg : d ∈ f '' uIcc u x :=
        intermediate_value_uIcc hf.continuousOn (by rw [hfu]; exact hd1)
      obtain ⟨y, hy, hfy⟩ := himg
      rw [uIcc_of_le hx.1] at hy
      have hvy : v ≤ y := hmin y hy.1 (le_trans (le_trans hy.2 hx.2) hvq) hfy
      have hxv : x = v := le_antisymm hx.2 (le_trans hvy hy.2)
      exact hd2 (by rw [hxv, hfv])
    · have himg : c ∈ f '' uIcc x v :=
        intermediate_value_uIcc hf.continuousOn (by rw [hfv]; exact hc1)
      obtain ⟨y, hy, hfy⟩ := himg
      rw [uIcc_of_le hx.2] at hy
      have hyu : y ≤ u := hmax y (le_trans hpu (le_trans hx.1 hy.1)) (le_trans hy.2 hvq) hfy
      have hxu : x = u := le_antisymm (le_trans hy.1 hyu) hx.1
      exact hc2 (by rw [hxu, hfu])
  · have := intermediate_value_uIcc (f := f) (a := u) (b := v) hf.continuousOn
    rwa [hfu, hfv] at this

/-- **Exact subinterval lemma.**  If `[a,b]` covers `[c,d]`, then `[a,b]` contains a closed
subinterval mapped by `f` exactly *onto* `[c,d]`. -/
theorem exists_exact_subinterval {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (h : Cov f a b c d) :
    ∃ u v : ℝ, uIcc u v ⊆ uIcc a b ∧ f '' uIcc u v = uIcc c d := by
  obtain ⟨p, hp, hfp⟩ := h (left_mem_uIcc)
  obtain ⟨q, hq, hfq⟩ := h (right_mem_uIcc)
  rcases eq_or_ne c d with rfl | hcd
  · exact ⟨p, p, by simpa using hp, by simp [hfp]⟩
  · have hpq : p ≠ q := by rintro rfl; exact hcd (hfp ▸ hfq ▸ rfl)
    have main : ∀ p' q' : ℝ, p' < q' → p' ∈ uIcc a b → q' ∈ uIcc a b →
        ∀ c' d' : ℝ, f p' = c' → f q' = d' → c' ≠ d' →
        ∃ u v : ℝ, uIcc u v ⊆ uIcc a b ∧ f '' uIcc u v = uIcc c' d' := by
      intro p' q' hlt hp' hq' c' d' h1 h2 h3
      obtain ⟨u, v, hu1, hu2, hu3, hu4⟩ := subint_aux hf hlt h1 h2 h3
      refine ⟨u, v, ?_, hu4⟩
      have hsub : uIcc u v ⊆ uIcc p' q' :=
        uIcc_subset_uIcc (mem_uIcc.2 (Or.inl ⟨hu1, le_trans hu2.le hu3⟩))
          (mem_uIcc.2 (Or.inl ⟨le_trans hu1 hu2.le, hu3⟩))
      exact hsub.trans (uIcc_subset_uIcc hp' hq')
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact main p q hlt hp hq c d hfp hfq hcd
    · obtain ⟨u, v, h1, h2⟩ := main q p hlt hq hp d c hfq hfp (Ne.symm hcd)
      exact ⟨u, v, h1, by rw [h2, uIcc_comm]⟩

end Shk

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (a b c d : ℝ)
    (h : Devaney.Covers f (Set.uIcc a b) (Set.uIcc c d)) :
    ∃ u v : ℝ, Set.uIcc u v ⊆ Set.uIcc a b ∧ f '' Set.uIcc u v = Set.uIcc c d :=
  Shk.exists_exact_subinterval hf h
