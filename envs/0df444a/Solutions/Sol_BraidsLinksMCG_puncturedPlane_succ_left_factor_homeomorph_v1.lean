-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_succ_left_factor_homeomorph_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:47:36.214984+00:00
-- url     : https://prove2.me/submissions/8493f1ba-f768-436f-bc81-7bf60883ce43

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option autoImplicit false

namespace P30b39e5f

noncomputable def fwd (c x : ℝ) : ℝ :=
  x + 2 * (max (x - c) 0) ^ 2 / (1 - 2 * max (x - c) 0)

noncomputable def bwd (c y : ℝ) : ℝ :=
  y - 2 * (max (y - c) 0) ^ 2 / (1 + 2 * max (y - c) 0)

lemma fwd_of_le {c x : ℝ} (hx : x ≤ c) : fwd c x = x := by
  simp [fwd, max_eq_right (sub_nonpos.mpr hx)]

lemma bwd_of_le {c y : ℝ} (hy : y ≤ c) : bwd c y = y := by
  simp [bwd, max_eq_right (sub_nonpos.mpr hy)]

lemma fwd_of_gt {c x : ℝ} (hx : c < x) (hx2 : x < c + 1 / 2) :
    fwd c x = c + (x - c) / (1 - 2 * (x - c)) := by
  have h1 : max (x - c) 0 = x - c := max_eq_left (by linarith)
  have h2 : (1 - 2 * (x - c)) ≠ 0 := (by linarith : (0:ℝ) < 1 - 2 * (x - c)).ne'
  unfold fwd
  rw [h1]
  field_simp
  ring

lemma bwd_of_gt {c y : ℝ} (hy : c < y) :
    bwd c y = c + (y - c) / (1 + 2 * (y - c)) := by
  have h1 : max (y - c) 0 = y - c := max_eq_left (by linarith)
  have h2 : (1 + 2 * (y - c)) ≠ 0 := (by linarith : (0:ℝ) < 1 + 2 * (y - c)).ne'
  unfold bwd
  rw [h1]
  field_simp
  ring

lemma fwd_gt_c {c x : ℝ} (hx : c < x) (hx2 : x < c + 1 / 2) : c < fwd c x := by
  rw [fwd_of_gt hx hx2]
  have : 0 < (x - c) / (1 - 2 * (x - c)) := div_pos (by linarith) (by linarith)
  linarith

lemma bwd_gt_c {c y : ℝ} (hy : c < y) : c < bwd c y ∧ bwd c y < c + 1 / 2 := by
  rw [bwd_of_gt hy]
  have hpos : (0:ℝ) < 1 + 2 * (y - c) := by linarith
  have h1 : 0 < (y - c) / (1 + 2 * (y - c)) := div_pos (by linarith) hpos
  have h2 : (y - c) / (1 + 2 * (y - c)) < 1 / 2 := by
    rw [div_lt_iff₀ hpos]; linarith
  constructor <;> linarith

lemma bwd_lt (c y : ℝ) : bwd c y < c + 1 / 2 := by
  rcases le_or_gt y c with h | h
  · rw [bwd_of_le h]; linarith
  · exact (bwd_gt_c h).2

lemma fwd_eq_of_le {c x : ℝ} (hx2 : x < c + 1 / 2) (h : fwd c x ≤ c) : fwd c x = x := by
  rcases le_or_gt x c with h' | h'
  · exact fwd_of_le h'
  · exact absurd h (not_le.mpr (fwd_gt_c h' hx2))

lemma bwd_eq_of_le {c y : ℝ} (h : bwd c y ≤ c) : bwd c y = y := by
  rcases le_or_gt y c with h' | h'
  · exact bwd_of_le h'
  · exact absurd h (not_le.mpr (bwd_gt_c h').1)

lemma bwd_fwd {c x : ℝ} (hx2 : x < c + 1 / 2) : bwd c (fwd c x) = x := by
  rcases le_or_gt x c with h | h
  · rw [fwd_of_le h, bwd_of_le h]
  · rw [bwd_of_gt (fwd_gt_c h hx2), fwd_of_gt h hx2]
    have hd : (0:ℝ) < 1 - 2 * (x - c) := by linarith
    have e : 1 + 2 * (c + (x - c) / (1 - 2 * (x - c)) - c) = 1 / (1 - 2 * (x - c)) := by
      field_simp; ring
    rw [e]
    have hd' : (1 - 2 * (x - c)) ≠ 0 := hd.ne'
    have h3 : c + (x - c) / (1 - 2 * (x - c)) - c = (x - c) / (1 - 2 * (x - c)) := by ring
    rw [h3, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hd']
    ring

lemma fwd_bwd (c y : ℝ) : fwd c (bwd c y) = y := by
  rcases le_or_gt y c with h | h
  · rw [bwd_of_le h, fwd_of_le h]
  · obtain ⟨h1, h2⟩ := bwd_gt_c h
    rw [fwd_of_gt h1 h2, bwd_of_gt h]
    have hd : (0:ℝ) < 1 + 2 * (y - c) := by linarith
    have e : 1 - 2 * (c + (y - c) / (1 + 2 * (y - c)) - c) = 1 / (1 + 2 * (y - c)) := by
      field_simp; ring
    rw [e]
    field_simp
    ring

lemma cont_fwd (c : ℝ) (S : Set ℝ) (hS : ∀ x ∈ S, x < c + 1 / 2) :
    Continuous (fun x : S => fwd c x.1) := by
  unfold fwd
  refine Continuous.add (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) ?_)
  intro x
  have hx := hS x.1 x.2
  have : max (x.1 - c) 0 < 1 / 2 := max_lt (by linarith) (by norm_num)
  have : (0:ℝ) < 1 - 2 * max (x.1 - c) 0 := by linarith
  exact this.ne'

lemma cont_bwd (c : ℝ) : Continuous (fun y : ℝ => bwd c y) := by
  unfold bwd
  refine Continuous.sub (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) ?_)
  intro y
  have : (0:ℝ) ≤ max (y - c) 0 := le_max_right _ _
  have : (0:ℝ) < 1 + 2 * max (y - c) 0 := by linarith
  exact this.ne'

open BraidsLinksMCG

lemma re_mk (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp
lemma im_mk (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp

abbrev SL (n : ℕ) : Set (PuncturedPlane (n + 1)) :=
  {z : PuncturedPlane (n + 1) | z.1.re < ((n : ℕ) + 1 : ℝ)}

lemma toFun_mem (n : ℕ) (z : ↥(SL n)) :
    ∀ j : Fin n, ((fwd ((n : ℝ) + 1 / 2) z.1.1.re : ℂ) + (z.1.1.im : ℂ) * Complex.I)
      ≠ ((j : ℕ) + 1 : ℂ) := by
  intro j hj
  have hre : fwd ((n : ℝ) + 1 / 2) z.1.1.re = ((j : ℕ) : ℝ) + 1 := by
    have := congrArg Complex.re hj
    rw [re_mk] at this
    rw [this]; simp
  have him : z.1.1.im = 0 := by
    have := congrArg Complex.im hj
    rw [im_mk] at this
    rw [this]; simp
  have hz : z.1.1.re < (n : ℝ) + 1 / 2 + 1 / 2 := by
    have := z.2; simp only [SL, Set.mem_ofPred_eq] at this; linarith
  have hj' : ((j : ℕ) : ℝ) + 1 ≤ n := by
    have := j.isLt; exact_mod_cast this
  have hle : fwd ((n : ℝ) + 1 / 2) z.1.1.re ≤ (n : ℝ) + 1 / 2 := by rw [hre]; linarith
  have e := fwd_eq_of_le hz hle
  rw [e] at hre
  apply z.1.2 (Fin.castSucc j)
  apply Complex.ext
  · simp [hre]
  · simp [him]

lemma invFun_mem (n : ℕ) (w : PuncturedPlane n) :
    ∀ j : Fin (n + 1), ((bwd ((n : ℝ) + 1 / 2) w.1.re : ℂ) + (w.1.im : ℂ) * Complex.I)
      ≠ ((j : ℕ) + 1 : ℂ) := by
  intro j hj
  have hre : bwd ((n : ℝ) + 1 / 2) w.1.re = ((j : ℕ) : ℝ) + 1 := by
    have := congrArg Complex.re hj
    rw [re_mk] at this
    rw [this]; simp
  have him : w.1.im = 0 := by
    have := congrArg Complex.im hj
    rw [im_mk] at this
    rw [this]; simp
  have hlt := bwd_lt ((n : ℝ) + 1 / 2) w.1.re
  have hjn : (j : ℕ) < n := by
    by_contra hc
    have : (n : ℝ) ≤ (j : ℕ) := by exact_mod_cast (not_lt.mp hc)
    linarith
  have hj' : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hle : bwd ((n : ℝ) + 1 / 2) w.1.re ≤ (n : ℝ) + 1 / 2 := by rw [hre]; linarith
  have e := bwd_eq_of_le hle
  rw [e] at hre
  apply w.2 ⟨j, hjn⟩
  apply Complex.ext
  · simp [hre]
  · simp [him]

noncomputable def homeo (n : ℕ) : ↥(SL n) ≃ₜ PuncturedPlane n where
  toFun z := ⟨(fwd ((n : ℝ) + 1 / 2) z.1.1.re : ℂ) + (z.1.1.im : ℂ) * Complex.I, toFun_mem n z⟩
  invFun w := ⟨⟨(bwd ((n : ℝ) + 1 / 2) w.1.re : ℂ) + (w.1.im : ℂ) * Complex.I,
      invFun_mem n w⟩, by
    simp only [SL, Set.mem_ofPred_eq]
    rw [re_mk]
    have := bwd_lt ((n : ℝ) + 1 / 2) w.1.re
    linarith⟩
  left_inv z := by
    have hz : z.1.1.re < (n : ℝ) + 1 / 2 + 1 / 2 := by
      have := z.2; simp only [SL, Set.mem_ofPred_eq] at this; linarith
    apply Subtype.ext; apply Subtype.ext
    apply Complex.ext
    · simp only [re_mk, im_mk]
      exact bwd_fwd hz
    · simp only [re_mk, im_mk]
  right_inv w := by
    apply Subtype.ext
    apply Complex.ext
    · simp only [re_mk, im_mk]
      exact fwd_bwd _ _
    · simp only [re_mk, im_mk]
  continuous_toFun := by
    have h1 : Continuous (fun z : ↥(SL n) => fwd ((n : ℝ) + 1 / 2) z.1.1.re) := by
      have hc := cont_fwd ((n : ℝ) + 1 / 2) {x | x < (n : ℝ) + 1 / 2 + 1 / 2}
        (fun x hx => hx)
      have hm : Continuous (fun z : ↥(SL n) =>
          (⟨z.1.1.re, by
            have := z.2; simp only [SL, Set.mem_ofPred_eq] at this
            show z.1.1.re < (n : ℝ) + 1 / 2 + 1 / 2
            linarith⟩ : {x : ℝ | x < (n : ℝ) + 1 / 2 + 1 / 2})) := by
        apply Continuous.subtype_mk
        fun_prop
      exact hc.comp hm
    apply Continuous.subtype_mk
    have h2 : Continuous (fun z : ↥(SL n) => z.1.1.im) := by fun_prop
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have h1 : Continuous (fun w : PuncturedPlane n => bwd ((n : ℝ) + 1 / 2) w.1.re) :=
      (cont_bwd _).comp (by fun_prop)
    fun_prop

end P30b39e5f

open BraidsLinksMCG in
theorem solution (n : ℕ)
    (A : Bool → Set (PuncturedPlane (n + 1)))
    (hfalse :
      A Bool.false =
        {z : PuncturedPlane (n + 1) |
          z.1.re < ((n : ℕ) + 1 : ℝ)}) :
    ∃ (c : ↥(A Bool.false))
      (h : ↥(A Bool.false) ≃ₜ PuncturedPlane n)
      (z : PuncturedPlane n),
      h c = z ∧ z.1.re = (n : ℝ) + 1 ∧ z.1.im = 1 := by
  let e : ↥(A Bool.false) ≃ₜ PuncturedPlane n :=
    (Homeomorph.setCongr hfalse).trans (P30b39e5f.homeo n)
  let z0 : PuncturedPlane n := ⟨((n : ℝ) + 1 : ℝ) + ((1 : ℝ) : ℂ) * Complex.I, by
    intro j hj
    have := congrArg Complex.im hj
    simp at this⟩
  refine ⟨e.symm z0, e, z0, e.apply_symm_apply z0, ?_, ?_⟩
  · simp [z0]
  · simp [z0]
