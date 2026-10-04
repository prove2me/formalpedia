-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_succ_cover_halfplanes_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:29:48.202153+00:00
-- url     : https://prove2.me/submissions/54975ed9-1191-4203-81bf-2e78b48aa9a4

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option autoImplicit false

namespace P9979

/-- A half-plane `{re < c}` (if `s = -1`) or `{c < re}` (if `s = 1`) is the injective continuous
image of `ℂ`, so removing a countable set keeps it path-connected. -/
lemma halfplane_diff_aux (c s : ℝ) (hs : s ≠ 0) (S : Set ℂ) (hS : S.Countable) :
    IsPathConnected ({z : ℂ | 0 < s * (z.re - c)} \ S) := by
  let f : ℂ → ℂ := fun w => ((c + s * Real.exp w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I
  have hre : ∀ w, (f w).re = c + s * Real.exp w.re := by
    intro w
    simp only [f, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : ∀ w, (f w).im = w.im := by
    intro w
    simp only [f, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hfc : Continuous f := by
    simp only [f]
    fun_prop
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Complex.re hab
    have h2 := congrArg Complex.im hab
    rw [hre, hre] at h1
    rw [him, him] at h2
    have h3 : Real.exp a.re = Real.exp b.re := by
      have := mul_left_cancel₀ hs (by linarith : s * Real.exp a.re = s * Real.exp b.re)
      exact this
    exact Complex.ext (Real.exp_injective h3) h2
  have hcnt : (f ⁻¹' S).Countable := hS.preimage hinj
  have hpc : IsPathConnected (f ⁻¹' S)ᶜ :=
    hcnt.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have himg : f '' (f ⁻¹' S)ᶜ = {z : ℂ | 0 < s * (z.re - c)} \ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, hw⟩
      show 0 < s * ((f w).re - c)
      rw [hre]
      have : s * (c + s * Real.exp w.re - c) = s * s * Real.exp w.re := by ring
      rw [this]
      exact mul_pos (mul_self_pos.mpr hs) (Real.exp_pos _)
    · rintro ⟨hz, hzS⟩
      have hz' : 0 < s * (z.re - c) := hz
      have hpos : 0 < (z.re - c) / s := by
        rcases lt_or_gt_of_ne hs with h | h
        · exact div_pos_of_neg_of_neg (by nlinarith) h
        · exact div_pos (by nlinarith) h
      refine ⟨⟨Real.log ((z.re - c) / s), z.im⟩, ?_, ?_⟩
      · have hfz : f ⟨Real.log ((z.re - c) / s), z.im⟩ = z := by
          apply Complex.ext
          · rw [hre]
            show c + s * Real.exp (Real.log ((z.re - c) / s)) = z.re
            rw [Real.exp_log hpos]
            field_simp
            ring
          · rw [him]
        show f _ ∉ S
        rw [hfz]; exact hzS
      · apply Complex.ext
        · rw [hre]
          show c + s * Real.exp (Real.log ((z.re - c) / s)) = z.re
          rw [Real.exp_log hpos]
          field_simp
          ring
        · rw [him]
  rw [← himg]
  exact hpc.image hfc

lemma halfplane_lt_diff (c : ℝ) (S : Set ℂ) (hS : S.Countable) :
    IsPathConnected ({z : ℂ | z.re < c} \ S) := by
  have := halfplane_diff_aux c (-1) (by norm_num) S hS
  have e : {z : ℂ | 0 < -1 * (z.re - c)} = {z : ℂ | z.re < c} := by
    ext z; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rwa [e] at this

lemma halfplane_gt_diff (c : ℝ) (S : Set ℂ) (hS : S.Countable) :
    IsPathConnected ({z : ℂ | c < z.re} \ S) := by
  have := halfplane_diff_aux c 1 (by norm_num) S hS
  have e : {z : ℂ | 0 < 1 * (z.re - c)} = {z : ℂ | c < z.re} := by
    ext z; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rwa [e] at this

end P9979

open BraidsLinksMCG in
theorem solution (n : ℕ) :
    ∃ (A : Bool → Set (PuncturedPlane (n + 1)))
      (x₀ : PuncturedPlane (n + 1)),
      A Bool.false =
          {z : PuncturedPlane (n + 1) |
            z.1.re < ((n : ℕ) + 1 : ℝ)} ∧
      A Bool.true =
          {z : PuncturedPlane (n + 1) |
            ((n : ℕ) : ℝ) + 1 / 2 < z.1.re} ∧
      (∀ i, x₀ ∈ A i) ∧
      (∀ i, IsOpen (A i)) ∧
      (∀ i, IsPathConnected (A i)) ∧
      (⋃ i, A i) = Set.univ ∧
      (∀ i j, IsPathConnected (A i ∩ A j)) := by
  set L : Set (PuncturedPlane (n + 1)) := {z | z.1.re < ((n : ℕ) + 1 : ℝ)} with hL
  set R : Set (PuncturedPlane (n + 1)) := {z | ((n : ℕ) : ℝ) + 1 / 2 < z.1.re} with hR
  let P : Set ℂ := Set.range (fun j : Fin (n + 1) => (((j : ℕ) : ℂ) + 1))
  have hP : P.Countable := (Set.finite_range _).countable
  have hval : ∀ (T : Set ℂ), (Subtype.val '' {z : PuncturedPlane (n + 1) | z.1 ∈ T}) = T \ P := by
    intro T
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hw, ?_⟩
      rintro ⟨j, hj⟩
      exact w.2 j hj.symm
    · rintro ⟨hz, hzP⟩
      refine ⟨⟨z, fun j hj => hzP ⟨j, hj.symm⟩⟩, hz, rfl⟩
  have hcont : Continuous (fun z : PuncturedPlane (n + 1) => z.1.re) :=
    Complex.continuous_re.comp continuous_subtype_val
  -- the base point
  let x₀ : PuncturedPlane (n + 1) :=
    ⟨((n : ℕ) : ℂ) + 3 / 4 + Complex.I, fun j hj => by
      have := congrArg Complex.im hj
      simp at this⟩
  have hx₀re : x₀.1.re = (n : ℝ) + 3 / 4 := by
    show (((n : ℕ) : ℂ) + 3 / 4 + Complex.I).re = _
    simp
  have hind : Topology.IsInducing (Subtype.val : PuncturedPlane (n + 1) → ℂ) := ⟨rfl⟩
  have hLpc : IsPathConnected L := by
    rw [hind.isPathConnected_iff]
    have := hval {z : ℂ | z.re < ((n : ℕ) + 1 : ℝ)}
    simp only [Set.mem_setOf_eq] at this
    rw [hL, this]
    exact P9979.halfplane_lt_diff _ P hP
  have hRpc : IsPathConnected R := by
    rw [hind.isPathConnected_iff]
    have := hval {z : ℂ | ((n : ℕ) : ℝ) + 1 / 2 < z.re}
    simp only [Set.mem_setOf_eq] at this
    rw [hR, this]
    exact P9979.halfplane_gt_diff _ P hP
  have hLRpc : IsPathConnected (L ∩ R) := by
    rw [hind.isPathConnected_iff]
    have e : L ∩ R = {z : PuncturedPlane (n + 1) | z.1 ∈
        {w : ℂ | w.re < ((n : ℕ) + 1 : ℝ) ∧ ((n : ℕ) : ℝ) + 1 / 2 < w.re}} := by
      ext z; simp [hL, hR]
    have hS : {w : ℂ | w.re < ((n : ℕ) + 1 : ℝ) ∧ ((n : ℕ) : ℝ) + 1 / 2 < w.re} \ P =
        {w : ℂ | w.re < ((n : ℕ) + 1 : ℝ) ∧ ((n : ℕ) : ℝ) + 1 / 2 < w.re} := by
      ext w
      refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
      obtain ⟨h1, h2⟩ := hw
      rintro ⟨j, rfl⟩
      have hre : ((((j : ℕ) : ℂ) + 1)).re = ((j : ℕ) : ℝ) + 1 := by simp
      rw [hre] at h1 h2
      have hj : (j : ℕ) < n := by exact_mod_cast (by linarith : ((j : ℕ) : ℝ) < n)
      have hj' : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hj
      linarith
    rw [e, hval, hS]
    apply Convex.isPathConnected
    · have h1 : Convex ℝ {w : ℂ | w.re < ((n : ℕ) + 1 : ℝ)} := convex_halfSpace_re_lt _
      have h2 : Convex ℝ {w : ℂ | ((n : ℕ) : ℝ) + 1 / 2 < w.re} := convex_halfSpace_re_gt _
      exact h1.inter h2
    · refine ⟨x₀.1, ?_, ?_⟩
      · rw [hx₀re]; linarith
      · rw [hx₀re]; linarith
  refine ⟨fun b => cond b R L, x₀, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i
    · show x₀.1.re < ((n : ℕ) + 1 : ℝ)
      rw [hx₀re]; linarith
    · show ((n : ℕ) : ℝ) + 1 / 2 < x₀.1.re
      rw [hx₀re]; linarith
  · intro i
    cases i
    · exact isOpen_lt hcont continuous_const
    · exact isOpen_lt continuous_const hcont
  · intro i
    cases i
    · exact hLpc
    · exact hRpc
  · apply Set.eq_univ_of_forall
    intro z
    rw [Set.mem_iUnion]
    rcases lt_or_ge z.1.re ((n : ℕ) + 1 : ℝ) with h | h
    · exact ⟨Bool.false, h⟩
    · refine ⟨Bool.true, ?_⟩
      show ((n : ℕ) : ℝ) + 1 / 2 < z.1.re
      linarith
  · intro i j
    cases i <;> cases j
    · simpa using hLpc
    · exact hLRpc
    · simpa [Set.inter_comm] using hLRpc
    · simpa using hRpc
