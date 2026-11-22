-- Prove2me | solution 1 for CGSpace.not_isQuotientMap_prodMap_id_rat
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:15:16.238852+00:00
-- url     : https://prove2.me/submissions/8d905040-c994-4380-a870-e801f5c8e8a5

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

namespace Sol_CGSpace_not_isQuotientMap_prodMap_id_rat

/-- The irrational numbers `c m = √2 / (|m| + 1)`, which tend to `0` as `|m| → ∞`. -/
noncomputable def c (m : ℤ) : ℝ := Real.sqrt 2 / ((m.natAbs : ℝ) + 1)

theorem c_irrational (m : ℤ) : Irrational (c m) := by
  have h : Irrational (Real.sqrt 2 / ((m.natAbs + 1 : ℕ) : ℝ)) :=
    irrational_sqrt_two.div_natCast (Nat.succ_ne_zero _)
  have e : c m = Real.sqrt 2 / ((m.natAbs + 1 : ℕ) : ℝ) := by
    unfold c
    push_cast
    rfl
  rw [e]
  exact h

theorem c_ne (m : ℤ) (y : ℚ) : (y : ℝ) ≠ c m :=
  fun h => (c_irrational m).ne_rat y h.symm

theorem c_pos (m : ℤ) : 0 < c m := by
  unfold c
  positivity

/-- The fibre over `x` of the open set
`U = ⋃ m : ℤ, {(x, y) | |x - m| < 1/4 ∧ |x - m| < |y - c m|}` of `ℚ × ℚ`. -/
def fib (x : ℚ) : Set ℚ :=
  {y | ∃ m : ℤ, |(x : ℝ) - m| < 1 / 4 ∧ |(x : ℝ) - m| < |(y : ℝ) - c m|}

/-- The fibre of `U` over an integer is all of `ℚ`, because `c m` is irrational. -/
theorem fib_int (m : ℤ) : fib (m : ℚ) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ⟨m, ?_, ?_⟩
  · have e : ((m : ℚ) : ℝ) - (m : ℝ) = 0 := by push_cast; ring
    rw [e, abs_zero]
    norm_num
  · have e : ((m : ℚ) : ℝ) - (m : ℝ) = 0 := by push_cast; ring
    rw [e, abs_zero]
    exact abs_pos.mpr (sub_ne_zero.mpr (c_ne m y))

/-- The set `U` is open in `ℚ × ℚ`. -/
theorem isOpen_U : IsOpen {p : ℚ × ℚ | p.2 ∈ fib p.1} := by
  have e : {p : ℚ × ℚ | p.2 ∈ fib p.1} =
      ⋃ m : ℤ, ({p : ℚ × ℚ | |(p.1 : ℝ) - m| < 1 / 4} ∩
        {p : ℚ × ℚ | |(p.1 : ℝ) - m| < |(p.2 : ℝ) - c m|}) := by
    ext p
    simp only [fib, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  rw [e]
  have h1 : Continuous fun p : ℚ × ℚ => (p.1 : ℝ) := Rat.continuous_coe_real.comp continuous_fst
  have h2 : Continuous fun p : ℚ × ℚ => (p.2 : ℝ) := Rat.continuous_coe_real.comp continuous_snd
  refine isOpen_iUnion fun m => (isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_)
  · exact (h1.sub continuous_const).abs
  · exact continuous_const
  · exact (h1.sub continuous_const).abs
  · exact (h2.sub continuous_const).abs

end Sol_CGSpace_not_isQuotientMap_prodMap_id_rat

open Sol_CGSpace_not_isQuotientMap_prodMap_id_rat in
theorem solution :
    ¬ IsQuotientMap
      (Prod.map (Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n)) (id : ℚ → ℚ)) := by
  intro hq
  -- the fibre function is constant on the integers, hence descends to the quotient
  have hfib : ∀ x x' : ℚ, (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) x x' → fib x = fib x' := by
    rintro x x' ⟨m, n, rfl, rfl⟩
    rw [fib_int, fib_int]
  -- the image `S` of `U`, described through its fibres
  let S : Set (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) :=
    {p | p.2 ∈ Quot.lift fib hfib p.1}
  have hpre : Prod.map (Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n)) (id : ℚ → ℚ) ⁻¹' S =
      {p : ℚ × ℚ | p.2 ∈ fib p.1} := rfl
  -- if the map were a quotient map, `S` would be open
  have hS : IsOpen S := by
    rw [← hq.isOpen_preimage, hpre]
    exact isOpen_U
  have h0 : ((Quot.mk _ (0 : ℚ), (0 : ℚ)) :
      Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) ∈ S := by
    show (0 : ℚ) ∈ fib 0
    have h := fib_int 0
    rw [Int.cast_zero] at h
    rw [h]
    trivial
  -- a basic open box around the point `(f 0, 0)` inside `S`
  obtain ⟨V, W, hV, hW, h0V, h0W, hVW⟩ := isOpen_prod_iff.mp hS _ _ h0
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW 0 h0W
  -- choose `n` with `c n < ε`
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.sqrt 2 / ε)
  have hc0 : 0 < c (n : ℤ) := c_pos _
  have hcε : c (n : ℤ) < ε := by
    have e : c (n : ℤ) = Real.sqrt 2 / ((n : ℝ) + 1) := by
      unfold c
      rw [Int.natAbs_natCast]
    rw [e, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hn
    nlinarith [Real.sqrt_nonneg 2]
  -- the preimage of `V` is an open set of `ℚ` containing the integer `n`
  have hVpre : IsOpen (Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) ⁻¹' V) :=
    hV.preimage continuous_quot_mk
  have hnV : (((n : ℤ) : ℚ)) ∈ Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) ⁻¹' V := by
    show Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) (((n : ℤ) : ℚ)) ∈ V
    have e : Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) (((n : ℤ) : ℚ)) =
        Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) (0 : ℚ) :=
      Quot.sound ⟨(n : ℤ), 0, rfl, by simp⟩
    rw [e]
    exact h0V
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hVpre _ hnV
  -- a rational `d` with `0 < d < min δ (1/4)` and a rational `y` with `c n < y < min (c n + d) ε`
  obtain ⟨d, hd0, hdη⟩ := exists_rat_btwn (lt_min hδ (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨y, hy1, hy2⟩ :=
    exists_rat_btwn (lt_min (lt_add_of_pos_right (c (n : ℤ)) hd0) hcε)
  have hdδ : (d : ℝ) < δ := lt_of_lt_of_le hdη (min_le_left _ _)
  have hd4 : (d : ℝ) < 1 / 4 := lt_of_lt_of_le hdη (min_le_right _ _)
  have hyd : (y : ℝ) < c (n : ℤ) + d := lt_of_lt_of_le hy2 (min_le_left _ _)
  have hyε : (y : ℝ) < ε := lt_of_lt_of_le hy2 (min_le_right _ _)
  have hxcast : (((((n : ℤ) : ℚ) + d : ℚ)) : ℝ) = (n : ℝ) + d := by push_cast; ring
  -- the point `(n + d, y)` lies in the box, hence in `U`
  have hx : Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) (((n : ℤ) : ℚ) + d) ∈ V := by
    apply hδV
    rw [Metric.mem_ball, Rat.dist_eq, hxcast]
    have e : (n : ℝ) + d - (((n : ℤ) : ℚ) : ℝ) = d := by push_cast; ring
    rw [e, abs_of_pos hd0]
    exact hdδ
  have hyW : y ∈ W := by
    apply hεW
    rw [Metric.mem_ball, Rat.dist_eq]
    have e : (y : ℝ) - ((0 : ℚ) : ℝ) = y := by push_cast; ring
    rw [e, abs_of_pos (hc0.trans hy1)]
    exact hyε
  have hmem : ((Quot.mk _ (((n : ℤ) : ℚ) + d), y) :
      Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) ∈ S := hVW ⟨hx, hyW⟩
  have hmem' : y ∈ fib (((n : ℤ) : ℚ) + d) := hmem
  obtain ⟨m, hm1, hm2⟩ := hmem'
  rw [hxcast] at hm1 hm2
  -- but `(n + d, y)` is not in `U`
  by_cases hmn : m = (n : ℤ)
  · subst hmn
    have e : (n : ℝ) + d - (((n : ℕ) : ℤ) : ℝ) = d := by push_cast; ring
    rw [e, abs_of_pos hd0, abs_of_pos (sub_pos.mpr hy1)] at hm2
    linarith
  · have hne : (n : ℤ) - m ≠ 0 := fun h => hmn (sub_eq_zero.mp h).symm
    have h1 : (1 : ℝ) ≤ |(((n : ℤ) - m : ℤ) : ℝ)| := by
      have := Int.one_le_abs hne
      rw [← Int.cast_abs]
      exact_mod_cast this
    have h2 : |(((n : ℤ) - m : ℤ) : ℝ)| ≤ |(n : ℝ) + d - (m : ℝ)| + |(d : ℝ)| := by
      have e : (((n : ℤ) - m : ℤ) : ℝ) = ((n : ℝ) + d - (m : ℝ)) - d := by push_cast; ring
      rw [e]
      exact abs_sub _ _
    rw [abs_of_pos hd0] at h2
    linarith
