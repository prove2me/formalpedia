-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_nonnegative_additive_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:29:54.925373+00:00
-- url     : https://prove2.me/submissions/6c6f6a4e-de7c-4ab1-b78a-3840ad157ec6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
/-- A continuous additive function on nonnegative real heights is linear. -/
theorem solution
    (g : ℝ → ℝ)
    (hzero : g 0 = 0)
    (hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      g (x + y) = g x + g y)
    (hcont : ContinuousAt g 0) :
    ∀ x : ℝ, 0 ≤ x → g x = x * g 1 := by
  let G : ℝ → ℝ := fun x => if 0 ≤ x then g x else -g (-x)
  have hGadd : ∀ x y : ℝ, G (x + y) = G x + G y := by
    intro x y
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hxy : 0 ≤ x + y := add_nonneg hx hy
        simpa only [G, if_pos hxy, if_pos hx, if_pos hy] using
          hadd x y hx hy
      · have hny : 0 ≤ -y := by linarith
        by_cases hxy : 0 ≤ x + y
        · have h := hadd (x + y) (-y) hxy hny
          have he : x + y + -y = x := by ring
          rw [he] at h
          simp only [G, if_pos hxy, if_pos hx, if_neg hy]
          linarith
        · have hnxy : 0 ≤ -(x + y) := by linarith
          have h := hadd x (-(x + y)) hx hnxy
          have he : x + -(x + y) = -y := by ring
          rw [he] at h
          simp only [G, if_neg hxy, if_pos hx, if_neg hy]
          linarith
    · have hnx : 0 ≤ -x := by linarith
      by_cases hy : 0 ≤ y
      · by_cases hxy : 0 ≤ x + y
        · have h := hadd (x + y) (-x) hxy hnx
          have he : x + y + -x = y := by ring
          rw [he] at h
          simp only [G, if_pos hxy, if_neg hx, if_pos hy]
          linarith
        · have hnxy : 0 ≤ -(x + y) := by linarith
          have h := hadd y (-(x + y)) hy hnxy
          have he : y + -(x + y) = -x := by ring
          rw [he] at h
          simp only [G, if_neg hxy, if_neg hx, if_pos hy]
          linarith
      · have hny : 0 ≤ -y := by linarith
        have hxy : ¬ 0 ≤ x + y := by linarith
        have h := hadd (-x) (-y) hnx hny
        have he : -x + -y = -(x + y) := by ring
        rw [he] at h
        simp only [G, if_neg hxy, if_neg hx, if_neg hy]
        linarith
  have hGformula : G = (fun x : ℝ => g (max x 0) - g (max (-x) 0)) := by
    funext x
    by_cases hx : 0 ≤ x
    · have hxp : max x 0 = x := max_eq_left hx
      have hxn : max (-x) 0 = 0 := max_eq_right (by linarith)
      simp only [G, if_pos hx, hxp, hxn, hzero, sub_zero]
    · have hxp : max x 0 = 0 := max_eq_right (by linarith)
      have hxn : max (-x) 0 = -x := max_eq_left (by linarith)
      simp only [G, if_neg hx, hxp, hxn, hzero, zero_sub]
  have hpcont : ContinuousAt (fun x : ℝ => g (max x 0)) 0 := by
    have hm : ContinuousAt (fun x : ℝ => max x 0) 0 := by fun_prop
    have hc : ContinuousAt g (max (0 : ℝ) 0) := by simpa using hcont
    have hcc := ContinuousAt.comp (f := (fun x : ℝ => max x 0)) hc hm
    simpa only [Function.comp_def, max_self] using hcc
  have hncont : ContinuousAt (fun x : ℝ => g (max (-x) 0)) 0 := by
    have hm : ContinuousAt (fun x : ℝ => max (-x) 0) 0 := by fun_prop
    have hc : ContinuousAt g (max (-(0 : ℝ)) 0) := by simpa using hcont
    have hcc := ContinuousAt.comp (f := (fun x : ℝ => max (-x) 0)) hc hm
    simpa only [Function.comp_def, neg_zero, max_self] using hcc
  have hGcont : ContinuousAt G 0 := by
    rw [hGformula]
    change ContinuousAt ((fun x : ℝ => g (max x 0)) -
      (fun x : ℝ => g (max (-x) 0))) 0
    exact hpcont.sub hncont
  let φ : ℝ →+ ℝ := {
    toFun := G
    map_zero' := by simp [G, hzero]
    map_add' := hGadd
  }
  have hφcont : Continuous (φ : ℝ → ℝ) := by
    apply continuous_of_continuousAt_zero φ
    change ContinuousAt G 0
    exact hGcont
  intro x hx
  have hlin := map_real_smul φ hφcont x (1 : ℝ)
  have hGx : G x = g x := if_pos hx
  have hG1 : G 1 = g 1 := if_pos (by norm_num : (0 : ℝ) ≤ 1)
  change G (x • (1 : ℝ)) = x • G 1 at hlin
  simpa only [smul_eq_mul, mul_one, hGx, hG1] using hlin
