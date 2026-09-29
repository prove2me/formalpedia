-- Prove2me | solution 1 for Freiman.middle_limit_realized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:52:06.34139+00:00
-- url     : https://prove2.me/submissions/d884f5ca-58ff-46c7-80e4-522206e37d40

import Definitions.Def_Freiman_middleRoots
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_prefix
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Freiman

private theorem constant_three : cfValue (fun _ : ℕ => (3 : ℕ+)) = middleZeta := by
  have hc := cf_convergence (fun _ : ℕ => (3 : ℕ+))
  have hpos := hc.2.2.1
  have heq := hc.2.2.2.2
  have hden : (3 : ℝ) + cfValue (fun _ : ℕ => (3 : ℕ+)) ≠ 0 := by linarith
  have hquad : cfValue (fun _ : ℕ => (3 : ℕ+)) *
      (3 + cfValue (fun _ : ℕ => (3 : ℕ+))) = 1 := by
    apply (eq_div_iff hden).mp
    simpa using heq
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  unfold middleZeta
  nlinarith

private theorem finite_with_three (w : List ℕ+) :
    cfValue (fun n : ℕ => w.getD n 3) = prefixEval w middleZeta := by
  have hp := cfValue_prefix (fun n : ℕ => w.getD n 3) w.length
  have hm : (List.range w.length).map (fun n : ℕ => w.getD n 3) = w := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h2, Option.getD_some]
  have ht : (fun k : ℕ => w.getD (w.length + k) 3) = (fun _ : ℕ => (3 : ℕ+)) := by
    funext k
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ w.length+k)]
  simpa only [hm, ht, constant_three] using hp

private def center_with_three (c : MiddleCore) (z : ℤ) : ℕ+ :=
  if z = 0 then 4 else if z < 0 then c.left.getD (-z-1).toNat 3
  else c.right.getD (z-1).toNat 3

private theorem center_zero (c : MiddleCore) : center_with_three c 0 = 4 := by
  simp [center_with_three]

private theorem center_left (c : MiddleCore) (n : ℕ) :
    center_with_three c (-(n : ℤ)-1) = c.left.getD n 3 := by
  have hn : -(n : ℤ)-1 < 0 := by omega
  simp [center_with_three, ne_of_lt hn, hn, show -(-(n : ℤ)-1)-1 = n by omega]

private theorem center_right (c : MiddleCore) (n : ℕ) :
    center_with_three c ((n : ℤ)+1) = c.right.getD n 3 := by
  have hn : 0 < (n : ℤ)+1 := by omega
  simp [center_with_three, ne_of_gt hn, not_lt_of_ge (le_of_lt hn)]

theorem solution :
    ∀ c : MiddleCore, middleRealized c (middleLimitValue c) := by
  intro c
  refine ⟨center_with_three c, ?_, ?_⟩
  · refine ⟨center_zero c, ?_, ?_, ?_, ?_⟩
    · intro n hn
      rw [center_left]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    · intro n hn
      rw [center_right]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    · intro n hn
      rw [center_left]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn]
    · intro n hn
      rw [center_right]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn]
  · unfold localValue middleLimitValue
    simp only [center_zero, zero_sub, zero_add, center_left, center_right,
      finite_with_three]
    norm_num

#print axioms solution
