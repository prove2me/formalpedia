-- Prove2me | solution 1 for BigDataNV.Reg.nvCost_sigmaAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:45:01.923479+00:00
-- url     : https://prove2.me/submissions/513ae2e1-57e6-4bd2-8552-e58c2da0068b

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

set_option autoImplicit false

namespace D436016aAux

lemma posPart_convex (s : ℝ) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun a : ℝ => max (s * a + c) 0) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hαβ
  simp only [smul_eq_mul]
  apply max_le
  · have h1 : s * (α * x + β * y) + c = α * (s * x + c) + β * (s * y + c) := by
      have : c = (α + β) * c := by rw [hαβ, one_mul]
      linarith [this]
    rw [h1]
    have := mul_le_mul_of_nonneg_left (le_max_left (s * x + c) 0) hα
    have := mul_le_mul_of_nonneg_left (le_max_left (s * y + c) 0) hβ
    linarith
  · have := mul_nonneg hα (le_max_right (s * x + c) 0)
    have := mul_nonneg hβ (le_max_right (s * y + c) 0)
    linarith

lemma nv_lip (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (x y d : ℝ) :
    |BigDataNV.Reg.nvCost b h x d - BigDataNV.Reg.nvCost b h y d| ≤ max b h * |x - y| := by
  unfold BigDataNV.Reg.nvCost InventoryControl.newsboyLoss
  have hbm : b ≤ max b h := le_max_left _ _
  have hhm : h ≤ max b h := le_max_right _ _
  rcases le_total x d with hx | hx <;> rcases le_total y d with hy | hy <;>
  rcases le_total x y with hxy | hxy <;>
  simp only [max_eq_left, max_eq_right, sub_nonneg, sub_nonpos, hx, hy] <;>
  first
  | (rw [abs_le]; constructor <;>
      (rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)] <;> nlinarith) )
  | (rw [abs_le]; constructor <;>
      (rw [abs_of_nonpos (by linarith : x - y ≤ 0)] <;> nlinarith) )
  | (rw [abs_le]; constructor <;>
      (rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)] <;> nlinarith) )

end D436016aAux

namespace BigDataNV.Reg
end BigDataNV.Reg

open BigDataNV.Reg in
theorem solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    {X : Type*} (F : Set (X → ℝ)) :
    StabGen.RKHS.SigmaAdmissible F (nvCost b h) (max b h) := by
  refine ⟨le_trans hb.le (le_max_left _ _), ?_, ?_⟩
  · intro d
    have h1 := (D436016aAux.posPart_convex 1 (-d)).smul hh.le
    have h2 := (D436016aAux.posPart_convex (-1) d).smul hb.le
    have h3 := h1.add h2
    have e : (fun a : ℝ => nvCost b h a d) =
        ((fun x : ℝ => h • max (1 * x + -d) 0) + fun x : ℝ => b • max (-1 * x + d) 0) := by
      funext a
      simp only [nvCost, InventoryControl.newsboyLoss, Pi.add_apply, smul_eq_mul]
      have e1 : a - d = 1 * a + -d := by ring
      have e2 : d - a = -1 * a + d := by ring
      rw [e1, e2]
    rw [e]
    exact h3
  · intro x _ y _ d
    exact D436016aAux.nv_lip b h hb hh x y d
