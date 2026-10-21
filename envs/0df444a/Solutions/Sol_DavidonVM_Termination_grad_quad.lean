-- Prove2me | solution 1 for DavidonVM.Termination.grad_quad
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:20:33.186779+00:00
-- url     : https://prove2.me/submissions/c18a3ea4-55c8-4eb7-b43f-dfc096c70908

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

set_option autoImplicit false

section DvSec
open Matrix DavidonVM.Termination

namespace Dv
variable {n : ℕ}

theorem symm_dot {A : Mat n} (hA : A.IsSymm) (v w : Vec n) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (A *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]

theorem rank1 (u w : Vec n) : vecMulVec u u *ᵥ w = (u ⬝ᵥ w) • u := by
  rw [Matrix.vecMulVec_mulVec]
  simp

theorem update_apply (H : Mat n) (a : ℝ) (u w : Vec n) :
    (H + a • vecMulVec u u) *ᵥ w = H *ᵥ w + (a * (u ⬝ᵥ w)) • u := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, rank1, smul_smul]

theorem update_symm {H : Mat n} (hH : H.IsSymm) (a : ℝ) (u : Vec n) :
    (H + a • vecMulVec u u).IsSymm := by
  have h1 : (vecMulVec u u).IsSymm := by
    unfold Matrix.IsSymm
    ext i j
    simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
  exact hH.add (h1.smul a)

theorem grad_sub (G : Mat n) (ξ x y : Vec n) :
    grad G ξ y - grad G ξ x = G *ᵥ (y - x) := by
  unfold grad
  rw [← Matrix.mulVec_sub]
  congr 1
  abel

theorem sec_core (H : Mat n) (hH : H.IsSymm) (g gp : Vec n)
    (hne : gp ⬝ᵥ (H *ᵥ g) ≠ gp ⬝ᵥ (H *ᵥ gp)) :
    (H + ((gp ⬝ᵥ (H *ᵥ g)) - (gp ⬝ᵥ (H *ᵥ gp)))⁻¹ • vecMulVec (H *ᵥ gp) (H *ᵥ gp)) *ᵥ (gp - g)
      = -(H *ᵥ g) := by
  rw [update_apply, Matrix.mulVec_sub]
  have h1 : (H *ᵥ gp) ⬝ᵥ (gp - g) = (gp ⬝ᵥ (H *ᵥ gp)) - (gp ⬝ᵥ (H *ᵥ g)) := by
    rw [symm_dot hH, Matrix.mulVec_sub, dotProduct_sub]
  have hne' : (gp ⬝ᵥ (H *ᵥ g)) - (gp ⬝ᵥ (H *ᵥ gp)) ≠ 0 := sub_ne_zero.2 hne
  have hc : ((gp ⬝ᵥ (H *ᵥ g)) - (gp ⬝ᵥ (H *ᵥ gp)))⁻¹ *
      ((gp ⬝ᵥ (H *ᵥ gp)) - (gp ⬝ᵥ (H *ᵥ g))) = -1 := by
    field_simp
    ring
  rw [h1, hc, neg_one_smul]
  abel

end Dv
end DvSec

open Matrix DavidonVM.Termination

theorem solution {n : ℕ} (G : Mat n) (hG : G.IsSymm) (ξ : Vec n) (c : ℝ) (x v : Vec n) :
    HasDerivAt (fun t : ℝ => quad G ξ c (x + t • v)) (grad G ξ x ⬝ᵥ v) 0 := by
  set a : Vec n := x - ξ with ha
  have h1 : a ⬝ᵥ (G *ᵥ v) = (G *ᵥ a) ⬝ᵥ v := (Dv.symm_dot hG a v).symm
  have h2 : v ⬝ᵥ (G *ᵥ a) = (G *ᵥ a) ⬝ᵥ v := dotProduct_comm _ _
  have hf : (fun t : ℝ => quad G ξ c (x + t • v)) =
      fun t : ℝ => ((1 / 2 : ℝ) * (a ⬝ᵥ (G *ᵥ a)) + c) + t * ((G *ᵥ a) ⬝ᵥ v)
        + t ^ 2 * ((1 / 2 : ℝ) * (v ⬝ᵥ (G *ᵥ v))) := by
    funext t
    unfold quad
    have e : x + t • v - ξ = a + t • v := by rw [ha]; abel
    rw [e]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, h1, h2]
    ring
  rw [hf]
  have hg : grad G ξ x = G *ᵥ a := rfl
  rw [hg]
  have := (((hasDerivAt_const (0 : ℝ) ((1 / 2 : ℝ) * (a ⬝ᵥ (G *ᵥ a)) + c)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const ((G *ᵥ a) ⬝ᵥ v))).add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const ((1 / 2 : ℝ) * (v ⬝ᵥ (G *ᵥ v)))))
  refine this.congr_deriv ?_
  simp
