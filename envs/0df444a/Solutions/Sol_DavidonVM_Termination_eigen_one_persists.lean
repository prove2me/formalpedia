-- Prove2me | solution 1 for DavidonVM.Termination.eigen_one_persists
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:20:30.984823+00:00
-- url     : https://prove2.me/submissions/de70761c-120c-4791-b3f3-4c7fedb5512c

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

theorem solution {n : ℕ} (G : Mat n) (hG : G.IsSymm) (ξ : Vec n) (H : Mat n)
    (hH : H.IsSymm) (a : ℝ) (x : Vec n) :
    let g : Vec n := grad G ξ x
    let xp : Vec n := x - H *ᵥ g
    let gp : Vec n := grad G ξ xp
    let Hp : Mat n := H + a • vecMulVec (H *ᵥ gp) (H *ᵥ gp)
    ∀ u : Vec n, H *ᵥ (G *ᵥ u) = u → Hp *ᵥ (G *ᵥ u) = u := by
  intro g xp gp Hp u hu
  have hgp : gp = g - G *ᵥ (H *ᵥ g) := by
    have h := Dv.grad_sub G ξ x xp
    have e : xp - x = -(H *ᵥ g) := by simp only [xp]; abel
    rw [e, Matrix.mulVec_neg] at h
    calc gp = g + (gp - g) := by abel
      _ = g - G *ᵥ (H *ᵥ g) := by rw [show gp - g = -(G *ᵥ (H *ᵥ g)) from h]; abel
  have h1 : (H *ᵥ gp) ⬝ᵥ (G *ᵥ u) = 0 := by
    rw [Dv.symm_dot hH, hu, hgp, sub_dotProduct, Dv.symm_dot hG, Dv.symm_dot hH, hu, sub_self]
  rw [Dv.update_apply, h1, mul_zero, zero_smul, add_zero, hu]
