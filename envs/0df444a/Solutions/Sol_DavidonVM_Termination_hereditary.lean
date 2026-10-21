-- Prove2me | solution 1 for DavidonVM.Termination.hereditary
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:57:05.200995+00:00
-- url     : https://prove2.me/submissions/34b9ba9e-7e8c-4dda-a439-9b01aee5c125

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

theorem solution {n : ℕ} (G : Mat n) (hG : G.IsSymm) (ξ : Vec n) (x : ℕ → Vec n)
    (H : ℕ → Mat n) (hH0 : (H 0).IsSymm) (hrun : IsQuadRun G ξ x H) (k : ℕ)
    (hMN : ∀ i < k, Mval (grad G ξ) x H i ≠ Nval (grad G ξ) x H i) :
    ∀ j < k, H k *ᵥ (G *ᵥ (x (j + 1) - x j)) = x (j + 1) - x j := by
  have key : ∀ k : ℕ, (∀ i < k, Mval (grad G ξ) x H i ≠ Nval (grad G ξ) x H i) →
      (H k).IsSymm ∧ ∀ j < k, H k *ᵥ (G *ᵥ (x (j + 1) - x j)) = x (j + 1) - x j := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hH0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hsym, hj⟩ := ih (fun i hi => hk i (Nat.lt_succ_of_lt hi))
      obtain ⟨hxk, hHk⟩ := hrun k
      have hne := hk k (Nat.lt_succ_self k)
      have hS : x (k + 1) - x k = -(H k *ᵥ grad G ξ (x k)) := by rw [hxk]; abel
      have hD : grad G ξ (x (k + 1)) - grad G ξ (x k) = G *ᵥ (x (k + 1) - x k) :=
        Dv.grad_sub G ξ _ _
      refine ⟨?_, ?_⟩
      · rw [hHk]; exact Dv.update_symm hsym _ _
      · intro j hjk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk | hjk'
        · -- j < k
          have hu : H k *ᵥ grad G ξ (x (k + 1))
              = -(x (k + 1) - x k) + H k *ᵥ (G *ᵥ (x (k + 1) - x k)) := by
            have : grad G ξ (x (k + 1)) = grad G ξ (x k) + G *ᵥ (x (k + 1) - x k) := by
              rw [← hD]; abel
            rw [this, Matrix.mulVec_add, hS]
            simp
          have h0 : (H k *ᵥ grad G ξ (x (k + 1))) ⬝ᵥ (G *ᵥ (x (j + 1) - x j)) = 0 := by
            rw [hu, add_dotProduct, neg_dotProduct, Dv.symm_dot hsym, hj j hjk,
              Dv.symm_dot hG]
            exact neg_add_cancel _
          rw [hHk, Dv.update_apply, h0, mul_zero, zero_smul, add_zero]
          exact hj j hjk
        · -- j = k
          rw [hjk', ← hD, hHk]
          have h := Dv.sec_core (H k) hsym (grad G ξ (x k)) (grad G ξ (x (k + 1))) hne
          rw [hS]
          exact h
  exact (key k hMN).2
