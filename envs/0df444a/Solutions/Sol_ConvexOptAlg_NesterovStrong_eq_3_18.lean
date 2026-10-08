-- Prove2me | solution 1 for ConvexOptAlg.NesterovStrong.eq_3_18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:05:42.760444+00:00
-- url     : https://prove2.me/submissions/843ec5b9-e5a1-4efd-b29b-5b1debf0a5d3

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

set_option autoImplicit false

namespace P67ad69c3
open ConvexOptAlg.NesterovStrong

lemma step {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (s : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    Phi f g α β x (s + 2) z - f z ≤
      (1 - 1 / Real.sqrt (kappa α β)) * (Phi f g α β x (s + 1) z - f z) := by
  have hL := hsc (x (s + 1)) (Set.mem_univ _) z (Set.mem_univ _)
  have hd : 0 ≤ 1 / Real.sqrt (kappa α β) := by positivity
  have hm := mul_le_mul_of_nonneg_left (ge_iff_le.mp hL) hd
  rw [Phi]
  nlinarith [hm]

lemma triv_case {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n))
    (hv : ∀ w : EuclideanSpace ℝ (Fin n), w = 0) (s : ℕ) :
    Phi f g α β x (s + 1) z = f z := by
  induction s with
  | zero => rw [Phi, hv z, hv (x 1)]; simp
  | succ k ih =>
    rw [Phi, ih, hv (x (k + 1)), hv z]
    simp
    ring

lemma alpha_le_beta {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) : α ≤ β := by
  have h1 := hsc w (Set.mem_univ _) 0 (Set.mem_univ _)
  have h2 := hsc 0 (Set.mem_univ _) w (Set.mem_univ _)
  have hL := hsm.2 w 0
  simp only [zero_sub, sub_zero, norm_neg, inner_neg_right] at h1 h2 hL
  have hci : ⟪g w - g 0, w⟫_ℝ ≤ ‖g w - g 0‖ * ‖w‖ := real_inner_le_norm _ _
  rw [inner_sub_left] at hci
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h3 : α * ‖w‖ ^ 2 ≤ β * ‖w‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hL hpos.le]
  exact le_of_mul_le_mul_right h3 (by positivity)

end P67ad69c3

open ConvexOptAlg.NesterovStrong in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    Phi f g α β x (s + 1) z ≤
      f z + (1 - 1 / Real.sqrt (kappa α β)) ^ s * (Phi f g α β x 1 z - f z) := by
  by_cases hv : ∀ w : EuclideanSpace ℝ (Fin n), w = 0
  · rw [P67ad69c3.triv_case f g α β x z hv s, P67ad69c3.triv_case f g α β x z hv 0]
    simp
  · push_neg at hv
    obtain ⟨w, hw⟩ := hv
    have hab : α ≤ β := P67ad69c3.alpha_le_beta f g α β hsc hsm w hw
    have hk : 1 ≤ kappa α β := by
      unfold kappa; rw [le_div_iff₀ hα]; linarith
    have hsq : 1 ≤ Real.sqrt (kappa α β) := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hk
    have hc0 : 0 ≤ 1 - 1 / Real.sqrt (kappa α β) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hsq
    induction s with
    | zero => simp
    | succ k ih =>
      have hst := P67ad69c3.step f g α β hsc x k z
      calc Phi f g α β x (k + 1 + 1) z
          ≤ f z + (1 - 1 / Real.sqrt (kappa α β)) * (Phi f g α β x (k + 1) z - f z) := by
            linarith
        _ ≤ f z + (1 - 1 / Real.sqrt (kappa α β)) *
              ((1 - 1 / Real.sqrt (kappa α β)) ^ k * (Phi f g α β x 1 z - f z)) := by
            gcongr; linarith
        _ = f z + (1 - 1 / Real.sqrt (kappa α β)) ^ (k + 1) * (Phi f g α β x 1 z - f z) := by
            ring
