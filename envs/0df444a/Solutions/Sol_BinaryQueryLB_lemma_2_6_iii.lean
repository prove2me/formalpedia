-- Prove2me | solution 1 for BinaryQueryLB.lemma_2_6_iii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:23:12.861409+00:00
-- url     : https://prove2.me/submissions/7a32e23f-f75e-4759-b34b-355665aa8719

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_Wset

namespace Aux_BQLB_26
open BinaryQueryLB

theorem fW_point {m : ℕ} [NeZero m] (W : Fin m → EuclideanSpace ℝ (Fin m)) (hW : W ∈ Wset m)
    (i : Fin m) (z : EuclideanSpace ℝ (Fin m)) (T : ℝ)
    (hT : 2 * tau m * ‖z‖ ≤ aConst * T) :
    fW W (WithLp.toLp 2 (Sum.elim (fun j => if j = i then T else 0) (fun j => z j))) =
      aConst * T + inner ℝ (W i) z := by
  have hx : ∀ j, xPart (WithLp.toLp 2 (Sum.elim (fun j => if j = i then T else 0) (fun j => z j)) :
      PtSpace m) j = if j = i then T else 0 := fun j => rfl
  have hz : zPart (WithLp.toLp 2 (Sum.elim (fun j => if j = i then T else 0) (fun j => z j)) :
      PtSpace m) = z := rfl
  unfold fW
  simp only [hx, hz]
  have hnorm : ∀ j, ‖W j‖ ≤ tau m := fun j => by
    have := hW j
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hb : ∀ j, |inner ℝ (W j) z| ≤ tau m * ‖z‖ := fun j =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hnorm j) (norm_nonneg _))
  apply le_antisymm
  · apply ciSup_le
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp only [hj, if_false, mul_zero, zero_add]
      have h1 := (abs_le.mp (hb j)).2
      have h2 := (abs_le.mp (hb i)).1
      linarith
  · have := le_ciSup (Set.finite_range (fun j => aConst * (if j = i then T else 0) +
      inner ℝ (W j) z)).bddAbove i
    simpa using this

end Aux_BQLB_26

open BinaryQueryLB Aux_BQLB_26 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (W W' : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2))) (hW : W ∈ Wset (d / 2)) (hW' : W' ∈ Wset (d / 2))
    (h : FW d R M W' = FW d R M W) : W' = W := by
  have hm1 : 1 ≤ d / 2 := by omega
  haveI : NeZero (d / 2) := ⟨by omega⟩
  have hPhi : ∀ q : PtSpace (d / 2), PhiW W' q = PhiW W q := by
    intro q
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun k =>
      if hk : k.1 < d / 2 then (R • q) (Sum.inl ⟨k.1, hk⟩)
      else if hk2 : k.1 - d / 2 < d / 2 then (R • q) (Sum.inr ⟨k.1 - d / 2, hk2⟩) else 0)
    have hy : ybar d y = R • q := by
      ext jj
      rcases jj with i | j
      · change (if hk : i.1 < d / 2 then (R • q) (Sum.inl ⟨i.1, hk⟩) else
          if hk2 : i.1 - d / 2 < d / 2 then (R • q) (Sum.inr ⟨i.1 - d / 2, hk2⟩) else 0) =
          (R • q) (Sum.inl i)
        rw [dif_pos i.2]
      · have h1 : ¬ (d / 2 + j.1 < d / 2) := by omega
        have h2 : d / 2 + j.1 - d / 2 < d / 2 := by omega
        change (if hk : d / 2 + j.1 < d / 2 then (R • q) (Sum.inl ⟨d / 2 + j.1, hk⟩) else
          if hk2 : d / 2 + j.1 - d / 2 < d / 2 then (R • q) (Sum.inr ⟨d / 2 + j.1 - d / 2, hk2⟩)
          else 0) = (R • q) (Sum.inr j)
        rw [dif_neg h1, dif_pos h2]
        have hj : (⟨d / 2 + j.1 - d / 2, h2⟩ : Fin (d / 2)) = j := Fin.ext (by simp)
        rw [hj]
    have := congrFun h y
    unfold FW at this
    rw [hy, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] at this
    have hpos : M * R / 2 ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos this
  have hf : ∀ q : PtSpace (d / 2), fW W' q = fW W q := by
    intro q
    have := hPhi q
    unfold PhiW at this
    linarith
  funext i
  apply ext_inner_right ℝ
  intro z
  have ha : (0 : ℝ) < aConst := by unfold aConst; norm_num
  have hT' : 2 * tau (d / 2) * ‖z‖ ≤ aConst * (2 * tau (d / 2) * ‖z‖ / aConst) := by
    rw [mul_div_cancel₀ _ ha.ne']
  have e1 := fW_point W hW i z _ hT'
  have e2 := fW_point W' hW' i z _ hT'
  have := hf (WithLp.toLp 2 (Sum.elim (fun j => if j = i then 2 * tau (d / 2) * ‖z‖ / aConst else 0)
    (fun j => z j)))
  rw [e1, e2] at this
  linarith
