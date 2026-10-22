-- Prove2me | solution 1 for BootRobust.NWDual.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:08:19.206377+00:00
-- url     : https://prove2.me/submissions/83dd54ae-d07d-4fed-a1c9-521f4c57a51a

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

set_option autoImplicit false

lemma brn_ereal_cancel (s : ℝ) (hs : 0 < s) (R : EReal) (r : ℝ)
    (h : (s : EReal) * R ≤ (s : EReal) * (r : EReal)) : R ≤ (r : EReal) := by
  induction R using EReal.rec with
  | bot => exact bot_le
  | top =>
    rw [EReal.coe_mul_top_of_pos hs, ← EReal.coe_mul] at h
    exact absurd (top_le_iff.mp h) (EReal.coe_ne_top _)
  | coe x =>
    rw [← EReal.coe_mul, ← EReal.coe_mul] at h
    have : s * x ≤ s * r := by exact_mod_cast h
    exact_mod_cast le_of_mul_le_mul_left this hs

lemma brn_ereal_mul (s : ℝ) (hs : 0 < s) (R : EReal) (r : ℝ) (h : R ≤ (r : EReal)) :
    (s : EReal) * R ≤ (s : EReal) * (r : EReal) :=
  mul_le_mul_of_nonneg_left h (by exact_mod_cast hs.le)

lemma brn_sg_pos {ι : Type*} [Fintype ι] (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) : 0 < ∑ i, w i * D i := by
  apply Finset.sum_pos'
  · intro i _; exact mul_nonneg (hw i).le (hD.1 i)
  · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := D)
      (by rw [hD.2]; exact one_ne_zero)
    exact ⟨i, Finset.mem_univ _, mul_pos (hw i) (lt_of_le_of_ne (hD.1 i) (Ne.symm hi))⟩

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (D : ι → ℝ) (r : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    BootRobust.NWDual.robustNW R D r w (L z) = BootRobust.NWDual.perspValue R D r w (L z) := by
  unfold BootRobust.NWDual.robustNW BootRobust.NWDual.perspValue
  apply le_antisymm
  · refine iSup₂_le fun D' hD' => ?_
    obtain ⟨hD's, hR⟩ := hD'
    have hpos := brn_sg_pos D' hD's w hw
    set Sg := ∑ i, w i * D' i with hSg
    have hs : 0 < 1 / Sg := by positivity
    refine le_iSup₂_of_le ((1 / Sg), fun i => D' i * (1 / Sg)) ?_ ?_
    · refine ⟨hs, ?_, ?_, ?_, ?_⟩
      · have : (fun i => D' i * (1 / Sg) / (1 / Sg)) = D' := by
          funext i; field_simp
        simpa only [this] using hD's
      · have : (fun i => D' i * (1 / Sg) / (1 / Sg)) = D' := by
          funext i; field_simp
        simp only [this]
        exact brn_ereal_mul _ hs _ _ hR
      · rw [← Finset.sum_mul, hD's.2]; ring
      · have : ∑ i, w i * (D' i * (1 / Sg)) = (∑ i, w i * D' i) * (1 / Sg) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, ← hSg]; field_simp
    · apply le_of_eq
      congr 1
      have : ∑ i, w i * L z i * (D' i * (1 / Sg)) = (∑ i, w i * L z i * D' i) * (1 / Sg) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      show (∑ i, w i * L z i * D' i) / Sg = _
      ring
  · refine iSup₂_le fun sP hsP => ?_
    obtain ⟨hs, hsimp, hR, hsum, hw1⟩ := hsP
    obtain ⟨s, P⟩ := sP
    simp only at hs hsimp hR hsum hw1
    refine le_iSup₂_of_le (fun i => P i / s) ⟨hsimp, brn_ereal_cancel s hs _ _ hR⟩ ?_
    apply le_of_eq
    congr 1
    have h1 : ∑ i, w i * (P i / s) = 1 / s := by
      have : ∑ i, w i * (P i / s) = (∑ i, w i * P i) / s := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hw1]
    show _ = (∑ i, w i * L z i * (P i / s)) / (∑ i, w i * (P i / s))
    rw [h1]
    have : ∑ i, w i * L z i * (P i / s) = (∑ i, w i * L z i * P i) / s := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    field_simp
