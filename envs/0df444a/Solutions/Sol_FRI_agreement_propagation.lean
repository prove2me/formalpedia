-- Prove2me | solution 1 for FRI_agreement_propagation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:34:49.622089+00:00
-- url     : https://prove2.me/submissions/3d8ac6b7-5872-4fff-bcc2-90a22a9f5719

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_agreement_next_implies_fold_agreement
import Theorems.Thm_FRI_green_set_pow_subset


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings)
    (h_not_bad : ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i))
    (h_large : FRI_Is_Large_Subset P f_0 bound i i.isLt (FRI_green_set P f_0 T i.castSucc))
    (h_agree_next : FRI_agreement_at_round P f_0 T i.succ) :
    FRI_agreement_at_round P f_0 T i.castSucc := by
  -- Proof by contradiction: assume no codeword agrees at round i, derive BadEvent
  unfold FRI_agreement_at_round at ⊢
  -- Show the fold agrees with some codeword on pow_domain(green_set at i)
  have h_fold_agree : ∃ (u : FRI_domain P (i + 1) → F), u ∈ FRI_code P (i + 1) ∧
      ∀ z, z ∈ pow_domain (FRI_green_set P f_0 T i) (P.m i) →
        Fold (FRI_domain P i) (P.m i)
          (extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt)) (T.alpha i) z =
          extend_by_zero (FRI_domain P (i + 1)) u z := by
    obtain ⟨u'', hu''_code, hu''_agree⟩ :=
      FRI_agreement_next_implies_fold_agreement P f_0 T i h_agree_next
    use u'', hu''_code
    intro z hz
    have h_z_in_domain : z ∈ FRI_domain P (i + 1) := FRI_green_set_subset_domain P f_0 T i.succ
      (FRI_green_set_pow_subset P f_0 T i i.isLt hz)
    simp only [extend_by_zero, h_z_in_domain, ↓reduceDIte]
    have h_agree_at_z := hu''_agree z hz
    simp only at h_agree_at_z
    rw [← h_agree_at_z]
    -- Show the two Fold expressions are equal via function extensionality
    unfold Fold
    congr 2
    funext y
    simp only [extend_by_zero]
    by_cases hy : y ∈ FRI_domain P i
    · simp only [hy, ↓reduceDIte, FRI_oracle_at_round, FRI_get_val, Fin.coe_castSucc]
      by_cases h0 : (↑i : ℕ) = 0
      · simp only [h0, ↓reduceDIte]
        have h_y_D0 : y ∈ P.D_0 := by simp only [FRI_domain, h0] at hy; exact hy
        simp only [h_y_D0, ↓reduceDIte]
      · simp only [h0, ↓reduceDIte]
    · simp only [hy, ↓reduceDIte]
  -- Proof by contradiction: derive BadEvent from lack of agreement
  by_contra h_no_agree
  push_neg at h_no_agree
  apply h_not_bad
  unfold FRI_BadEvent
  refine ⟨FRI_green_set P f_0 T i, h_large, h_fold_agree, ?_⟩
  intro v hv
  push_neg
  obtain ⟨x, hx_green, hx_neq⟩ := h_no_agree v hv
  use x, hx_green
  have hx_domain := FRI_green_set_subset_domain P f_0 T i hx_green
  simp only [extend_by_zero, hx_domain, ↓reduceDIte]
  suffices h_oracle_eq_get_val :
      FRI_oracle_at_round P f_0 T ↑i i.isLt ⟨x, hx_domain⟩ =
        FRI_get_val P f_0 T i.castSucc x by rw [h_oracle_eq_get_val, ne_eq, eq_comm]; exact hx_neq
  simp only [FRI_oracle_at_round, FRI_get_val, Fin.coe_castSucc]
  by_cases h0 : (↑i : ℕ) = 0
  · simp only [h0, ↓reduceDIte]
    have h_x_D0 : x ∈ P.D_0 := by simp only [FRI_domain, h0] at hx_domain; exact hx_domain
    simp only [h_x_D0, ↓reduceDIte]
  · simp only [h0, ↓reduceDIte, dif_pos hx_domain]
