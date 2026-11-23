-- Prove2me | solution 1 for FRI_agreement_next_implies_fold_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:32:46.267294+00:00
-- url     : https://prove2.me/submissions/fe33c210-696e-41e1-9a4b-1a215cf00d1d

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_green_set_pow_subset


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : Fin P.num_foldings)
    (h_agree_next : FRI_agreement_at_round P f_0 T i.succ) :
    ∃ u' ∈ FRI_code P i.succ, ∀ z (hz : z ∈ pow_domain (FRI_green_set P f_0 T i) (P.m i)),
      let f_prev := extend_by_zero (FRI_domain P i) (fun x ↦ FRI_get_val P f_0 T i.castSucc x)
      Fold (FRI_domain P i) (P.m i) f_prev (T.alpha i) z =
        u' ⟨z, FRI_green_set_subset_domain P f_0 T i.succ
          (FRI_green_set_pow_subset P f_0 T i i.isLt hz)⟩ := by
  -- Extract the codeword from the agreement at round i.succ
  obtain ⟨u', hu'_code, hu'_agree⟩ := h_agree_next
  use u', hu'_code
  intro z hz
  -- z ∈ pow_domain (green_set at i) ⊆ green_set at i+1
  have hz_green : z ∈ FRI_green_set P f_0 T i.succ := FRI_green_set_pow_subset P f_0 T i i.isLt hz
  -- From hz, there exists x in green_set at i such that z = x^m
  rw [pow_domain, Finset.mem_image] at hz
  obtain ⟨x, hx_green, rfl⟩ := hz
  -- x is green at round i, so the fold check passes at y = x^m
  have h_fold_check : FRI_fold_check P f_0 T i (x ^ P.m i) := by
    classical
    have hx_green' : FRI_is_green P f_0 T i x := (Finset.mem_filter.mp hx_green).2
    unfold FRI_is_green at hx_green'
    simp only [i.isLt, ↓reduceDIte] at hx_green'
    exact hx_green'.2
  -- The fold check says: Fold ... = FRI_get_val ... i.succ (x^m)
  unfold FRI_fold_check at h_fold_check
  simp only []
  -- Show that Fold with extend_by_zero equals Fold without it
  have h_fold_eq :
      Fold (FRI_domain P i) (P.m i) (fun x ↦ FRI_get_val P f_0 T i.castSucc x)
        (T.alpha i) (x ^ P.m i) =
      Fold (FRI_domain P i) (P.m i)
        (extend_by_zero (FRI_domain P i) (fun x ↦ FRI_get_val P f_0 T i.castSucc x))
        (T.alpha i) (x ^ P.m i) := by
    unfold Fold
    congr 1
    apply Lagrange.interpolate_eq_of_values_eq_on
    intro y hy
    simp only [Block, Finset.mem_filter, extend_by_zero] at hy ⊢
    simp only [hy.1, ↓reduceDIte]
  rw [← h_fold_eq, h_fold_check]
  exact (hu'_agree (x ^ P.m i) hz_green).symm
