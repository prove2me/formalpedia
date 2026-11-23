-- Prove2me | solution 1 for FRI_fold_agreement_on_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:28:57.857116+00:00
-- url     : https://prove2.me/submissions/326e0d45-abbc-4b5e-8ad7-34edbed26b9e

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_W_eq_image
import Theorems.Thm_folded_query_in_domain


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (i : Fin P.num_foldings) :
    ∀ z ∈ FRI_W P f_0 T (i + 1),
      Fold (FRI_domain P i) (P.m i)
        (extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt)) (T.alpha i) z =
      extend_by_zero (FRI_domain P (i.val + 1)) (T.f i) z := by
  intro z hz
  -- Since z ∈ FRI_W P f_0 T (i + 1), there exists s ∈ FRI_BadQuery_Points P f_0 T
  -- such that z = folded_query P s (i + 1).
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ FRI_BadQuery_Points P f_0 T, z = folded_query P s (i + 1) := by
    have := FRI_W_eq_image P f_0 T (i + 1) (by grind)
    simp_all only [Finset.mem_image, Finset.ext_iff, Subtype.exists, exists_and_right]
    rcases hz with ⟨a, ha, rfl⟩
    exact ⟨a, by simpa [FRI_W] using ha, rfl⟩
  simp only [FRI_BadQuery_Points, Finset.mem_filter, Finset.mem_attach, true_and] at hs
  have hlocal := hs i
  simp only [FRI_local_check, Nat.succ_eq_add_one] at hlocal
  -- The folded query is in the domain since s ∈ D_0
  have h_z_in_domain : folded_query P (↑s) (↑i + 1) ∈ FRI_domain P (↑i + 1) :=
    folded_query_in_domain P (↑s) s.property (↑i + 1) (Nat.succ_le_of_lt i.isLt)
  simp only [extend_by_zero, h_z_in_domain, ↓reduceDIte]
  -- Show FRI_get_val at i.succ equals T.f i
  have h_get_val_succ : FRI_get_val P f_0 T i.succ (folded_query P (↑s) (↑i + 1)) =
                        T.f i ⟨folded_query P (↑s) (↑i + 1), h_z_in_domain⟩ := by
    simp [FRI_get_val, dif_pos h_z_in_domain]
  rw [← h_get_val_succ, ← hlocal]
  -- Show extend_by_zero(FRI_oracle_at_round) = FRI_get_val i.castSucc
  have h_castSucc_eq := Fin.coe_castSucc i
  -- Prove function extensionality
  congr 1 with y
  simp only [extend_by_zero, FRI_oracle_at_round, FRI_get_val]
  -- Case analysis: is y in the domain?
  by_cases hy : y ∈ FRI_domain P ↑i
  · -- y ∈ FRI_domain P ↑i
    simp only [hy, ↓reduceDIte]
    have h_domain_hy : y ∈ FRI_domain P i.castSucc := by grind
    by_cases h0 : (↑i : ℕ) = 0
    · -- i = 0: both return f_0
      have h_y_D0 : y ∈ P.D_0 := by simpa only [FRI_domain, h0] using hy
      simp only [h0, h_castSucc_eq, dif_pos h_y_D0]
      rfl
    · -- i ≠ 0: both return T.f
      have h0' : i.castSucc.val ≠ 0 := by grind
      simp only [h0, h0', ↓reduceDIte, dif_pos h_domain_hy]
      congr 1
  · -- y ∉ FRI_domain P ↑i: both return 0
    simp only [hy, ↓reduceDIte]
    have h_not_in : y ∉ FRI_domain P i.castSucc := by grind
    by_cases h0 : i.castSucc.val = 0
    · have h_i_zero : (↑i : ℕ) = 0 := by grind
      have h_D0 : y ∉ P.D_0 := by simpa only [FRI_domain, h_i_zero] using hy
      simp only [h0, dif_neg h_D0, dif_pos trivial]
    · simp only [h0, h_not_in, ↓reduceDIte]
