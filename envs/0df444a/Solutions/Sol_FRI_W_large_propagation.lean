-- Prove2me | solution 1 for FRI_W_large_propagation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:06.576845+00:00
-- url     : https://prove2.me/submissions/b29e82ec-1e04-4978-a74f-a173026e4373

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_W_ratio_le
import Theorems.Thm_FRI_domain_card_pos


set_option autoImplicit true

theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F)
    (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_large_0 : (FRI_W P f_0 T 0).card ≥
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P 0).card) :
    ∀ i : Fin (P.num_foldings + 1), (FRI_W P f_0 T i).card ≥
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card := by
  intro i
  induction i using Fin.induction with
  | zero => exact h_large_0
  | succ i ih =>
    have h_ratio := FRI_W_ratio_le P f_0 T h_domain_size i i.isLt
    -- h_ratio: |W_i|/|D_i| ≤ |W_{i+1}|/|D_{i+1}|, and ih: (1-δ)|D_i| ≤ |W_i|.
    -- By transitivity: (1-δ) ≤ |W_i|/|D_i| ≤ |W_{i+1}|/|D_{i+1}|, so (1-δ)|D_{i+1}| ≤ |W_{i+1}|.
    simp only [ge_iff_le, Fin.coe_castSucc, Fin.val_succ] at *
    have hD_i_pos : (0:ℝ) < (FRI_domain P ↑i).card :=
      Nat.cast_pos.mpr <| FRI_domain_card_pos P ⟨i, Nat.lt_succ_of_lt i.isLt⟩
    have hD_succ_pos : (0:ℝ) < (FRI_domain P (↑i + 1)).card :=
      Nat.cast_pos.mpr <| FRI_domain_card_pos P i.succ
    calc (1 - FRI_distance_star P f_0 bound) * (FRI_domain P (↑i + 1)).card
      _ ≤ (FRI_W P f_0 T ↑i).card / (FRI_domain P ↑i).card * (FRI_domain P (↑i + 1)).card := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rwa [le_div_iff₀ hD_i_pos]
      _ ≤ (FRI_W P f_0 T (↑i + 1)).card / (FRI_domain P (↑i + 1)).card *
          (FRI_domain P (↑i + 1)).card := by
          apply mul_le_mul_of_nonneg_right h_ratio (by positivity)
      _ = (FRI_W P f_0 T (↑i + 1)).card := by field_simp
