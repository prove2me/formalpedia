-- Prove2me | solution 1 for FRI_W_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:29:05.043291+00:00
-- url     : https://prove2.me/submissions/6d0af310-87b5-44dd-8478-a1c39020208e

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_W_size_le

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (h_domain_size : FRI_Domain_Size_Property P)
    (i : ℕ) (h : i < P.num_foldings) :
    ((FRI_W P f_0 T i).card : ℝ) / (FRI_domain P i).card ≤
      ((FRI_W P f_0 T (i + 1)).card : ℝ) / (FRI_domain P (i + 1)).card := by
  -- By definition of FRI_domain, |FRI_domain P i| = m_i * |FRI_domain P (i + 1)|.
  have h_domain_size_eq : (FRI_domain P i).card = P.m ⟨i, h⟩ * (FRI_domain P (i + 1)).card :=
    h_domain_size i h
  -- Upper bound on W set size.
  have h_ratio :
      ((FRI_W P f_0 T i).card : ℝ) ≤ P.m ⟨i, h⟩ * ((FRI_W P f_0 T (i + 1)).card : ℝ) :=
    mod_cast FRI_W_size_le P f_0 T i h
  simp only [h_domain_size_eq, Nat.cast_mul]
  by_cases hD : (FRI_domain P (i + 1)).card = 0
  · simp [hD]
  · have hm_pos : (0 : ℝ) < P.m ⟨i, h⟩ := Nat.cast_pos.mpr (P.h_m_pos _)
    rw [mul_comm (P.m ⟨i, h⟩ : ℝ), div_mul_eq_div_div, div_le_iff₀ hm_pos]
    calc ((FRI_W P f_0 T i).card : ℝ) / (FRI_domain P (i + 1)).card
        ≤ P.m ⟨i, h⟩ * (FRI_W P f_0 T (i + 1)).card / (FRI_domain P (i + 1)).card := by gcongr
        _ = (FRI_W P f_0 T (i + 1)).card / (FRI_domain P (i + 1)).card * P.m ⟨i, h⟩ := by ring
