-- Prove2me | solution 1 for Freiman.form_reduced_pair
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:31.070203+00:00
-- url     : https://prove2.me/submissions/fe1007f6-43b0-4966-b828-a5ec9ff7b0e6

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_irrational_roots
import Theorems.Thm_Freiman_form_roots_reduction
import Theorems.Thm_Freiman_form_reduction_algebra
import Theorems.Thm_Freiman_form_unimodular_minimum
import Theorems.Thm_Freiman_form_unimodular_discriminant
import Theorems.Thm_Freiman_form_scaling_minimum

open Freiman

theorem solution (A B C : ℝ) (hd : 0 < B^2-4*A*C) (hm : 0 < quadraticMinimum A B C) :
    ∃ α β : ℝ, 1 < α ∧ 0 < β ∧ β < 1 ∧ Irrational α ∧ Irrational β ∧
      0 < reducedMinimum α β ∧ Real.sqrt (B^2-4*A*C) / quadraticMinimum A B C = 1 / reducedMinimum α β := by
  obtain ⟨hA, r, s, hrs, hr, hs, hf⟩ := form_irrational_roots A B C hd hm
  obtain ⟨a, b, c, d, α, β, hdet, hα, hβ, hβ1, hiα, hiβ, hcα, hcβ, her, hes⟩ :=
    form_roots_reduction r s hrs hr hs
  refine ⟨α, β, hα, hβ, hβ1, hiα, hiβ, ?_⟩
  exact form_reduction_algebra A B C r s a b c d α β hd hm hA hf hdet hα hβ hβ1 hcα hcβ her hes
    (form_unimodular_minimum A B C a b c d hdet)
    (form_unimodular_discriminant A B C a b c d hdet)
    (fun k hk => form_scaling_minimum (reducedA α β) (reducedB α β) (reducedC α β) k hk)
