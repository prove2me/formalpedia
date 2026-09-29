-- Prove2me | solution 1 for Freiman.form_root_convergent_data
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:30.151388+00:00
-- url     : https://prove2.me/submissions/8027b044-d41d-465e-b477-514c2befeee8

import Definitions.Def_Freiman_reducedForms
import Definitions.Def_Freiman_rootConvergentData
import Theorems.Thm_Freiman_irrational_integer_normalization
import Theorems.Thm_Freiman_cfValue_surjective_irrational_unit
import Theorems.Thm_Freiman_form_root_data_of_cfValue

open Freiman

theorem solution (r : ℝ) (hr : Irrational r) :
    Nonempty (RootConvergentData r) := by
  obtain ⟨x,z,hx,h0,h1,he⟩ := irrational_integer_normalization r hr
  obtain ⟨b,hb⟩ := cfValue_surjective_irrational_unit x hx h0 h1
  rw [he, ← hb]
  exact form_root_data_of_cfValue b z
