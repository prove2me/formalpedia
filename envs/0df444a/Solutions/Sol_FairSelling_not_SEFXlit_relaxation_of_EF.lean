-- Prove2me | solution 1 for FairSelling.not_SEFXlit_relaxation_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:38.365485+00:00
-- url     : https://prove2.me/submissions/fd16732e-f416-49bc-92a3-96dd804a07e0

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
import Theorems.Thm_FairSelling_RelaxEx_p_nonneg
import Theorems.Thm_FairSelling_RelaxEx_v_nonneg
import Theorems.Thm_FairSelling_RelaxEx_o_valid
import Theorems.Thm_FairSelling_RelaxEx_o_EF
import Theorems.Thm_FairSelling_RelaxEx_o_not_SEFXlit

set_option autoImplicit true
open scoped BigOperators
open FairSelling
namespace FairSelling
theorem _root_.solution :
    ¬ ∀ (v : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
        (∀ i g, 0 ≤ v i g) → (∀ g, 0 ≤ p g) → o.Valid p → EF v p o → SEFXlit v p o := by
  intro h
  exact RelaxEx.o_not_SEFXlit
    (h RelaxEx.v RelaxEx.p RelaxEx.o RelaxEx.v_nonneg RelaxEx.p_nonneg RelaxEx.o_valid RelaxEx.o_EF)
end FairSelling
