-- Prove2me | solution 1 for Comp.sum_ite_coe_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:32.179922+00:00
-- url     : https://prove2.me/submissions/67494ed8-9836-459c-9dde-c0531e53eeb3

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_sum_ite_coe_eq

set_option autoImplicit true
open Comp
namespace Comp
theorem _root_.solution {n t : ℕ} (ht : t < n) :
    ∑ s' : Fin n, (if (s' : ℕ) = t then (1 : ℚ) else 0) = 1 :=
  sum_ite_coe_eq ht 1
end Comp
