-- Prove2me | solution 1 for FairSelling.RelaxEx.o_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:43.39313+00:00
-- url     : https://prove2.me/submissions/04f9d408-2a95-4f7c-a58b-8105eef24b1c

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
import Theorems.Thm_FairSelling_RelaxEx_o_EF
import Theorems.Thm_FairSelling_SEFX_of_EF


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution : SEFX v p o := SEFX_of_EF o_EF
end FairSelling.RelaxEx
