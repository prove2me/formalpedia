-- Prove2me | solution 1 for FairSelling.RelaxEx.o_SEF1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:22.841305+00:00
-- url     : https://prove2.me/submissions/19572014-e997-43b6-8fb6-1d12f54b207b

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
import Theorems.Thm_FairSelling_RelaxEx_o_EF
import Theorems.Thm_FairSelling_SEF1_of_EF


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution : SEF1 v p o := SEF1_of_EF o_EF
end FairSelling.RelaxEx
