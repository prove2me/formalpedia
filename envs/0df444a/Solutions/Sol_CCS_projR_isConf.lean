-- Prove2me | solution 1 for CCS.projR_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:52.363728+00:00
-- url     : https://prove2.me/submissions/9ed5b26a-a4ea-4b5e-8289-d1ad9173c440

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Theorems.Thm_GES_isConf_pmap


set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}
namespace CCS
theorem _root_.solution (hc : (parSES E F).toGES.isConf c) : F.toGES.isConf (projR c) :=
  GES.isConf_pmap (G := (parSES E F).toGES) (H := F.toGES) Tag.evR
    (fun {s} h => con_projR (s := s) h)
    (fun {_ _ x} hX hu => (hX.2 x hu)) hc
end CCS
