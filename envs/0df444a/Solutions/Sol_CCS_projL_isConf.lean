-- Prove2me | solution 1 for CCS.projL_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:50.999871+00:00
-- url     : https://prove2.me/submissions/7d1b3078-976d-4beb-a8bb-c60daf593955

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
theorem _root_.solution (hc : (parSES E F).toGES.isConf c) : E.toGES.isConf (projL c) :=
  GES.isConf_pmap (G := (parSES E F).toGES) (H := E.toGES) Tag.evL
    (fun {s} h => con_projL (s := s) h)
    (fun {_ _ x} hX hu => (hX.1 x hu)) hc
end CCS
