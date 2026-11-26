-- Prove2me | solution 1 for Erdos266.tendsto_cast_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:55.323665+00:00
-- url     : https://prove2.me/submissions/7dc3740a-0e3a-4b51-bfcf-2131692c2fb6

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}
namespace Erdos266
theorem _root_.solution (ha : StrictMono a) :
    Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (fun n => by exact_mod_cast ha.le_apply)
    tendsto_natCast_atTop_atTop
end Erdos266
