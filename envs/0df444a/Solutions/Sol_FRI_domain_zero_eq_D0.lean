-- Prove2me | solution 1 for FRI_domain_zero_eq_D0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:57:18.741748+00:00
-- url     : https://prove2.me/submissions/8b9e71a8-fa01-4752-9165-353b69b0a1dc

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) : FRI_domain P 0 = P.D_0 := rfl
