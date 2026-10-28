-- Prove2me | solution 1 for BitcoinActivation.activeAfter_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:17.096832+00:00
-- url     : https://prove2.me/submissions/4823292d-f0c1-4042-9299-c7badc7e8c1d

import Definitions.Def_BitcoinActivation

open BitcoinActivation

theorem solution (dep : BuriedDeployment) (prevHeight : Nat) :
    BitcoinActivation.activeAfter prevHeight dep = BitcoinActivation.activeAt (prevHeight + 1) dep := rfl
