-- Prove2me | solution 1 for D1Bound5.pairLightIndexedWitnessesCheckedBool_of_prefix_drop
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:52.008587+00:00
-- url     : https://prove2.me/submissions/ee80984b-a15a-4836-b580-c03cf94297fd

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq_prefix_drop

section
namespace D1Bound5

/- Exact coordinate-only version of the indexed closure checker. Mathematical
soundness is established in PairLightClosureBridge, not assumed here. -/





















theorem _root_.solution (tau nu : Int)
    (a b r0 : PairLightCoordinate) (bound : Int) (vertices : List PairLightCoordinate)
    (n : Nat) (witnesses : List PairLightRootWitness)
    (destinations : List (Option Nat × Option Nat))
    (hprefix : pairLightIndexedWitnessesPrefixBool tau nu a b r0 bound vertices n
      witnesses destinations = true)
    (htail : pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices
      (witnesses.drop n) (destinations.drop n) = true) :
    pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices witnesses destinations = true :=
  (pairLightIndexedWitnessesCheckedBool_eq_prefix_drop tau nu a b r0 bound vertices n
    witnesses destinations).trans (Bool.and_eq_true_iff.mpr ⟨hprefix, htail⟩)

end D1Bound5
end
