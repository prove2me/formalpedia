-- Prove2me | solution 1 for D1Bound5.pairLightIndexedWitnessesCheckedBool_eq_prefix_drop
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:08.708987+00:00
-- url     : https://prove2.me/submissions/51883f4d-c930-436b-8dc6-28e6addab57f

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions

section
namespace D1Bound5

/- Exact coordinate-only version of the indexed closure checker. Mathematical
soundness is established in PairLightClosureBridge, not assumed here. -/



















theorem _root_.solution (tau nu : Int)
    (a b r0 : PairLightCoordinate) (bound : Int) (vertices : List PairLightCoordinate)
    (n : Nat) (witnesses : List PairLightRootWitness)
    (destinations : List (Option Nat × Option Nat)) :
    pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices witnesses destinations =
      (pairLightIndexedWitnessesPrefixBool tau nu a b r0 bound vertices n witnesses destinations &&
        pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices
          (witnesses.drop n) (destinations.drop n)) := by
  induction n generalizing witnesses destinations with
  | zero =>
      simp only [pairLightIndexedWitnessesPrefixBool, List.drop_zero, Bool.true_and]
  | succ n ih =>
      cases witnesses with
      | nil => cases destinations <;> rfl
      | cons w ws =>
          cases destinations with
          | nil => rfl
          | cons d ds =>
              change
                (pairLightIndexedRootWitnessCheckedBool tau nu a b r0 bound vertices w d &&
                  pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices ws ds) =
                ((pairLightIndexedRootWitnessCheckedBool tau nu a b r0 bound vertices w d &&
                    pairLightIndexedWitnessesPrefixBool tau nu a b r0 bound vertices n ws ds) &&
                  pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices
                    (ws.drop n) (ds.drop n))
              rw [ih ws ds, Bool.and_assoc]



end D1Bound5
end
