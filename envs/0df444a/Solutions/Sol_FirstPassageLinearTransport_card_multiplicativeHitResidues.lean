-- Prove2me | solution 1 for FirstPassageLinearTransport.card_multiplicativeHitResidues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:28:45.715682+00:00
-- url     : https://prove2.me/submissions/69d861af-0e84-43da-b349-c137fd5864ac

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (M : ℕ) (u : ℝ) :
    (multiplicativeHitResidues M u).card =
      multiplicativeHitCount u M 1 := by
  classical
  unfold multiplicativeHitResidues multiplicativeHitCount
  rw [← Fintype.card_subtype (fun x : Fin (2 ^ M) =>
        crossesMultiplicativeFrom u M 1 (boolParityCode M x)),
      ← Fintype.card_subtype (crossesMultiplicativeFrom u M 1)]
  exact Fintype.card_congr (multiplicativeHitResidueEquiv M u)
end FirstPassageLinearTransport
