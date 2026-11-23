-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.out_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:52.633168+00:00
-- url     : https://prove2.me/submissions/583e70b4-741e-4b04-ba7f-97623ed311cf

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (y : G ⧸ Λ) (v : G) :
    ∃ l ∈ Λ, (Quotient.out (y + (v : G ⧸ Λ)) : G) = Quotient.out y + v + l := by
  refine ⟨Quotient.out (y + (v : G ⧸ Λ)) - Quotient.out y - v, ?_, by abel⟩
  rw [← QuotientAddGroup.eq_zero_iff]
  simp [QuotientAddGroup.mk_sub]
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
