-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.kpHerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:43.189823+00:00
-- url     : https://prove2.me/submissions/b193f1ad-7efc-466c-a09d-176d9ac72093

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_iso_card

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
namespace Formalism.FourierDecayAlt.P.A6x8
theorem _root_.solution : KpHerm := by
  intro K _ R ψ w w'
  unfold Kp
  have h := AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom
    (starRingEnd ℂ).injective (pairTerm R ψ w w')
  have h' : conj (∑ᶠ q, pairTerm R ψ w w' q) = ∑ᶠ q, conj (pairTerm R ψ w w' q) := h
  rw [h', ← finsum_comp_equiv (Equiv.prodComm (Cos R w) (Cos R w'))]
  refine finsum_congr fun q => ?_
  rcases q with ⟨q1, q2⟩
  show pairTerm R ψ w' w (q2, q1) = conj (pairTerm R ψ w w' (q1, q2))
  have hc := iso_card R (orbZ w (rep R q1)) (orbZ w' (rep R q2))
  unfold pairTerm
  by_cases h1 : IsInt R (orbZ w (rep R q1)) ∧ IsInt R (orbZ w' (rep R q2))
  · rw [if_pos h1, if_pos h1.symm, hc]; simp; ring
  · rw [if_neg h1, if_neg (fun h => h1 h.symm)]; simp
end Formalism.FourierDecayAlt.P.A6x8
