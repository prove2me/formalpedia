-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.germExpansionKernelOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:44.712804+00:00
-- url     : https://prove2.me/submissions/dd572496-dd1b-4aa6-ab41-64724732c92c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumSwap_finsum_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FiniteSumSwap
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.GermKernelAssemble := by
  intro hGerm hKp hInt hRoots K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨V, hV, H⟩ := hGerm K R ψ hD hn m hm γ hγ h Q hQ hQu
  refine ⟨V, hV, fun t c ht hc w' => ?_⟩
  have := hD.artin
  have := hD.red
  have hT : {z : Kˣ | z ^ (m + 1) = (-t) ^ m * c}.Finite :=
    hRoots K (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) ((-t) ^ m * c)
  have hP : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite := hInt K R ψ hD w'
  rw [hKp K R ψ hD (pt2 h m t c) w']
  simp_rw [H t c ht hc]
  unfold germSum
  simp_rw [hKp K R ψ hD (addBlock h (m + 1) _) w']
  classical
  convert finsum_swap (fun q : Cos R w' => IsInt R (orbZ w' (rep R q)))
    (fun z : Kˣ => z ^ (m + 1) = (-t) ^ m * c) hP hT _ (germCoef R ψ m γ t)
    (fun z q => bbZ R ψ (addBlock h (m + 1) z) (orbZ w' (rep R q)))
    (fun q => conj (phase ψ (rep R q)))
end Formalism.FourierDecayAlt.P
