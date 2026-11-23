-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.Kp_eq_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:07.989422+00:00
-- url     : https://prove2.me/submissions/767fd596-4973-42c9-b563-1014fe9cedbd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_Gterm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_toCos_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w w' : Point K) (T T' : Type)
    (σ : T → lowW K w.1 w.2 × upUniG K w.1.sum) (σ' : T' → lowW K w'.1 w'.2 × upUniG K w'.1.sum)
    (hσ : Function.Bijective (fun t => toCos R (σ t)))
    (hσ' : Function.Bijective (fun t => toCos R (σ' t))) :
    Kp R ψ w w' = ∑ᶠ x : T × T', Gterm R ψ w w' (σ x.1) (σ' x.2) := by
  unfold Kp
  symm
  refine finsum_eq_of_bijective
    (fun x : T × T' => ((toCos R (σ x.1), toCos R (σ' x.2)) : Cos R w × Cos R w'))
    (hσ.prodMap hσ') fun x => ?_
  show _ = Gterm R ψ w w' (rep R (toCos R (σ x.1))) (rep R (toCos R (σ' x.2)))
  exact Gterm_inv R ψ hψ w w' _ _ _ _ (inv_toCos_rep R _).symm (inv_toCos_rep R _).symm
end Formalism.FourierDecayAlt.P.A5x8
