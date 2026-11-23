-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_low_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.023616+00:00
-- url     : https://prove2.me/submissions/f2067413-2ca2-4fc6-bc57-53827ec04458

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_lowW_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_low_bij


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (m : ℕ) (t c : Kˣ) :
    Function.Bijective (fun ξ : Fin m → KR R =>
      (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K (addBlock (addBlock h0 m t) 1 c).1
        (addBlock (addBlock h0 m t) 1 c).2))) (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)))) := by
  have hb := sec_low_bij R (addBlock h0 m t) c
  have hb2 : Function.Bijective (fun ξ : Fin m → KR R =>
      ((Quotient.mk _ 1, ξ) : Quotient (QuotientGroup.rightRel
        (intSub R (lowW K (addBlock h0 m t).1 (addBlock h0 m t).2))) ×
        (Fin (addBlock h0 m t).1.sum → KR R))) := by
    constructor
    · intro a b h
      exact (Prod.ext_iff.1 h).2
    · rintro ⟨q₁, ξ⟩
      refine ⟨ξ, Prod.ext ?_ rfl⟩
      show Quotient.mk _ 1 = q₁
      rw [← Quotient.out_eq q₁, st_lowW_single m t (Quotient.out q₁)]
  have hc := hb.comp hb2
  convert hc using 2 with ξ
  show _ = Quotient.mk _ (sec_lowJ (addBlock h0 m t) c (Quotient.out _) (outV R ξ))
  rw [st_lowW_single m t (Quotient.out _)]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
