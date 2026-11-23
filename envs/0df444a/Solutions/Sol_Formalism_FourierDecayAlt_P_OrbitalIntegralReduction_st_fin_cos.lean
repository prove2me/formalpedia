-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_fin_cos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:22.397791+00:00
-- url     : https://prove2.me/submissions/ac576275-6f37-4c81-a053-9e9688fa39ea

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_pt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_lowW_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite


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
theorem _root_.solution (hD : LocalDatum K R ψ) (w : Point K) (π : Kˣ) :
    {q : Cos R w | IsInt R ((π : K) • orbZ w (rep R q))}.Finite := by
  have key := integral_points_finite K R ψ hD (w.1, fun b => π * w.2 b)
  have gen : ∀ H : Subgroup (GL (Fin w.1.sum) K), H = lowW K w.1 (fun b => π * w.2 b) →
      {q : Quotient (QuotientGroup.rightRel (intSub R H)) ×
        (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) |
        IsInt R (sec_m (Quotient.out q.1) * ((π : K) • pt w.1 w.2) *
          sec_m (Quotient.out q.2))}.Finite := by
    intro H hH
    subst hH
    have e : ((π : K) • pt w.1 w.2) = pt w.1 (fun b => π * w.2 b) := (st_pt_smul _ _ _).symm
    rw [e]
    exact key
  have h2 := gen (lowW K w.1 w.2) (st_lowW_smul w.1 w.2 π).symm
  refine h2.subset ?_
  intro q hq
  have hq' : IsInt R ((π : K) • (sec_m (Quotient.out q.1) * pt w.1 w.2 * sec_m (Quotient.out q.2))) := hq
  show IsInt R (sec_m (Quotient.out q.1) * ((π : K) • pt w.1 w.2) * sec_m (Quotient.out q.2))
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hq'
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
