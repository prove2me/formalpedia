-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.ckOn_phiD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:14:35.581245+00:00
-- url     : https://prove2.me/submissions/0a9993a0-8aa4-415d-9d31-dfcd1e439ccc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScalBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_dlast_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_open_dlast
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_Dmin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
noncomputable section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.JA
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiD k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiD k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => (starRingEnd ℂ) (Dmin k r D.z D.z' g (Fin.last (r + 1)))) :=
    Complex.conjCLE.contDiff.comp h1
  refine (h1.contDiffOn.mul (h2.contDiffOn.inv (fun x hx => by simpa using hx))).congr (fun x _ => ?_)
  simp [phiD, div_eq_mul_inv]
end Formalism.FourierDecayAlt.P.CutMP.JA
