-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.phiR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:58:38.582162+00:00
-- url     : https://prove2.me/submissions/bd227bb3-0f34-4024-a855-0879e78c2442

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScalBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_dlast_pos

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
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiR k r D.z D.z' g‖ ≤ C0 := by
  set T := Tz k r D.z * Tz k r D.z' with hT
  have hT0 : 0 < T := mul_pos D.T_pos D.T'_pos
  refine ⟨1 + 1 / T, fun g hg => ?_⟩
  have hG := hg.2
  have h1 := dlast_pos D hε hG
  have hpos : 0 < Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) := lt_of_lt_of_le hε h1
  unfold Gf at hG
  set a := Complex.normSq (Dmin k r D.z D.z' g ⟨r, by omega⟩)
  set b := Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1)))
  have hsq : ‖phiR k r D.z D.z' g‖ ^ 2 = a / b := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [phiR, Complex.normSq_div]
    rfl
  have hle : a / b ≤ 1 / T := by
    rw [div_le_div_iff₀ hpos hT0]
    nlinarith
  have hx := norm_nonneg (phiR k r D.z D.z' g)
  nlinarith [sq_nonneg (‖phiR k r D.z D.z' g‖ - 1)]
end Formalism.FourierDecayAlt.P.CutMP.JA
