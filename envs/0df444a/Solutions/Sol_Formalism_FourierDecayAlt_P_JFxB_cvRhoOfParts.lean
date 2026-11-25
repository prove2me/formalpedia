-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvRhoOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:38.136271+00:00
-- url     : https://prove2.me/submissions/edd7cd47-6aa9-4609-831b-2ea1be8fe28f

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxB_rho_eq_trn__db6dceb877d0
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution : JF.CVRhoOfParts := by
  intro hL hR hP k r Wp Wq _ _ _ _ D Y f p hp hf g hg
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    gv_mul (gv_inv h1.1) (gv_inv h2.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := gv_mul h4.1 h3.1
  set a := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹
  set b := Matrix.of p.2.2 * Matrix.of p.2.1
  rw [rho_eq_trn', rho_eq_trn']
  have hf1 : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (fun x => f (a * x * b)) := by
    have := CkOn_trn (ContinuousLinearMap.id ℂ _) ha hb hf
    have e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) a b f = fun x => f (a * x * b) := by
      funext x; simp [trn]
    rwa [e] at this
  have hf2 : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (fun x => f (x * b)) := by
    have := CkOn_trn (ContinuousLinearMap.id ℂ _) gv_one hb hf
    have e : trn (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) 1 b f = fun x => f (x * b) := by
      funext x; simp [trn]
    rwa [e] at this
  have e1 : trn (Lq D p) a b f = fun x => Lq D p ((fun x => f (a * x * b)) x) := rfl
  rw [e1, hP k r _ _ Y (Lq D p) _ hf1 g hg]
  have e2 : (fun x => f (a * x * b)) = fun x => (fun x => f (x * b)) (a * x) := by
    funext x; rfl
  rw [e2, hL k r _ Y _ hf2 a ha g hg, hR k r _ Y f hf b hb (a * g) (gv_mul ha hg)]
  rfl
end Formalism.FourierDecayAlt.P.JFxB
