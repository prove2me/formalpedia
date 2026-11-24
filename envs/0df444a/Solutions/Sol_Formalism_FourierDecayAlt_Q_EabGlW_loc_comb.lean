-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.loc_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:48:01.365401+00:00
-- url     : https://prove2.me/submissions/4eb4b8e5-78e9-41a7-a3a5-1e04b74d34ab

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_rd_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {G : Set (Matrix (Fin n) (Fin n) ℂ)} {V A B : Matrix (Fin n) (Fin n) ℂ}
    (hV : Flow G V) (hA : Flow G A) (hB : Flow G B)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) (c : ℂ) :
    RdV V (fun h => RdV A f h + c • RdV B f h) g = RdV V (RdV A f) g + c • RdV V (RdV B f) g := by
  have hU := hL.1
  have hF := hL.2.1
  have hsA := loc_smooth hU hF A
  have hsB := loc_smooth hU hF B
  have hLc : LocExt G (fun h => RdV A f h + c • RdV B f h)
      (fun k => fderiv ℝ F k (k * A) + c • fderiv ℝ F k (k * B)) U :=
    ⟨hU, hsA.add (hsB.const_smul c), fun h hh hhG => by
      show RdV A f h + c • RdV B f h = fderiv ℝ F h (h * A) + c • fderiv ℝ F h (h * B)
      rw [loc_ext hA hL hh hhG, loc_ext hB hL hh hhG]⟩
  rw [loc_ext hV hLc hg hgG, loc_ext hV (loc_rd_ext hA hL) hg hgG,
    loc_ext hV (loc_rd_ext hB hL) hg hgG]
  have dA : DifferentiableAt ℝ (fun k => fderiv ℝ F k (k * A)) g :=
    (hsA.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have dB : DifferentiableAt ℝ (fun k => fderiv ℝ F k (k * B)) g :=
    (hsB.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hD : HasFDerivAt (fun k => fderiv ℝ F k (k * A) + c • fderiv ℝ F k (k * B))
      (fderiv ℝ (fun k => fderiv ℝ F k (k * A)) g + c • fderiv ℝ (fun k => fderiv ℝ F k (k * B)) g) g :=
    dA.hasFDerivAt.add (dB.hasFDerivAt.const_smul c)
  rw [hD.fderiv]
  simp
end Formalism.FourierDecayAlt.Q.EabGlW
