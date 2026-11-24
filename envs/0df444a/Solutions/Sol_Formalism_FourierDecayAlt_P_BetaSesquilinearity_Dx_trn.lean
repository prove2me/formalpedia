-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_trn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:16.039484+00:00
-- url     : https://prove2.me/submissions/559f68c1-4308-4e8e-91ea-d2bcc90061af

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) {X : Mat k r}
    (hX : inLie k r X) {f : Mat k r → E} (hf : CkOn 1 (GV k r) f) :
    ∀ g ∈ GV k r, Dx (false, X) (trn L a b f) g = trn L a b (Dx (false, b⁻¹ * X * b) f) g := by
  intro g hg
  have hb' := gv_unit hb
  have hagb : a * g * b ∈ GV k r := gv_mul (gv_mul ha hg) hb
  have hY : inLie k r (b⁻¹ * X * b) := lie_conj hX hb
  have hφ := CkOn_diff (x := (false, b⁻¹ * X * b)) hY hf hagb hagb
  have hc : ∀ t : ℝ, crv (false, b⁻¹ * X * b) (a * g * b) t =
      a * g * b * NormedSpace.exp ((t : ℂ) • (b⁻¹ * X * b)) := fun t => rfl
  simp only [hc] at hφ
  have hL := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hφ
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at hL
  have e : ∀ t : ℝ, a * (g * NormedSpace.exp ((t : ℂ) • X)) * b =
      a * g * b * NormedSpace.exp ((t : ℂ) • (b⁻¹ * X * b)) := by
    intro t
    have h1 : (t : ℂ) • (b⁻¹ * X * b) = b⁻¹ * ((t : ℂ) • X) * b := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).mpr hb')]
    have h2 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hb'
    calc a * (g * NormedSpace.exp ((t : ℂ) • X)) * b
        = a * g * (b * b⁻¹) * NormedSpace.exp ((t : ℂ) • X) * b := by
          rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = a * g * b * (b⁻¹ * NormedSpace.exp ((t : ℂ) • X) * b) := by simp only [Matrix.mul_assoc]
  show deriv (fun t : ℝ => L (f (a * (g * NormedSpace.exp ((t : ℂ) • X)) * b))) 0 =
    L (Dx (false, b⁻¹ * X * b) f (a * g * b))
  simp only [e]
  exact hL.deriv
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
