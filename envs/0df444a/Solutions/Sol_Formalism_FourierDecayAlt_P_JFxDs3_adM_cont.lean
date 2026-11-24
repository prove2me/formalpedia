-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs3.adM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:24.619205+00:00
-- url     : https://prove2.me/submissions/084aff42-4fcb-4f7d-a471-0c34f3b12fab

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sL_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sR_mem
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JFxDs3
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (x : Bool × Mat k r) :
    ContinuousOn (fun p => (adM p x).2) {p : SS k r | D.inSS p} := by
  obtain ⟨b, X⟩ := x
  have hof : ∀ q : SS k r → (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ), Continuous q →
      Continuous fun p => (Matrix.of (q p) : Mat k r) := fun q hq => hq
  have hcL : Continuous fun p : SS k r => sL p := by
    unfold sL; exact (hof _ (by fun_prop)).mul (hof _ (by fun_prop))
  have hcR : Continuous fun p : SS k r => sR p := by
    unfold sR; exact (hof _ (by fun_prop)).mul (hof _ (by fun_prop))
  have hinvOn : ∀ s : SS k r → Mat k r, Continuous s → (∀ p, D.inSS p → s p ∈ GV k r) →
      ContinuousOn (fun p => (s p)⁻¹) {p | D.inSS p} := by
    intro s hs hG p hp
    have hy' : (s p)ᴴ * Hpk k r * s p = Hpk k r := hG p hp
    have hl : (Hpk k r * (s p)ᴴ * Hpk k r) * s p = 1 := by
      simp only [mul_assoc] at hy' ⊢; rw [hy', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
    obtain ⟨u, hu⟩ := Matrix.isUnit_det_of_left_inverse hl
    have hc : ContinuousAt Inv.inv (s p) :=
      continuousAt_matrix_inv _ (by rw [← hu]; exact NormedRing.inverse_continuousAt u)
    exact (hc.comp hs.continuousAt).continuousWithinAt
  cases b
  · show ContinuousOn (fun p => (sR p)⁻¹ * X * sR p) {p | D.inSS p}
    exact ((hinvOn _ hcR fun p hp => JFxDs2.sR_mem hp).mul continuousOn_const).mul hcR.continuousOn
  · show ContinuousOn (fun p => (sL p)⁻¹ * X * sL p) {p | D.inSS p}
    exact ((hinvOn _ hcL fun p hp => JFxDs2.sL_mem hp).mul continuousOn_const).mul hcL.continuousOn
end Formalism.FourierDecayAlt.P.JFxDs3
