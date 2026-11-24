-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Pr.leib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:43.19481+00:00
-- url     : https://prove2.me/submissions/5d991ab7-7c9c-4996-b004-71d512639835

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_apz

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
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Pr
theorem _root_.solution (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) {x : Bool × Mat k r}
    (hx : inLie k r x.2) (h : Pr O UU 1 a Φ) :
    ∀ g ∈ GV k r, Dx x (ap a Φ) g = ap (Dx x a) Φ g + ap a (Dx x Φ) g := by
  intro g hg
  rcases hcov g hg with hgO | hgU
  · have h1 : Dx x (ap a Φ) g = 0 := Dx_vanish hO hx (Pr.apz (h.mono (by simp))) g hg hgO
    have h2 : Φ g = 0 := h.hz g hg hgO
    have h3 : Dx x Φ g = 0 := Dx_vanish hO hx h.hz g hg hgO
    rw [h1]
    show (0 : E') = Dx x a g (Φ g) + a g (Dx x Φ g)
    rw [h2, h3, map_zero, map_zero, add_zero]
  · have ha := CkOn_diff hx h.ha hgU hg
    have hΦ := CkOn_diff hx h.hΦ hg hg
    have ha' := (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
    have hp := ha'.clm_apply hΦ
    have e1 : ∀ A : E →L[ℂ] E', (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ) A =
        A.restrictScalars ℝ := fun A => rfl
    simp only [Function.comp_def, crv_zero, e1, ContinuousLinearMap.coe_restrictScalars'] at hp
    rw [Dx_eq]
    exact hp.deriv
end Pr
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
