-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_trn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:55.956647+00:00
-- url     : https://prove2.me/submissions/4b99e3ee-657e-43d9-9286-bab84354f222

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_abL_apply

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
theorem _root_.solution {m : ℕ∞} (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    {f : Mat k r → E} (hf : CkOn m (GV k r) f) : CkOn m (GV k r) (trn L a b f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf (a * g₀ * b) (gv_mul (gv_mul ha hg₀) hb)
  refine ⟨(abL a b) ⁻¹' U, fun g => L (f' (a * g * b)), hU.preimage (abL a b).continuous, ?_, ?_, ?_⟩
  · show abL a b g₀ ∈ U
    rw [abL_apply]; exact hgU
  · have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g => f' (abL a b g)) ((abL a b) ⁻¹' U) :=
      hc.comp (abL a b).contDiff.contDiffOn (fun g hg => hg)
    have h2 := (L.restrictScalars ℝ).contDiff.comp_contDiffOn h1
    refine h2.congr (fun g _ => ?_)
    simp [abL_apply]
  · intro g hg hgG
    show L (f (a * g * b)) = L (f' (a * g * b))
    have hg' : a * g * b ∈ U := by rw [← abL_apply]; exact hg
    rw [he _ hg' (gv_mul (gv_mul ha hgG) hb)]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
