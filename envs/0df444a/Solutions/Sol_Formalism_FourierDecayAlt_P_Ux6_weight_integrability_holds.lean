-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.weight_integrability_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:51.497091+00:00
-- url     : https://prove2.me/submissions/fcbb4e48-65fc-4648-83cd-229ff7efaf23

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_rpow3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_intH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_intRC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution : WeightIntegrable := by
  intro k p s ρ σ a hs ha
  set r := p + s + ρ
  set n := 2 * (p + s + ρ) + k + 1
  have hrn : ∀ D : ℕ, D ≤ 2 * r * n → (D : ℝ) < a := fun D hD =>
    lt_of_le_of_lt (by
      have : ((D : ℕ) : ℝ) ≤ ((2 * r * n : ℕ) : ℝ) := by exact_mod_cast hD
      simpa [r, n] using this) ha
  have iR := intRC k (p + s) ρ a (hrn _ (by simp only [r, n]; nlinarith))
  have iH := intH p s σ a (hrn _ (by simp only [r, n]; nlinarith)) (hrn _ (by simp only [r, n]; nlinarith))
    (hrn _ (by simp only [r, n]; nlinarith))
  have h := (iR.mul_prod iR).mul_prod iH
  refine h.congr (ae_of_all _ fun ξ => ?_)
  simp only [wt]
  rw [rpow3 (by positivity) (by positivity) (by unfold wtH; positivity)]
end Formalism.FourierDecayAlt.P.Ux6
