-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:08.359796+00:00
-- url     : https://prove2.me/submissions/2e3bb9a9-f316-44f0-92bd-e645f3d171f6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_len_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_unit_lie

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
theorem _root_.solution {A : ℝ} {m : ℕ} {F F' : Mat k r → E} {c c' : ℝ} (hF : CCle A m F c) (hF' : CCle A m F' c') :
    CCle A m (fun g => F g + F' g) (c + c') := by
  obtain ⟨hc, hb⟩ := hF
  obtain ⟨hc', hb'⟩ := hF'
  refine ⟨CkOn_add hc hc', fun u v hu hv hl g hg => ?_⟩
  have hl' : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
    rw [len_LR]; exact_mod_cast hl
  have hw : ∀ x ∈ wL u ++ wR v, inLie k r x.2 := lie_LR (unit_lie hu) (unit_lie hv)
  have e : dLR u v (fun g => F g + F' g) g = dLR u v F g + dLR u v F' g := by
    rw [dLR_eq, dLR_eq, dLR_eq]
    exact Dw_add hw (sCkOn_mono hl' hc) (sCkOn_mono hl' hc') g hg
  rw [e]
  have h1 := hb u v hu hv hl g hg
  have h2 := hb' u v hu hv hl g hg
  have h3 := norm_add_le (dLR u v F g) (dLR u v F' g)
  have h4 : 0 ≤ gN g ^ A := Real.rpow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
  calc gN g ^ A * ‖dLR u v F g + dLR u v F' g‖ ≤ gN g ^ A * (‖dLR u v F g‖ + ‖dLR u v F' g‖) :=
        mul_le_mul_of_nonneg_left h3 h4
    _ ≤ c + c' := by rw [mul_add]; exact add_le_add h1 h2
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
