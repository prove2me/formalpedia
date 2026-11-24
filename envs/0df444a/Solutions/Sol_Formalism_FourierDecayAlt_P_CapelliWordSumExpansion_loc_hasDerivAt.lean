-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:48.154903+00:00
-- url     : https://prove2.me/submissions/18978f89-a616-4334-9df4-f53f54835d51

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution {m : ℕ∞} (hm : 1 ≤ m) {f : Mat k r → E} {g X : Mat k r} (h : Loc m f g)
    (hg : g ∈ GV k r) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), f (g * NormedSpace.exp ((t : ℂ) • X)) = f' (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hmem] with t ht
    exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  have hf'd : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [hγ0]
    exact (hf'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by exact_mod_cast (show m ≠ 0 from fun h0 => by simp [h0] at hm))
  exact ((hf'd.comp (0 : ℝ) hγ.differentiableAt).congr_of_eventuallyEq hev).hasDerivAt
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
