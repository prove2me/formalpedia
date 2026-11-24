-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.loc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:57.83621+00:00
-- url     : https://prove2.me/submissions/ff268d6f-a4ef-4d98-8d8f-ddabbcf89e33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {m : ℕ∞} {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m Φ₁ g) (h₂ : Loc m Φ₂ g) (c : ℂ) :
    Loc m (fun x => Φ₁ x + c • Φ₂ x) g := by
  obtain ⟨U₁, f₁, hU₁, hg₁, hc₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂, hU₂, hg₂, hc₂, he₂⟩ := h₂
  refine ⟨U₁ ∩ U₂, fun x => f₁ x + c • f₂ x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact (hc₁.mono Set.inter_subset_left).add
      ((hc₂.mono Set.inter_subset_right).const_smul (c : ℂ))
  · intro x hx hxG
    show Φ₁ x + c • Φ₂ x = f₁ x + c • f₂ x
    rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
