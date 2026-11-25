-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:16:10.604809+00:00
-- url     : https://prove2.me/submissions/afee0ef9-dbf0-4673-8803-7b177697ff5c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_le
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution {N : ℕ} {f f₂ : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) (h₂ : ZJ k r N f₂ g₀) :
    ZJ k r N (fun x => f x + f₂ x) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hfF₂, hv₂⟩ := h₂
  have hO : IsOpen (U ∩ U₂) := hU.inter hU₂
  have hx : g₀ ∈ U ∩ U₂ := ⟨hgU, hgU₂⟩
  have hF1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (U ∩ U₂) := hF.mono Set.inter_subset_left
  have hF2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ (U ∩ U₂) := hF₂.mono Set.inter_subset_right
  refine ⟨U ∩ U₂, fun x => F x + F₂ x, hO, hx, hF1.add hF2, ?_, ?_⟩
  · intro g hg hgl
    simp only [hfF g hg.1 hgl, hfF₂ g hg.2 hgl]
  · intro j hj
    show iteratedFDeriv ℝ j (F + F₂) g₀ = 0
    rw [← iteratedFDerivWithin_of_isOpen j hO hx,
      iteratedFDerivWithin_add_apply ((hF1 g₀ hx).of_le (jetT_le j)) ((hF2 g₀ hx).of_le (jetT_le j))
        hO.uniqueDiffOn hx,
      iteratedFDerivWithin_of_isOpen j hO hx, iteratedFDerivWithin_of_isOpen j hO hx, hv j hj, hv₂ j hj,
      add_zero]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
