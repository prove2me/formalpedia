-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.ckOn_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:33:46.560782+00:00
-- url     : https://prove2.me/submissions/72f9b8f0-5b8f-4d1d-b05d-668f02586a1a

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_top_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hS : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop c d f))
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    CkOn (m : ℕ∞) (GV k r) (Top Eop u c d f) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁, hU₁, hg₁, hc₁, he₁⟩ := hf g₀ hg₀
  obtain ⟨U₂, f₂, hU₂, hg₂, hc₂, he₂⟩ := hS c d m f hf g₀ hg₀
  by_cases hcd : c = d
  · refine ⟨U₁ ∩ U₂, fun g => u • f₁ g + f₂ g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
    · have hle : ((m : ℕ∞) : WithTop ℕ∞) ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast Nat.le_succ m
      exact (((hc₁.of_le hle).const_smul u).mono Set.inter_subset_left).add
        (hc₂.mono Set.inter_subset_right)
    · intro g hg hgG
      rw [top_apply, if_pos hcd, he₁ g hg.1 hgG, he₂ g hg.2 hgG]
  · refine ⟨U₂, f₂, hU₂, hg₂, hc₂, ?_⟩
    intro g hg hgG
    rw [top_apply, if_neg hcd, zero_add, he₂ g hg hgG]
end Formalism.FourierDecayAlt.P.JFxB
