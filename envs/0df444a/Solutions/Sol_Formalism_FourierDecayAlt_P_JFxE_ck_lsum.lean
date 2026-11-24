-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ck_lsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:53:55.867603+00:00
-- url     : https://prove2.me/submissions/4a673ea6-f21e-4981-989d-4fb1328a7e15

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Rep_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {m : ℕ∞} (L : List (ℂ × (Mat k r → E))) (h : ∀ p ∈ L, CkOn m (GV k r) p.2) :
    CkOn m (GV k r) (fun x => (L.map fun p => p.1 • p.2 x).sum) := by
  induction L with
  | nil =>
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => by simp⟩
  | cons p L ih =>
    intro g₀ hg₀
    obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := h p (by simp) g₀ hg₀
    obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := ih (fun q hq => h q (by simp [hq])) g₀ hg₀
    refine ⟨U1 ∩ U2, fun x => p.1 • f1 x + f2 x, hU1.inter hU2, ⟨hg1, hg2⟩,
      ((hc1.mono Set.inter_subset_left).const_smul p.1).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro g hg hgG
    simp only [List.map_cons, List.sum_cons]
    rw [he1 g hg.1 hgG]
    congr 1
    exact he2 g hg.2 hgG
end Formalism.FourierDecayAlt.P.JFxE
