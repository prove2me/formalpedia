-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:05:47.99379+00:00
-- url     : https://prove2.me/submissions/ad3f13fa-6314-4241-aece-dec6dc661ead

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_integral_list_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_list_smul_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (hJ : JF.JWords) (hW : JF.CVWordSum) (hR : JF.RwRho) : JF.CVUnderInt := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hCC g hg
  obtain ⟨hCk, hJW⟩ := hJ k r Wp Wq D A m F hThr hCC
  obtain ⟨L, hLw, hL⟩ := hW k r Y
  have hgG : g ∈ GV k r := hg.1
  obtain ⟨c0, hc0⟩ := hCC
  have hFm : CkOn ((m : ℕ) : ℕ∞) (GV k r) F := hc0.1
  have hFn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := sCkOn_mono (by exact_mod_cast hnm) hFm
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (JF.Om k r D.z D.z') (B.JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hg₀U, hc, hff⟩ := hCk g₀ ⟨glev0 hg₀.1, hg₀.2⟩
    refine ⟨U, F', hU, hg₀U, hc.of_le ?_, fun g hgU hgG => hff g hgU (glev0 hgG)⟩
    exact_mod_cast hnm
  have hcw : ∀ cw ∈ L,
      Integrable (fun p => JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g) D.μSS ∧
        Rw cw.2 (B.JF D F) g = ∫ p, JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g ∂D.μSS := by
    intro cw hcw
    have := hJW [] cw.2 (by simp) (hLw cw hcw).1 (by simpa using (hLw cw hcw).2.trans hnm) g hg
    simpa [B.dLR] using this
  rw [hL _ _ _ hJck g hg hgG]
  have e1 : (L.map fun cw => cw.1 • Rw cw.2 (B.JF D F) g).sum =
      (L.map fun cw => cw.1 • ∫ p, JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g ∂D.μSS).sum := by
    congr 1
    apply List.map_congr_left
    intro cw h
    rw [(hcw cw h).2]
  rw [e1, ← (integral_list_smul L (fun cw => cw.1)
    (fun cw p => JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g) (fun cw h => (hcw cw h).1)).2]
  apply integral_congr_ae
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  have hrho : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (B.rho D p F) := Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hFn
  rw [hL _ (GV k r) _ hrho g hgG hgG, list_smul_sum]
  congr 1
  apply List.map_congr_left
  intro cw h
  have this : Rw cw.2 (B.rho D p F) g = B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g :=
    hR k r Wp Wq D m F p hp hFm [] cw.2 (by simp) (fun X hX => ((hLw cw h).1 X hX).1)
      (by simpa using (hLw cw h).2.trans hnm) g hgG
  rw [this]
end Formalism.FourierDecayAlt.P.JFxB
