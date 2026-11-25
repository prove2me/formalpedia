-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliUnderIntegral.cvUnderInt_of_jWords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:21.698748+00:00
-- url     : https://prove2.me/submissions/896972d4-f79e-4fe9-b106-da37cf34c4e1

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliUnderIntegral_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliUnderIntegral_integral_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_cvWordSumG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
namespace CapelliUnderIntegral
theorem _root_.solution : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt := by
  intro hJW hRR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hF g hg
  obtain ⟨L, hLw, hL⟩ := CapelliWordSumExpansion.cvWordSumG k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJ := hJW k r Wp Wq D A m F hThr hF
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨(CapelliUnderIntegral.glev0 g₀).2 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm),
      fun g' hg'U hg'G => he g' hg'U ((CapelliUnderIntegral.glev0 g').2 hg'G)⟩
  have hw : ∀ cw ∈ L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ m :=
    fun cw h => ⟨(hLw cw h).1, (hLw cw h).2.trans hnm⟩
  have hword : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := by
    intro cw hcw
    obtain ⟨hint, heq⟩ := hJ.2 [] cw.2 (by simp) (hw cw hcw).1 (by simpa using (hw cw hcw).2) g hg
    have hae : (fun p => xiP D p • rho D p (dLR ([].map (AdL p)) (cw.2.map (AdR p)) F) g) =ᵐ[D.μSS]
        (fun p => xiP D p • Rw cw.2 (rho D p F) g) := by
      filter_upwards [B5.ae_inSS D] with p hp
      have e := hRR k r Wp Wq D m F p hp hCk [] cw.2 (by simp)
        (fun X hX => ((hw cw hcw).1 X hX).1) (by simpa using (hw cw hcw).2) g hg.1
      simp only [List.map_nil] at e ⊢
      rw [← e]
      rfl
    exact ⟨hint.congr hae, (show Rw cw.2 (JF D F) g = dLR [] cw.2 (JF D F) g from rfl).trans
      (heq.trans (integral_congr_ae hae))⟩
  rw [hL _ _ (JF D F) hJck g hg hg.1]
  have hae2 : (fun p => xiP D p • Q.CV k r Y (rho D p F) g) =ᵐ[D.μSS]
      (fun p => (L.map (fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g))).sum) := by
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hL _ _ (rho D p F) (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left (fun cw _ => ?_)
    simp only [Function.comp_apply]
    exact smul_comm _ _ _
  rw [integral_congr_ae hae2, CapelliUnderIntegral.integral_map_sum L
    (fun cw p => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g))
    (fun cw hcw => (hword cw hcw).1.smul cw.1)]
  congr 1
  refine List.map_congr_left (fun cw hcw => ?_)
  rw [integral_smul, (hword cw hcw).2]
end CapelliUnderIntegral
end Formalism.FourierDecayAlt.P
