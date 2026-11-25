-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_under_integral_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:13.958826+00:00
-- url     : https://prove2.me/submissions/4b3688ea-d741-495d-9188-22494898fdb7

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_int_list_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_smul_list_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_word_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_rho


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
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by
  intro hW hWS hR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hT hF g hg
  obtain ⟨L, hLw, hLeq⟩ := hWS k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ ⟨WordKeyIdentity.glev0 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun x hx hxG => he x hx (WordKeyIdentity.glev0 hxG)⟩
  rw [hLeq _ _ _ hJck g hg hg.1]
  have key : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := fun cw hcw =>
    WordKeyIdentity.word_key hW hR D hT hF hg cw.2 (hLw cw hcw).1 ((hLw cw hcw).2.trans hnm)
  have hRHS : (∫ p, xiP D p • Q.CV k r Y (rho D p F) g ∂D.μSS) =
      ∫ p, (L.map fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g)).sum ∂D.μSS := by
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hLeq _ _ _ (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, WordKeyIdentity.smul_list_smul]
  rw [hRHS, WordKeyIdentity.int_list_smul D.μSS L (fun cw => cw.1) (fun cw p => xiP D p • Rw cw.2 (rho D p F) g)
    fun cw hcw => (key cw hcw).1]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [(key cw hcw).2]
end Formalism.FourierDecayAlt.P
