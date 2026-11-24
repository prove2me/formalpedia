-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordKeyIdentity.word_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:42:13.246377+00:00
-- url     : https://prove2.me/submissions/cd86267a-7e84-40a0-890e-166f6ee60eca

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordKeyIdentity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.WordKeyIdentity
theorem _root_.solution (hW : JWords) (hR : RwRho) (D : RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : InCC A m F) {g : Mat k r} (hg : g ∈ Om k r D.z D.z')
    (w : List (Mat k r)) (hw : ∀ X ∈ w, unitLie k r X) (hl : w.length ≤ m) :
    Integrable (fun p => xiP D p • Rw w (rho D p F) g) D.μSS ∧
      Rw w (JF D F) g = ∫ p, xiP D p • Rw w (rho D p F) g ∂D.μSS := by
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] w (by simp) hw (by simpa using hl) g hg
  simp only [List.map_nil] at hI hE
  have hae : (fun p => xiP D p • rho D p (dLR [] (w.map (AdR p)) F) g) =ᵐ[D.μSS]
      fun p => xiP D p • Rw w (rho D p F) g := by
    filter_upwards [B5.ae_inSS D] with p hp
    have := hR k r Wp Wq D m F p hp hCk [] w (by simp) (fun X hX => (hw X hX).1) (by simpa using hl) g hg.1
    simp only [List.map_nil] at this
    rw [← this]
    rfl
  exact ⟨hI.congr hae, by rw [← integral_congr_ae hae]; exact hE⟩
end Formalism.FourierDecayAlt.P.WordKeyIdentity
