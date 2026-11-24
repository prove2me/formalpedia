-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_fdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:49.361815+00:00
-- url     : https://prove2.me/submissions/81145ee2-3101-4fbe-9f92-85e2599df615

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_fdb
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_lss_of_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (K : Set F)
    (hK : ∀ g ∈ S, ψ g ∈ K) (α n : ℕ) (M : ℝ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w ψ g‖ ≤ M * gN g ^ (α * w.length))
    (Φ : F → E) (hΦ : ContDiff ℝ ∞ Φ) (hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) :
    UBL (fun g => Φ (ψ g)) S n 0 α := by
  obtain ⟨C, hC, hb⟩ := fdb ψ hψ S K hK gN (fun g hg => gN_ge_one (hSG hg)) α 0 M n
    (fun w hw hne g hg => by simpa using H w hw hne g (hSG hg)) n E Φ hΦ hB
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff (hΦ.comp hψ) S⟩
  have hlen : w.length ≤ n := by
    obtain ⟨u, v, -, -, hl, rfl⟩ := hw
    simpa [wL, wR] using hl
  simpa using hb w hw hlen g hg
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
