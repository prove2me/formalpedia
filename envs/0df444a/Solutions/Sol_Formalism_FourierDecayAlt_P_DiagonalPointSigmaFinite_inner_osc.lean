-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.inner_osc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:49.645059+00:00
-- url     : https://prove2.me/submissions/c1421494-0ebf-464c-b80d-ebd58a3a822f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_derivBound_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_singleton_subset_detSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_one_le_tau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (hOm : OmConverges) (hCut : CutPhiBound) (hIn : InnerXY) {m : ℕ} {β : ℂ} {Kc : Set ℂ}
    (h0 : (0 : ℂ) ∉ Kc) {Φ : Mat (m + 1 + 1) → V} {A K ε : ℝ} {k : ℕ}
    (hA : ((m : ℝ) + 1) * ((m : ℝ) + 4) < A) (hε : 0 ≤ ε)
    (hΦ : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ)
    {t c : ℂ} (ht : t ≠ 0) (ht1 : ‖t‖ ≤ 1) (hD : c * t ^ (m + 1) ∈ Kc) :
    Integrable (blockIntegrand β (m + 1) (cutPhi (‖t‖ ^ (-ε)) Φ) t c) (muBlock β (m + 1)) ∧
    Integrable (blockIntegrand β (m + 1) (cutPhiC (‖t‖ ^ (-ε)) Φ) t c) (muBlock β (m + 1)) ∧
    Integrable (oscIn β m ε Φ (c * t ^ (m + 1)) t) (muXY β m) ∧
      ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) • OmBlock β (m + 1) (cutPhi (‖t‖ ^ (-ε)) Φ) t c =
        ∫ p : XY m, oscIn β m ε Φ (c * t ^ (m + 1)) t p ∂(muXY β m) := by
  obtain ⟨C, hC⟩ := hCut (m + 1 + 1) 0
  have hc : c ≠ 0 := by
    rintro rfl
    apply h0; simpa using hD
  have hΦ0 := derivBound_mono hΦ (Nat.zero_le k) (singleton_subset_detSet (m := m) hD)
  obtain ⟨hC1, hC2⟩ := hC V Φ _ _ (‖t‖ ^ (-ε)) (one_le_tau ht ht1 hε) hΦ0
  have e : (fun Z : Mat (m + 1 + 1) => C * (K * min 1 (‖Z‖ ^ (-A)))) =
      fun Z => (C * K) * min 1 (‖Z‖ ^ (-A)) := by
    funext Z; ring
  rw [e] at hC1 hC2
  have i1 := (hOm m β A (C * K) hA V _ t c ht hc hC1).1
  have i2 := (hOm m β A (C * K) hA V _ t c ht hc hC2).1
  obtain ⟨j1, j2⟩ := hIn m β t c ht V _ i1
  exact ⟨i1, i2, j1, j2⟩
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
