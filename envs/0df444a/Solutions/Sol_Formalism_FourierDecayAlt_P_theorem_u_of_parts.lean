-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theorem_u_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:00:42.501916+00:00
-- url     : https://prove2.me/submissions/4c8bef3c-e64f-4a98-bc43-a1b15b28715a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_norm_iter_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_iter_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_lamC_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_lamC_norming
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_sc_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_sc_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_unit_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
namespace Formalism.FourierDecayAlt.P.Ux11
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.TheoremUOfParts := by
  intro hU41 hSupp hW k p s ρ σ d hd hs K hK hK0 m mm Q A₁ hQ ha
  obtain ⟨C, hC⟩ := hU41 k p s ρ σ d hd hs K hK hK0 m mm Q A₁ hQ ha
  refine ⟨C, fun z z' E _ _ _ F₁ B₁ hStar => ?_⟩
  obtain ⟨hint, hcc, hder⟩ := hC z z' E F₁ B₁ hStar
  refine ⟨hint, fun Z hZ hKZ γ hγ => hSupp k p s ρ σ d z z' E F₁ A₁ B₁ Q K hd hStar Z hZ hKZ γ hγ, ?_⟩
  intro S V _ _ _ M hS
  have hex : ∀ Z : G.Mat s, ∃ v : V, G.detM Z ≠ 0 →
      ∀ γ ∈ B.GV k ρ, M.ev v γ = U.PhiFun k ρ σ d z z' F₁ Z γ := by
    intro Z
    by_cases hZ : G.detM Z ≠ 0
    · obtain ⟨v, hv⟩ := M.surj _ ⟨_, hcc Z hZ⟩ (hS Z hZ)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hZ⟩
  choose Φ hΦ using hex
  refine ⟨Φ, hΦ, ?_⟩
  have hdet : Continuous (fun Z : G.Mat s => G.detM Z) := by
    unfold G.detM
    exact Continuous.matrix_det continuous_id
  have hΩ : IsOpen {Z : G.Mat s | G.detM Z ≠ 0} := isOpen_ne_fun hdet continuous_const
  have hbd : ContinuousOn (fun Z : G.Mat s => C * B₁ * (1 + ‖Z‖) ^ (-(U.a1 (p + s + ρ) A₁ m mm)))
      {Z : G.Mat s | G.detM Z ≠ 0} :=
    (continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
      (fun Z => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg Z)).ne'))).continuousOn
  have key : ∀ (t : Idx k ρ mm), ∀ Z ∈ {Z : G.Mat s | G.detM Z ≠ 0}, lamC M t (Φ Z) =
      sc E (B.gN t.1.2.2 ^ (U.a1 (p + s + ρ) A₁ m mm))
        (B.dLR t.1.1 t.1.2.1 (U.PhiFun k ρ σ d z z' F₁ Z) t.1.2.2) := by
    intro t Z hZ
    rw [lamC_apply, sc_apply]
    congr 1
    rw [BetaSesquilinearity.dLR_eq, BetaSesquilinearity.dLR_eq]
    exact BetaSesquilinearity.Dw_congr (BetaSesquilinearity.lie_LR (BetaSesquilinearity.unit_lie t.2.1) (BetaSesquilinearity.unit_lie t.2.2.1)) (hΦ Z hZ) _ t.2.2.2.2
  obtain ⟨hcont, hbound⟩ := hW (G.Mat s) V E (Idx k ρ mm) (lamC M) (lamC_norming M)
    {Z : G.Mat s | G.detM Z ≠ 0} Φ m (fun Z => C * B₁ * (1 + ‖Z‖) ^ (-(U.a1 (p + s + ρ) A₁ m mm)))
    hΩ hbd
    (fun t => ((sc E _).contDiff.comp_contDiffOn
      (hder t.1.1 t.1.2.1 t.2.1 t.2.2.1 t.2.2.2.1 t.1.2.2 t.2.2.2.2).1).congr (fun Z hZ => key t Z hZ))
    (fun t q hq Z hZ => by
      rw [iter_congr hΩ (key t) hZ q]
      have h2 := (hder t.1.1 t.1.2.1 t.2.1 t.2.2.1 t.2.2.2.1 t.1.2.2 t.2.2.2.2).2 q hq Z hZ
      calc _ ≤ ‖sc E (B.gN t.1.2.2 ^ (U.a1 (p + s + ρ) A₁ m mm))‖ *
            ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s =>
              B.dLR t.1.1 t.1.2.1 (U.PhiFun k ρ σ d z z' F₁ Z') t.1.2.2) Z‖ :=
            norm_iter_comp _ (hder t.1.1 t.1.2.1 t.2.1 t.2.2.1 t.2.2.2.1 t.1.2.2 t.2.2.2.2).1 hΩ hZ
              (by exact_mod_cast hq)
        _ ≤ B.gN t.1.2.2 ^ (U.a1 (p + s + ρ) A₁ m mm) *
            ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s =>
              B.dLR t.1.1 t.1.2.1 (U.PhiFun k ρ σ d z z' F₁ Z') t.1.2.2) Z‖ :=
            mul_le_mul_of_nonneg_right (sc_norm _ (gNa_nonneg _ _)) (norm_nonneg _)
        _ ≤ _ := h2)
  exact fun Z hZ => ⟨hcont.contDiffAt (hΩ.mem_nhds hZ), fun q hq => hbound q hq Z hZ⟩
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.Ux11
