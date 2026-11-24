-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.intAll_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:47.598129+00:00
-- url     : https://prove2.me/submissions/6a83552d-c1c3-42a7-a572-0c81d5c3b850

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_ae_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_limit_fourier
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_psiL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_Lm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_decay_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_g_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_gramLoc_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hB : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 →
      ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
          ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c‖ ≤
          C * ((1 + ‖l‖) ^ 3)⁻¹) :
    KB.IntAll S := by
  intro v ε hε i hi1 hi2 w h h' hh hh'
  obtain ⟨C, hC⟩ := hB v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ h h' hh hh'
  have hC0 : 0 ≤ C := by
    have := ((hC 0).2 0).trans' (norm_nonneg _)
    simpa using this
  have H := fun n => hInt n v ε hε i hi1 hi2 w h h' hh hh'
  choose φ hφc hφe hφb hφi using H
  have hg := g_ge_one S hg1 hg2
  have hT : ∀ n w', ‖𝓕 (φ n) w'‖ ≤ 8 * C * dw w' := by
    intro n w'
    set l : ℂ := (((-(S.g : ℝ) / 2 : ℝ)) : ℂ) * conj w' with hl
    have hLm : Lm S.g l = w' := Lm_inv S.g (by linarith) w'
    have he : 𝓕 (φ n) w' = ∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) *
        KB.psiL S l c := by
      rw [Real.fourier_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero] with c hc
      rw [psiL_eq, hLm, hφe n c hc]
    rw [he]
    have h8 := mul_le_mul_of_nonneg_left (decay_scale S.g hg w') hC0
    calc _ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹ := (hC n).2 l
      _ ≤ C * (8 * dw w') := h8
      _ = 8 * C * dw w' := by ring
  obtain ⟨ψ, hψc, hψe, hψb, hψi⟩ := limit_fourier
    (fun n c => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]))
    (fun c => S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) φ C (8 * C) hφc hφe
    (fun c => gramLoc_tendsto S RR hconv v hε i w _ _) (fun n c hc => (hC n).1 c hc) hT
  refine ⟨ψ, hψc, hψe, ⟨C, hψb⟩, ?_⟩
  have h1 : Tendsto (fun n => ∫ c, φ n c) atTop
      (𝓝 (((KB.dlB S i 1 : ℝ) : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h')) := by
    have : (fun n => ∫ c, φ n c) =
        fun n => ((KB.dlB S i 1 : ℝ) : ℂ) * (KB.withRR S (RR n)).gramLoc v ε (i - 1) (w.1 v) h h' :=
      funext fun n => hφi n
    rw [this]
    exact (gramLoc_tendsto S RR hconv v hε (i - 1) w h h').const_mul _
  exact tendsto_nhds_unique hψi h1
end Formalism.FourierDecayAlt.P.PBB.K8
