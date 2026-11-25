-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.aestronglyMeasurable_mainD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:34.585463+00:00
-- url     : https://prove2.me/submissions/1b3570b9-e716-418c-b2ad-3095741e5777

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_mainD_ae_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
section abar
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
private lemma measurable_R_lemma (s k : ℕ) : Measurable (NthRootMeasurability.R s k) := by
  unfold NthRootMeasurability.R
  exact measurable_const.mul (measurable_id.pow_const _)
private lemma continuous_psi_lemma_2 (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop
end abar
section moving
end moving
section cut
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end cut
end
end Formalism.FourierDecayAlt.P.PBK
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (x : ℂ) : AEStronglyMeasurable (mainD s β ε bt x) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (mainD_ae_eq hs β hε bt x).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ =>
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D))) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    have hp : Measurable fun D : ℂ => G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) :=
      (continuous_psi_lemma_2 β).measurable.comp ((measurable_const.mul hR).mul measurable_const)
    exact hp.stronglyMeasurable.smul (hbt.comp_measurable hR)
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1
  funext D
  simp only [Finset.sum_apply]
end Formalism.FourierDecayAlt.P.PBK
