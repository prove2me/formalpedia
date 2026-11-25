-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.mainD_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:00:59.685776+00:00
-- url     : https://prove2.me/submissions/5cb7ec89-e426-461d-b221-60315fbd74b1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_sum_rootSet_eq_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (x : ℂ) :
    mainD s β ε bt x =ᵐ[volume] fun D => ∑ k ∈ Finset.range s,
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D)) := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold mainD
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]
end Formalism.FourierDecayAlt.P.PBK
