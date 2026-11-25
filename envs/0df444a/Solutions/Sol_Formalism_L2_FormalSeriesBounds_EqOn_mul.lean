-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.EqOn.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:39.486168+00:00
-- url     : https://prove2.me/submissions/b586d943-4dd4-4751-9bc8-12e1f9fc9f16

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace EqOn
theorem _root_.solution {A : Set σ} {F G F' G' : MvPowerSeries σ K} (h : EqOn A F G) (h' : EqOn A F' G') :
    EqOn A (F * F') (G * G') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hs : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have h1 : (↑p.1.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.1 ≤ μ := hs ▸ le_self_add
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  have h2 : (↑p.2.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.2 ≤ μ := hs ▸ le_add_self
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  rw [h p.1 h1, h' p.2 h2]
end EqOn
end Formalism.L2.FormalSeriesBounds
