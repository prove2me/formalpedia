-- Prove2me | solution 1 for Formalism.L2.Th1.E.Power.sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:41.187008+00:00
-- url     : https://prove2.me/submissions/f0a24b09-a374-48a7-9ea9-20bb4d59aaaf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Power_sum_add
import Theorems.Thm_Formalism_L2_Th1_E_Power_sum_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Power
namespace Formalism.L2.Th1.E.Power
theorem _root_.solution {A : Type} [AddCommGroup A] [Finite A] (M₀ : A → ℝ) (Q : A) (c : ℝ)
    (h : ∀ P : A, M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * c) : c = 0 := by
  have := Fintype.ofFinite A
  have hs : ∑ P : A, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P) = ∑ _P : A, 2 * c :=
    Finset.sum_congr rfl fun P _ => h P
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_add, sum_sub, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this.ne'
  have : (Fintype.card A : ℝ) * (2 * c) = 0 := by rw [← hs]; ring
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hc
  · linarith
end Formalism.L2.Th1.E.Power
