-- Prove2me | solution 1 for Formalism.L2.Th1.E.Power.ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:43.560902+00:00
-- url     : https://prove2.me/submissions/bbd9b18e-aa95-4199-a84e-4195efa26977

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin

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
variable {R : Type} [CommRing R] [IsDomain R]
namespace Formalism.L2.Th1.E.Power
theorem _root_.solution (g φ : ℕ → R) (k : ℕ) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → g (m + 1) * g 0 = (∏ j ∈ Finset.range m, φ (j + 1)) * g 1 * g m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hrec m hm
    have h3 := hne m (by omega)
    apply mul_right_cancel₀ h3
    rw [Finset.prod_range_succ]
    calc g (m + 1 + 1) * g 0 * g m = (g (m + 2) * g m) * g 0 := by ring
      _ = φ (m + 1) * g (m + 1) * (g (m + 1) * g 0) := by rw [h2]; ring
      _ = _ := by rw [h1]; ring
end Formalism.L2.Th1.E.Power
