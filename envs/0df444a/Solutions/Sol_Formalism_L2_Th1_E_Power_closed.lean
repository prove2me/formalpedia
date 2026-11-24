-- Prove2me | solution 1 for Formalism.L2.Th1.E.Power.closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:08.211256+00:00
-- url     : https://prove2.me/submissions/ded30cb5-6716-4a9a-b427-1f551547797c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Power_tri_succ
import Theorems.Thm_Formalism_L2_Th1_E_Power_ratio

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
theorem _root_.solution (g φ : ℕ → R) (e x : R) (k : ℕ) (h0 : g 0 = e * x) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → e ^ m * g (m + 1) * x ^ m =
      g 1 ^ (m + 1) * ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := ratio g φ k hne hrec (m + 1) hm
    rw [tri_succ]
    calc e ^ (m + 1) * g (m + 1 + 1) * x ^ (m + 1)
        = e ^ m * x ^ m * (g (m + 1 + 1) * (e * x)) := by ring
      _ = (e ^ m * g (m + 1) * x ^ m) * ((∏ j ∈ Finset.range (m + 1), φ (j + 1)) * g 1) := by
          rw [← h0, h2]; ring
      _ = _ := by rw [h1]; ring
end Formalism.L2.Th1.E.Power
