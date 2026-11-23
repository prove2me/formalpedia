-- Prove2me | solution 1 for Formalism.DivisionValues.RowsOrigin.origin_interlace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:12.684095+00:00
-- url     : https://prove2.me/submissions/6a8a035e-8d6d-4047-87c9-f0f738e16269

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RowsOrigin
namespace Formalism.DivisionValues.RowsOrigin
theorem _root_.solution {n wr T : ℕ} {u : Fin (n + 2) → ℝ} {v : Fin (n + 1) → ℝ}
    {νr : Fin (n + 2) → ℕ} {ar : Fin (n + 1) → ℕ}
    (eν : ∀ i, (νr i : ℝ) = (wr : ℝ) + (u i - (((n : ℝ) + 2) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2))
    (ea : ∀ i, (ar i : ℝ) = (wr : ℝ) + (v i - (((n : ℝ) + 2) - 2 * (((i : ℕ) : ℝ) + 1)) / 2) + (T : ℝ))
    (hint : ∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) :
    (∀ i, ar i ≤ νr i.castSucc + T) ∧ (∀ i, νr i.succ + T ≤ ar i) := by
  constructor
  · intro i
    by_contra hc
    have h1 : νr i.castSucc + T + 1 ≤ ar i := by omega
    have h2 : (νr i.castSucc : ℝ) + (T : ℝ) + 1 ≤ (ar i : ℝ) := by exact_mod_cast h1
    have h3 := eν i.castSucc
    rw [Fin.val_castSucc] at h3
    have := ea i; have := (hint i).1
    linarith
  · intro i
    by_contra hc
    have h1 : ar i + 1 ≤ νr i.succ + T := by omega
    have h2 : (ar i : ℝ) + 1 ≤ (νr i.succ : ℝ) + (T : ℝ) := by exact_mod_cast h1
    have h3 := eν i.succ
    rw [Fin.val_succ] at h3
    push_cast at h3
    have := ea i; have := (hint i).2
    linarith
end Formalism.DivisionValues.RowsOrigin
