-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_dom_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:11.153857+00:00
-- url     : https://prove2.me/submissions/a8baacb1-58c6-4f53-be34-51fc746efa05

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hs : HStrip lam kap b) : Dominant kap := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hy : y.1 - 1 < n := by have := y.2; omega
    have h1 : (⟨y.1 - 1, hy⟩ : Fin n).1 + 1 < n := by
      have := y.2; have := Fin.lt_def.1 hlt; simp only; omega
    have h2 := hs.2.1 ⟨y.1 - 1, hy⟩ h1
    have h3 : (⟨(⟨y.1 - 1, hy⟩ : Fin n).1 + 1, h1⟩ : Fin n) = y := by
      apply Fin.ext; have := Fin.lt_def.1 hlt; simp only; omega
    rw [h3] at h2
    have h4 : lam ⟨y.1 - 1, hy⟩ ≤ lam x := hl (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact h2.trans (h4.trans (hs.1 x))
end Formalism.InvariantFactorPaths.ColumnFamilies
