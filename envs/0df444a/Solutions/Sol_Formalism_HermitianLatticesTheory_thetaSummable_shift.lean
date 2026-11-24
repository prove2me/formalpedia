-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:18.214896+00:00
-- url     : https://prove2.me/submissions/487ec205-6680-41cf-b137-0892e5c087fd

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_trpara
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (γ x : V) :
    Algebra.trace ℚ K (h x x) ≤
      2 * Algebra.trace ℚ K (h (γ + x) (γ + x)) + 2 * Algebra.trace ℚ K (h γ γ) := by
  have e := thetaSummable_trpara h (γ + x) (-γ)
  have n0 := thetaSummable_nonneg h hpos (γ + x - -γ)
  have e1 : γ + x + -γ = x := by abel
  have e2 : h (-γ) (-γ) = h γ γ := by simp
  rw [e1, e2] at e
  linarith
end Formalism.HermitianLatticesTheory
