-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.pairAbs_le_ampSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:10.030837+00:00
-- url     : https://prove2.me/submissions/568838df-1c2a-4fb8-a4e7-d4718e0f1c77

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution (hG : 0 ≤ X.Gam1) (Q : Set (τ × τ))
    (hs : Summable (Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖))) :
    X.pairAbs Q ≤ X.Gam1 * ampSum X Q := by
  unfold PB.Terms.pairAbs ampSum
  refine mul_le_mul_of_nonneg_left ?_ hG
  have hle : ∀ p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p ≤
      Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p := by
    intro p
    by_cases hp : p ∈ Q
    · simp only [Set.indicator_of_mem hp]
      exact norm_inner_le_norm _ _
    · simp [Set.indicator_apply, hp]
  have hnn : ∀ p, 0 ≤ Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p :=
    fun p => Set.indicator_nonneg (fun _ _ => norm_nonneg _) p
  exact Summable.tsum_le_tsum hle (hs.of_nonneg_of_le hnn hle) hs
end Formalism.L2.SG.RowsOther
