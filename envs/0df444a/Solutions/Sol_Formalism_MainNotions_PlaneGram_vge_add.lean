-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:56.087885+00:00
-- url     : https://prove2.me/submissions/022265b2-6ef1-4ad4-88d5-dc4cf36d3fb9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
private lemma map_ratCast_le_map_ratCast_iff {u w : WithTop ℚ} :
    u.map (fun n : ℚ => (n : ℝ)) ≤ w.map (fun n : ℚ => (n : ℝ)) ↔ u ≤ w := by
  cases u <;> cases w <;> simp
private lemma vR_le_vR_iff {x y : K} : vR v x ≤ vR v y ↔ v x ≤ v y := map_ratCast_le_map_ratCast_iff
section DVR
variable {v} {p : ℕ} [CharZero K]
end DVR
section DVR2
variable {v} {p : ℕ} [CharZero K]
end DVR2
section Star
variable {v} {p : ℕ} [CharZero K]
end Star
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x + y) := by
  unfold vge at *
  have hm := v.map_add x y
  rcases le_total (v x) (v y) with h | h
  · rw [min_eq_left h] at hm
    exact hx.trans ((vR_le_vR_iff v).mpr hm)
  · rw [min_eq_right h] at hm
    exact hy.trans ((vR_le_vR_iff v).mpr hm)
end Formalism.MainNotions.PlaneGram
