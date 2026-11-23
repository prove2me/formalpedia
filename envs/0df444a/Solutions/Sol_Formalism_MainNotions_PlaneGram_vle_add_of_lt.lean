-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vle_add_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:30.084675+00:00
-- url     : https://prove2.me/submissions/3e84d8f5-a1a7-4998-900a-090560226e5a

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
theorem _root_.solution {a b : ℝ} {x y : K} (hx : vle v a x) (hy : vge v b y) (hab : a < b) :
    vle v a (x + y) := by
  unfold vle vge at *
  have hlt : vR v x < vR v y :=
    lt_of_le_of_lt hx (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hab) hy)
  have hlt' : v x < v y :=
    not_le.mp fun h => absurd ((vR_le_vR_iff v).mpr h) (not_le.mpr hlt)
  have e : vR v (x + y) = vR v x := by
    unfold vR
    rw [AddValuation.map_add_eq_of_lt_left v hlt']
  rw [e]
  exact hx
end Formalism.MainNotions.PlaneGram
