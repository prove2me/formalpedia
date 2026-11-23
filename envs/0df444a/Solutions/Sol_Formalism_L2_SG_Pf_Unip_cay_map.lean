-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.cay_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:41.330806+00:00
-- url     : https://prove2.me/submissions/a891998d-df43-48b8-a242-160ebc3711da

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]
variable {lv : ι → ℕ} {k : ℕ}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {K' : Type*} [CommRing K'] [Invertible (2 : K')] (f : K →+* K') (N : ℕ) (Z : Matrix ι ι K) :
    (cay N Z).map f = cay N (Z.map f) := by
  have h2 : f (⅟2 : K) = ⅟2 := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat f 2, ← map_mul, mul_invOf_self, map_one]
  have hm : ∀ M : Matrix ι ι K, M.map f = f.mapMatrix M := fun _ => rfl
  have hs : f.mapMatrix ((⅟2 : K) • Z) = (⅟2 : K') • f.mapMatrix Z := by
    ext a b
    simp [h2]
  unfold cay geo
  rw [hm, hm, map_add, map_one, map_mul, map_sum]
  simp only [map_pow, hs]
end Formalism.L2.SG.Pf.Unip
