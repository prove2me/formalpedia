-- Prove2me | solution 1 for Formalism.L2.NCov.add_pow_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:34.099495+00:00
-- url     : https://prove2.me/submissions/f7bf7363-91f1-4f1e-a8e6-5f2bef790995

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.NCov
theorem _root_.solution {P Q : End K V} (h : Commute P Q) {x : V} {k l : ℕ}
    (hP : (P ^ k) x = 0) (hQ : (Q ^ l) x = 0) : ((P + Q) ^ (k + l)) x = 0 := by
  rw [h.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, Module.End.mul_apply]
  suffices h0 : (P ^ m) ((Q ^ (k + l - m)) x) = 0 by rw [h0, smul_zero]
  rcases le_or_gt k m with hkm | hkm
  · obtain ⟨d, rfl⟩ : ∃ d, m = d + k := ⟨m - k, by omega⟩
    rw [← Module.End.mul_apply, (h.pow_pow (d + k) (k + l - (d + k))).eq, Module.End.mul_apply,
      pow_add, Module.End.mul_apply, hP, map_zero, map_zero]
  · obtain ⟨d, hd⟩ : ∃ d, k + l - m = d + l := ⟨k + l - m - l, by omega⟩
    rw [hd, pow_add, Module.End.mul_apply, hQ, map_zero, map_zero]
end Formalism.L2.NCov
