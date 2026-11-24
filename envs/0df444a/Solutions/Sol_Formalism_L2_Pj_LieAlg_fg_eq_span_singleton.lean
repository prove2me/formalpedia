-- Prove2me | solution 1 for Formalism.L2.Pj.LieAlg.fg_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:01.193427+00:00
-- url     : https://prove2.me/submissions/6f9e29ec-80c8-45b4-9d21-7addaf26641f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Theorems.Thm_Formalism_L2_Pj_LieAlg_exists_divisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace Formalism.L2.Pj.LieAlg
theorem _root_.solution (S : Submodule V K) (hS : S.FG) : ∃ t : K, S = span V {t} := by
  classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, -, hts, hdiv⟩ := exists_divisor (V := V) s
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [span_le]
    intro x hx
    obtain ⟨r, hr⟩ := hdiv x hx
    rw [SetLike.mem_coe, mem_span_singleton]
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  · rw [span_le, Set.singleton_subset_iff]
    rcases hts with h | h
    · rw [h]; exact zero_mem _
    · exact subset_span h
end Formalism.L2.Pj.LieAlg
