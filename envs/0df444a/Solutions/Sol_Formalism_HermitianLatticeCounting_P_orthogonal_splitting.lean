-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.orthogonal_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:04.984541+00:00
-- url     : https://prove2.me/submissions/f93a595c-b642-45fe-a226-c4dffc949882

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_mem_perpR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PerpSplit := by
  intro K V _ _ _ σ B U A hAU hc
  constructor
  · apply le_antisymm
    · intro x hx
      have : x ∈ U ⊔ perpR B U := by rw [hc.sup_eq_top]; trivial
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp this
      refine Submodule.mem_sup.mpr ⟨w, hw, u, ⟨hu, ?_⟩, by abel⟩
      rw [SetLike.mem_coe, s5a4_mem_perpR]
      rw [s5a4_mem_perpR] at hx hw
      intro a ha
      have h1 := hx a ha
      rw [map_add, hw a (hAU ha), add_zero] at h1
      exact h1
    · apply sup_le
      · intro x hx; rw [s5a4_mem_perpR] at hx ⊢; exact fun a ha => hx a (hAU ha)
      · exact inf_le_right
  · exact (hc.disjoint.symm).mono_right inf_le_left
end Formalism.HermitianLatticeCounting.P
