-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostSplitK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:14.751806+00:00
-- url     : https://prove2.me/submissions/3088e5a6-2450-4a10-8915-28aaf000e17a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_clause
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ram_ncard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hFrob : HostFrob) : HostSplitK := by
  intro e q d hH L _ _ ζ a b hL
  obtain ⟨hq, hd, hq8, hd16, hJq⟩ := hH
  have hb : b ^ 2 = -(d : L) := hL.2.2.1
  have hd7 : d % 8 = 7 := by omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    norm_num at hq8
  have hd2 : d ≠ 2 := by
    rintro rfl
    norm_num at hd16
  have hqd : q ≠ d := by
    rintro rfl
    omega
  refine ⟨fun p hp => SplitK.clause hd hd7 hb p hp, SplitK.ram_ncard hd hb,
    (SplitK.clause hd hd7 hb q hq).mpr (Or.inr ⟨hq2, hJq⟩), ?_⟩
  intro p hfp hp2 hpq hpd P _ _ σ hσ
  have hF := ((hFrob e q d ⟨hq, hd, hqd, hq2, hd2⟩ L ζ a b hL p hp2 hpq hpd P).2.1 σ).mp hσ
  have h2 := hF.2.1
  rw [SplitK.clause hd hd7 hb p hfp.out]
  show galE e ζ a b σ ∈ (chD e).ker ↔ _
  rw [MonoidHom.mem_ker]
  show (galE e ζ a b σ).1.2 = 1 ↔ _
  constructor
  · intro h
    refine Or.inr ⟨hp2, ?_⟩
    rw [← h2, h]
    first | rfl | simp
  · rintro (h | ⟨-, h⟩)
    · exact absurd h hp2
    · apply Units.ext
      rw [h2, h]
      first | rfl | simp
end Formalism.FrobeniusOrbits
