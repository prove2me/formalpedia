-- Prove2me | solution 1 for Bl.FirstBlockLemmaK.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:06.818804+00:00
-- url     : https://prove2.me/submissions/4528717a-22a6-4ab1-aaff-ee453970a591

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaK_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaK
namespace Bl.FirstBlockLemmaK
theorem _root_.solution :
  ∀ {R : Type} [inst : CommRing.{0} R] {A : Type} [inst_1 : CommRing.{0} A] [inst_2 : Algebra.{0, 0} R A]
  (aug : AlgHom.{0, 0, 0} R A R),
  IsNilpotent.{0} (RingHom.ker.{0, 0, 0} aug) → ∀ (a : A), IsUnit.{0} (DFunLike.coe.{1, 1, 1} aug a) → IsUnit.{0} a := by
  intro R _ A _ _ aug hI a ha
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, hn⟩ := hI
  set c : A := a * algebraMap R A (↑u⁻¹ : R) with hc
  have hker : c - 1 ∈ RingHom.ker aug := by
    rw [RingHom.mem_ker]
    simp only [hc, map_sub, map_mul, AlgHom.commutes, map_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hu]
    simp
  have hnil : IsNilpotent (c - 1) := by
    refine ⟨n, ?_⟩
    have h1 : (c - 1) ^ n ∈ (RingHom.ker aug) ^ n := Ideal.pow_mem_pow hker n
    rw [hn] at h1
    simpa using h1
  have hcu : IsUnit c := by
    have := hnil.isUnit_one_add
    simpa using this
  exact isUnit_of_mul_isUnit_left hcu
end Bl.FirstBlockLemmaK
