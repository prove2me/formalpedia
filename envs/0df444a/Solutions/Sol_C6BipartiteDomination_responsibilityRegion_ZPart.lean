-- Prove2me | solution 1 for C6BipartiteDomination.responsibilityRegion_ZPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:02.250276+00:00
-- url     : https://prove2.me/submissions/411b455b-470b-41c8-8849-56d6762355cc

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_isolatedSubset_region_subset
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    (D : Finset V) :
    responsibilityRegion G D (ZPart G D) = ZPart G D ∪ W0Part G D := by
  classical
  apply Finset.ext
  intro v
  constructor
  · intro hvR
    by_cases hvZ : v ∈ ZPart G D
    · exact Finset.mem_union_left _ hvZ
    · have hvPred := (mem_responsibilityRegion G D (ZPart G D) v).mp hvR
      have hvD : v ∉ D := by
        intro hvD
        have hvRet : v ∈ D \ ZPart G D := Finset.mem_sdiff.mpr ⟨hvD, hvZ⟩
        exact hvPred.1 hvRet
      apply Finset.mem_union_right
      rw [mem_W0Part]
      refine ⟨hvD, ?_⟩
      intro b hb hAdj
      have hbD : b ∈ D := (mem_BPart G D b).mp hb |>.1
      have hbZ : b ∉ ZPart G D := (mem_BPart G D b).mp hb |>.2
      have hbRet : b ∈ D \ ZPart G D := Finset.mem_sdiff.mpr ⟨hbD, hbZ⟩
      exact hvPred.2 b hbRet hAdj
  · intro hv
    rcases Finset.mem_union.mp hv with hvZ | hvW
    · have hIso : IsolatedSubset G D (ZPart G D) := by
        refine ⟨?_, ?_⟩
        · intro z hz
          exact (mem_ZPart G D z).mp hz |>.1
        · intro z u hz hu hAdj
          exact (mem_ZPart G D z).mp hz |>.2 u hu hAdj
      exact isolatedSubset_region_subset G hIso hvZ
    · have hvW' := (mem_W0Part G D v).mp hvW
      rw [mem_responsibilityRegion]
      refine ⟨?_, ?_⟩
      · intro hvRet
        exact hvW'.1 (Finset.mem_sdiff.mp hvRet).1
      · intro b hb hAdj
        have hbB : b ∈ BPart G D :=
          (mem_BPart G D b).mpr ⟨(Finset.mem_sdiff.mp hb).1,
            (Finset.mem_sdiff.mp hb).2⟩
        exact hvW'.2 b hbB hAdj
end C6BipartiteDomination
