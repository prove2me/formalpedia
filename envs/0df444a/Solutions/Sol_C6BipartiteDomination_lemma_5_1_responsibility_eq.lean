-- Prove2me | solution 1 for C6BipartiteDomination.lemma_5_1_responsibility_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:03.33314+00:00
-- url     : https://prove2.me/submissions/214381cd-e47f-4cd7-aa94-7f2a40fad13b

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_isolatedSubset_region_subset
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V}
    (hD : IsBipartiteDominatingSet G D)
    (hX : X ⊆ Z0Part G D) :
    responsibilityRegion G D X = X := by
  classical
  have hXZ : X ⊆ ZPart G D := by
    intro x hx
    exact (mem_Z0Part G D x).mp (hX hx) |>.1
  have hXisolated : IsolatedSubset G D X := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (mem_ZPart G D x).mp (hXZ hx) |>.1
    · intro x u hx hu hAdj
      have hxZ := (mem_ZPart G D x).mp (hXZ hx)
      exact hxZ.2 u hu hAdj
  apply Finset.Subset.antisymm
  · intro v hvR
    rw [mem_responsibilityRegion] at hvR
    by_cases hvX : v ∈ X
    · exact hvX
    · have hvD : v ∉ D := by
        intro hvD
        have hvRet : v ∈ D \ X := Finset.mem_sdiff.mpr ⟨hvD, hvX⟩
        exact hvR.1 hvRet
      obtain ⟨d, hd, hAdj⟩ := hD.1 hvD
      have hdNotRet : d ∉ D \ X := by
        intro hdRet
        exact hvR.2 d hdRet hAdj
      have hdX : d ∈ X := by
        by_contra hnot
        exact hdNotRet (Finset.mem_sdiff.mpr ⟨hd, hnot⟩)
      have hdZ0 : d ∈ Z0Part G D := hX hdX
      have hvW0 : v ∈ W0Part G D := by
        rw [mem_W0Part]
        refine ⟨hvD, ?_⟩
        intro b hb hAdjB
        have hbD : b ∈ D := (mem_BPart G D b).mp hb |>.1
        have hbNotX : b ∉ X := by
          intro hbX
          have hbZ : b ∈ ZPart G D := hXZ hbX
          exact (mem_BPart G D b).mp hb |>.2 hbZ
        have hbRet : b ∈ D \ X := Finset.mem_sdiff.mpr ⟨hbD, hbNotX⟩
        exact hvR.2 b hbRet hAdjB
      have hdZ0info := (mem_Z0Part G D d).mp hdZ0
      exact (hdZ0info.2 v hvW0 hAdj).elim
  · exact isolatedSubset_region_subset G hXisolated
end C6BipartiteDomination
