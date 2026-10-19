-- Prove2me | solution 1 for CompactnessConjecture.thetaBaseExtensions_commonNeighborIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/1f2c07b5-3a74-47cd-86a1-5441ed208d79

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_no_jTemplate
import Theorems.Thm_CompactnessConjecture_gluedJHom_injOn_marked_copy
import Theorems.Thm_CompactnessConjecture_gluedJBase_injective
import Theorems.Thm_CompactnessConjecture_gluedJHom_color_respecting

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (y z : Fin n) :
    CommonNeighborIndependent host (thetaBaseExtensions host y z) := by
  intro x x' hx hx' hdistinct
  rintro ⟨_, joining, hxjoin, hx'join⟩
  obtain ⟨first, hfirstX, hfirstY, hfirstZ⟩ :=
    (mem_thetaBaseExtensions host x y z).mp hx
  obtain ⟨second, hsecondX, hsecondY, hsecondZ⟩ :=
    (mem_thetaBaseExtensions host x' y z).mp hx'
  let copies : Fin 2 → SimpleGraph.Copy thetaGraph host :=
    ![first, second]
  have hsharedFirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    change second (.inl (.inl (1 : Fin 3))) =
      first (.inl (.inl (1 : Fin 3)))
    exact hsecondY.trans hfirstY.symm
  have hsharedSecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    change second (.inl (.inl (2 : Fin 3))) =
      first (.inl (.inl (2 : Fin 3)))
    exact hsecondZ.trans hfirstZ.symm
  have hjoinFirst :
      host.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (first (.inl (.inl (0 : Fin 3)))) joining
    rw [hfirstX]
    exact hxjoin
  have hjoinSecond :
      host.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (second (.inl (.inl (0 : Fin 3)))) joining
    rw [hsecondX]
    exact hx'join
  have hbaseDistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3))) := by
    change first (.inl (.inl (0 : Fin 3))) ≠
      second (.inl (.inl (0 : Fin 3)))
    rw [hfirstX, hsecondX]
    exact hdistinct
  apply proposedFamilyFree_no_jTemplate hfree
    (gluedJHom copies joining hsharedFirst hsharedSecond
      hjoinFirst hjoinSecond)
  · exact gluedJHom_color_respecting hbip copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond
  · change Function.Injective (gluedJBase copies)
    exact gluedJBase_injective copies hsharedFirst
      hsharedSecond hbaseDistinct
  · intro copy
    exact gluedJHom_injOn_marked_copy copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond copy
end CompactnessConjecture
