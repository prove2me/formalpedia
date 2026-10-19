-- Prove2me | solution 1 for CompactnessConjecture.gluedJHom_injOn_marked_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/c242126d-09bd-490f-8458-28a9e0f4a233

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_gluedJVertex_jThetaVertex
import Theorems.Thm_CompactnessConjecture_inJCopy_iff_exists_jThetaVertex

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    (copy : Fin 2) :
    Set.InjOn
      (gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond)
      {vertex | InJCopy copy vertex} := by
  intro left hleft right hright heq
  change InJCopy copy left at hleft
  change InJCopy copy right at hright
  obtain ⟨source, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy left).mp hleft
  obtain ⟨target, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy right).mp hright
  change
    gluedJVertex copies joining (jThetaVertex copy source) =
      gluedJVertex copies joining (jThetaVertex copy target) at heq
  rw [gluedJVertex_jThetaVertex copies joining hfirst hsecond copy,
    gluedJVertex_jThetaVertex copies joining hfirst hsecond copy] at heq
  have hequal := (copies copy).injective heq
  subst target
  rfl
end CompactnessConjecture
