-- Prove2me | solution 1 for C6BipartiteDomination.mem_privateCompensation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:38.626661+00:00
-- url     : https://prove2.me/submissions/2ffb293c-1f6e-4454-93dd-a45db8739ad9

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (u q : V) :
    u ∈ D → (q ∈ privateCompensation G D u ↔
      q ∉ D ∧ neighborhoodIn G D q = {u}) := by
  classical
  intro huD
  rw [privateCompensation, mem_privateExternalNeighbors]
  constructor
  · rintro ⟨hqD, hpriv⟩
    refine ⟨hqD, Finset.ext fun d => ?_⟩
    constructor
    · intro hdN
      have hdD := (mem_neighborhoodIn G D q d).mp hdN |>.1
      have hdq := (mem_neighborhoodIn G D q d).mp hdN |>.2
      exact Finset.mem_singleton.mpr ((hpriv d hdD).mp hdq.symm)
    · intro hdu
      have hdu' := Finset.mem_singleton.mp hdu
      subst d
      have huq : G.Adj u q := (hpriv u huD).mpr rfl
      exact (mem_neighborhoodIn G D q u).mpr ⟨huD, huq.symm⟩
  · rintro ⟨hqD, hN⟩
    refine ⟨hqD, ?_⟩
    intro d hdD
    constructor
    · intro hqd
      have hdN : d ∈ neighborhoodIn G D q :=
        (mem_neighborhoodIn G D q d).mpr ⟨hdD, hqd.symm⟩
      have : d ∈ ({u} : Finset V) := by simpa [hN] using hdN
      exact Finset.mem_singleton.mp this
    · intro hdu
      subst d
      have huN : u ∈ neighborhoodIn G D q := by simpa [hN]
      exact ((mem_neighborhoodIn G D q u).mp huN).2.symm
end C6BipartiteDomination
