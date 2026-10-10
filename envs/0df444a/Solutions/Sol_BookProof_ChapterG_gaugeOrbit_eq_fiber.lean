-- Prove2me | solution 1 for BookProof.ChapterG.gaugeOrbit_eq_fiber
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:21:39.06298+00:00
-- url     : https://prove2.me/submissions/64c07b27-04d1-40c4-9b75-63182cd205fc

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.gaugeOrbit_eq_fiber
import Mathlib
import Definitions.Def_ChapterG
import Theorems.Thm_BookProof_ChapterG_swap_mem_gaugeGroup
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} (π : X → Y) (x : X) :
    MulAction.orbit (gaugeGroup π) x = π ⁻¹' {π x} := by

  classical
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact g.2 x
  · intro hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    refine ⟨⟨Equiv.swap x z, swap_mem_gaugeGroup hz.symm⟩, ?_⟩
    change (Equiv.swap x z) x = z
    rw [Equiv.swap_apply_left]
