-- Prove2me | solution 1 for BookProof.NavierStokesFlow.finiteModes_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:05.740987+00:00
-- url     : https://prove2.me/submissions/e0282743-4418-4460-9676-b706594aed31

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.finiteModes_ne_top
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_mem_finiteModes
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution : finiteModes ≠ (⊤ : Submodule ℂ L2Z) := by

  have hsummable : Summable fun k : ℤ => ‖(1 / (k : ℂ))‖ ^ 2 := by
    have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    refine h.congr fun k => ?_
    rw [norm_div, norm_one, Complex.norm_intCast, div_pow, one_pow, sq_abs]
  set g : L2Z := ⟨fun k : ℤ => 1 / (k : ℂ), memℓp_two_of_summable hsummable⟩ with hgdef
  intro htop
  have hg : g ∈ finiteModes := htop ▸ Submodule.mem_top
  rw [mem_finiteModes] at hg
  have hsub : (Set.univ \ {(0 : ℤ)}) ⊆ Function.support ((g : ℤ → ℂ)) := by
    intro k hk
    have hk0 : k ≠ 0 := by simpa using hk.2
    have hkC : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    simpa [hgdef, Function.mem_support] using one_div_ne_zero hkC
  exact (Set.infinite_univ.diff (Set.finite_singleton (0 : ℤ))) (hg.subset hsub)
