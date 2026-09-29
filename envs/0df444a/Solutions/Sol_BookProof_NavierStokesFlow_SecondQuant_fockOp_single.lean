-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SecondQuant.fockOp_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:10:09.781369+00:00
-- url     : https://prove2.me/submissions/d4f70bc9-f1a6-411e-aee2-f12aa7eec2a5

-- Generated from ChapterNavierStokesSecondQuant.lean — solution of BookProof.NavierStokesFlow.SecondQuant.fockOp_single
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
import Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_single_mem_fockCore
import Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_apply
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant










open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq ι] (A : ∀ m, D m →ₗ[ℂ] D m) (m : ι) (x : D m) :
    (fockOp A ⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩ : lp S 2)
      = lp.single 2 m ((A m x : D m) : S m) := by

  set f : fockCore D := ⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩ with hf
  apply lp.ext
  funext j
  rw [fockOp_apply A f j]
  rcases eq_or_ne j m with rfl | hne
  · have hx : (⟨(f : lp S 2) j, (f.2).2 j⟩ : D j) = x := by
      ext
      change ((lp.single 2 j (x : S j) : lp S 2) : ∀ j, S j) j = (x : S j)
      exact lp.single_apply_self 2 j (x : S j)
    rw [hx, lp.single_apply_self]
  · have hz : (⟨(f : lp S 2) j, (f.2).2 j⟩ : D j) = 0 := by
      ext
      change ((lp.single 2 m (x : S m) : lp S 2) : ∀ j, S j) j = 0
      exact lp.single_apply_ne 2 m (x : S m) hne
    rw [hz, lp.single_apply_ne 2 m _ hne]
    simp
