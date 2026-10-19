-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:49.431106+00:00
-- url     : https://prove2.me/submissions/84007b23-05ed-44a8-830d-f6bf5bc3ed06

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.inner_of_block_supported
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_embFun_of_ne
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (j : J) (x : L2I (ℕ × J)) (a : L2I ℕ)
    (hx : ∀ p, (x : ℕ × J → ℂ) p = embFun j ((a : ℕ → ℂ)) p) (w : L2I (ℕ × J)) :
    (inner ℂ x w : ℂ) = inner ℂ a (blockVec w j) := by

  have hinj : Function.Injective fun n : ℕ => (n, j) := by
    intro p q hpq
    simpa using hpq
  have h1 : HasSum (fun p : ℕ × J =>
      (inner ℂ ((x : ℕ × J → ℂ) p) ((w : ℕ × J → ℂ) p) : ℂ)) (inner ℂ x w) :=
    lp.hasSum_inner x w
  have hzero : ∀ p ∉ Set.range fun n : ℕ => (n, j),
      (inner ℂ ((x : ℕ × J → ℂ) p) ((w : ℕ × J → ℂ) p) : ℂ) = 0 := by
    rintro ⟨n, j'⟩ hp
    have hj : j' ≠ j := by
      intro h
      exact hp ⟨n, by simp [h]⟩
    rw [hx (n, j'), embFun_of_ne _ _ hj]
    simp
  have h1' := (hinj.hasSum_iff hzero).2 h1
  have hfun : ((fun p : ℕ × J => (inner ℂ ((x : ℕ × J → ℂ) p) ((w : ℕ × J → ℂ) p) : ℂ))
      ∘ fun n : ℕ => (n, j))
      = fun n : ℕ => (inner ℂ ((a : ℕ → ℂ) n) (((blockVec w j : L2I ℕ) : ℕ → ℂ) n) : ℂ) := by
    funext n
    simp [hx (n, j)]
  rw [hfun] at h1'
  exact h1'.unique (lp.hasSum_inner a (blockVec w j))
