-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:57.917424+00:00
-- url     : https://prove2.me/submissions/539c161a-0714-41aa-aff6-0b95314ae4a2

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_bilH_apply
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) {j : J} (hj : 0 < κ j) :
    ∃ x : lpFiniteModes (ℕ × J), bilH κ x ≠ 0 := by

  classical
  refine ⟨⟨lp.single 2 ((0 : ℕ), j) (1 : ℂ), lpSingle_mem_lpFiniteModes _ _⟩, ?_⟩
  set x : lpFiniteModes (ℕ × J) :=
    ⟨lp.single 2 ((0 : ℕ), j) (1 : ℂ), lpSingle_mem_lpFiniteModes _ _⟩ with hxdef
  have hX : ∀ n : ℕ, ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j) = if n = 0 then 1 else 0 := by
    intro n
    simp [hxdef, lp.single_apply, Pi.single_apply, Prod.ext_iff]
  have hcoord : ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (2, j)
      = Complex.I * ((amp (κ j) 0 : ℝ) : ℂ) := by
    rw [blockVec_bilH_apply]
    simp [hFun, shift2, hX]
  have hamp : amp (κ j) 0 ≠ 0 := by
    have hs : 0 < Real.sqrt (((0 : ℕ) + 1) * ((0 : ℕ) + 2)) := by
      rw [Real.sqrt_pos]
      norm_num
    simp only [amp]
    positivity
  intro h0
  rw [h0] at hcoord
  simp only [lp.coeFn_zero, Pi.zero_apply] at hcoord
  have : ((amp (κ j) 0 : ℝ) : ℂ) = 0 := by
    have := hcoord.symm
    field_simp at this
    simpa using this
  exact hamp (by exact_mod_cast this)
