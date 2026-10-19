-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:21:49.923482+00:00
-- url     : https://prove2.me/submissions/9c304a33-4d9e-4d5c-9833-154624e04d89

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)


theorem solution {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) :
    ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear c n : ℝ) : ℂ) := by
  have e : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = (affData hκ hc).fst.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 1)
        + (affData hκ hc).snd.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 1) := rfl
  rw [e]
  have hX : ∀ m, ((basisState κ c n : L2I ℕ) : ℕ → ℂ) m = if m = n then 1 else 0 := by
    intro m
    show (lp.single 2 n (1 : ℂ) : L2I ℕ) m = _
    rw [lp.single_apply, Pi.single_apply]
  have h2 : (affData hκ hc).snd.hop (fun α => (((affData hκ hc).snd.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 1)
      = (((affData hκ hc).snd.amp n : ℝ) : ℂ) * ((basisState κ c n : L2I ℕ) : ℕ → ℂ) n :=
    (affData hκ hc).snd.hop_shift _ n
  have h1 : (affData hκ hc).fst.hop (fun α => (((affData hκ hc).fst.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 1) = 0 := by
    rcases n with _ | m
    · apply ShiftData.hop_eq_zero
      rintro ⟨α, hα⟩
      have : α + 2 = 1 := hα
      omega
    · have := (affData hκ hc).fst.hop_shift (fun α => (((affData hκ hc).fst.amp α : ℝ) : ℂ) *
        ((basisState κ c (m+1) : L2I ℕ) : ℕ → ℂ) α) m
      refine this.trans ?_
      rw [hX]; simp
  simp only [ShiftData.hFun] at *
  rw [h1, h2]
  have s1 : (affData hκ hc).shift₁ (n + 1) = n + 3 := rfl
  have s2 : (affData hκ hc).shift₂ (n + 1) = n + 2 := rfl
  have a2 : (affData hκ hc).amp₂ n = shear c n := rfl
  rw [s1, s2, a2, hX, hX, hX]
  simp

