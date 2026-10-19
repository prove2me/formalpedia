-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:22:36.180696+00:00
-- url     : https://prove2.me/submissions/ee567913-a2f9-407c-a7be-62d93e46baf1

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ
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
    ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by
  have e : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = (affData hκ hc).fst.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 2)
        + (affData hκ hc).snd.hFun ((basisState κ c n : L2I ℕ) : ℕ → ℂ) (n + 2) := rfl
  rw [e]
  have hX : ∀ m, ((basisState κ c n : L2I ℕ) : ℕ → ℂ) m = if m = n then 1 else 0 := by
    intro m
    show (lp.single 2 n (1 : ℂ) : L2I ℕ) m = _
    rw [lp.single_apply, Pi.single_apply]
  have h1 : (affData hκ hc).fst.hop (fun α => (((affData hκ hc).fst.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 2)
      = (((affData hκ hc).fst.amp n : ℝ) : ℂ) * ((basisState κ c n : L2I ℕ) : ℕ → ℂ) n :=
    (affData hκ hc).fst.hop_shift _ n
  have h2 : (affData hκ hc).snd.hop (fun α => (((affData hκ hc).snd.amp α : ℝ) : ℂ) *
      ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 2) = 0 := by
    have := (affData hκ hc).snd.hop_shift (fun α => (((affData hκ hc).snd.amp α : ℝ) : ℂ) *
        ((basisState κ c n : L2I ℕ) : ℕ → ℂ) α) (n + 1)
    refine this.trans ?_
    rw [hX]; simp
  simp only [ShiftData.hFun] at *
  rw [h1, h2]
  rw [show (affData hκ hc).shift₁ (n + 2) = n + 4 from rfl,
    show (affData hκ hc).shift₂ (n + 2) = n + 3 from rfl,
    show (affData hκ hc).amp₁ n = amp κ n from rfl, hX, hX, hX]
  simp

