-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpDiag_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:28:06.616854+00:00
-- url     : https://prove2.me/submissions/ea1944f0-48cb-4b27-b038-8a5162533e5d

import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_inner_self
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]


theorem solution {ι : Type*} (c : ι → ℝ) (v : lpFiniteModes ι) :
    (inner ℂ ((v : lp (fun _ : ι => ℂ) 2))
        (((lpDiag c v : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2)) : ℂ)
      = ((∑ i ∈ v.2.toFinset, c i * ‖((v : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i‖ ^ 2 : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := v.2.toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    show (inner ℂ (((v : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i)
      (diagCoeff c ((v : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) : ℂ) = _
    simp only [diagCoeff, RCLike.inner_apply]
    rw [mul_assoc, Complex.mul_conj']
  · intro i hi
    have : ((v : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i = 0 := by
      by_contra h
      exact hi ((Set.Finite.mem_toFinset _).mpr h)
    show (inner ℂ (((v : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i)
      (diagCoeff c ((v : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) : ℂ) = 0
    simp [this, diagCoeff]

