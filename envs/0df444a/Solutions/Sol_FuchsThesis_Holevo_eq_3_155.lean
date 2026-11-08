-- Prove2me | solution 1 for FuchsThesis.Holevo.eq_3_155
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:21:48.247104+00:00
-- url     : https://prove2.me/submissions/bb934ad4-5329-46b2-b051-078014d9319c

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Holevo_mutualInfo
import Definitions.Def_FuchsThesis_Holevo_holevoS

namespace Aux_FTH3155
open FuchsThesis.Holevo

theorem mix0 {d : Type} [Fintype d] (ρ0 ρ1 : Matrix d d ℂ) : mixState ρ0 ρ1 0 = ρ0 := by
  unfold mixState
  simp

theorem mix1 {d : Type} [Fintype d] (ρ0 ρ1 : Matrix d d ℂ) : mixState ρ0 ρ1 1 = ρ1 := by
  unfold mixState
  simp

end Aux_FTH3155

open FuchsThesis.Holevo Aux_FTH3155 in
theorem solution {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    {m : ℕ} (E : Fin m → Matrix d d ℂ) (hE : FuchsVdGraaf.IsPOVM E) :
    mutualInfo ρ0 ρ1 E 0 = 0 ∧ mutualInfo ρ0 ρ1 E 1 = 0 ∧
      holevoS ρ0 ρ1 0 = 0 ∧ holevoS ρ0 ρ1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mutualInfo; rw [mix0]; ring
  · unfold mutualInfo; rw [mix1]; ring
  · unfold holevoS; rw [mix0]; ring
  · unfold holevoS; rw [mix1]; ring
