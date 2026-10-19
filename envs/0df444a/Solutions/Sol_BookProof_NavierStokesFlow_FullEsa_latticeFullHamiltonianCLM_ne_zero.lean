-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:33:50.892798+00:00
-- url     : https://prove2.me/submissions/041d3d7a-fc9b-41be-b5ae-9a5362847643

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_ne_zero
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)
theorem h43_mom_apply (f : L2Z) (k : ℤ) :
    ((BookProof.ChapterContinuityUnitaryInfinite.momentum f : L2Z) : ℤ → ℂ) k = (-Complex.I / 2) * ((f : ℤ → ℂ) (k + 1) - (f : ℤ → ℂ) (k + -1)) := rfl

theorem h43_smul_apply (c : ℂ) (f : L2Z) (k : ℤ) : ((c • f : L2Z) : ℤ → ℂ) k = c * (f : ℤ → ℂ) k := rfl

theorem h43_single_apply (j k : ℤ) : ((lp.single 2 j (1 : ℂ) : L2Z) : ℤ → ℂ) k = if k = j then 1 else 0 := by
  rw [lp.single_apply, Pi.single_apply]

theorem h43_full_ne_zero :
    latticeFullHamiltonianCLM (fun _ => constField 1) 1 ≠ 0 := by
  intro h
  have hv : BookProof.ChapterContinuityUnitaryInfinite.velocityOp (constField 1) = 1 := by
    ext f k; simp [constField]
  have hH : latticeFullHamiltonianCLM (fun _ => constField 1) 1 = (12 : ℂ) • BookProof.ChapterContinuityUnitaryInfinite.momentum := by
    simp only [latticeFullHamiltonianCLM, latticeAdvectionCLM, hv, mul_one, one_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Complex.ofReal_one, one_smul, mul_sub, sub_mul,
      mul_smul_comm, smul_mul_assoc, smul_add]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_smul, ← sub_smul, ← add_smul]
    congr 1; norm_num
  rw [hH] at h
  have e := congrArg (fun T : L2Z →L[ℂ] L2Z => ((T (lp.single 2 0 1) : L2Z) : ℤ → ℂ) (-1)) h
  simp only [ContinuousLinearMap.smul_apply, h43_smul_apply, h43_mom_apply, h43_single_apply,
    ContinuousLinearMap.zero_apply] at e
  norm_num at e

theorem solution :
    latticeFullHamiltonianCLM (fun _ => constField 1) 1 ≠ 0 := by
  exact h43_full_ne_zero

