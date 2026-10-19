-- Prove2me | solution 2 for BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:00:59.994835+00:00
-- url     : https://prove2.me/submissions/17e3d445-5963-43a6-8ab8-6fa1273f985c

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_velocityOp_isSelfAdjoint
import Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_momentum_isSelfAdjoint
-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)
theorem h43_sa_mul_comm {A : Type*} [Semiring A] [StarRing A] {a b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hc : Commute a b) : IsSelfAdjoint (a * b) := by
  rw [isSelfAdjoint_iff, star_mul, hb.star_eq, ha.star_eq, hc.eq]

theorem h43_sa_anti {A : Type*} [Semiring A] [StarRing A] {a b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) : IsSelfAdjoint (a * b + b * a) := by
  rw [isSelfAdjoint_iff, star_add, star_mul, star_mul, hb.star_eq, ha.star_eq, add_comm]

open BookProof.ChapterContinuityUnitaryInfinite BookProof.NavierStokesFlow.FullEsa in
theorem h43_latAdv_sa (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) :
    IsSelfAdjoint (latticeAdvectionCLM v nu i) := by
  unfold latticeAdvectionCLM
  refine IsSelfAdjoint.sub (isSelfAdjoint_sum _ fun j _ => h43_sa_mul_comm
    (velocityOp_isSelfAdjoint _) (velocityOp_isSelfAdjoint _) (velocityOp_commute _ _)) ?_
  rw [isSelfAdjoint_iff, star_smul, (velocityOp_isSelfAdjoint _).star_eq, Complex.star_def,
    Complex.conj_ofReal]

open BookProof.ChapterContinuityUnitaryInfinite BookProof.NavierStokesFlow.FullEsa in
theorem h43_latHam_sa (v : Fin 15 → LinfZ) (nu : ℝ) :
    IsSelfAdjoint (latticeFullHamiltonianCLM v nu) := by
  unfold latticeFullHamiltonianCLM
  exact isSelfAdjoint_sum _ fun i _ => h43_sa_anti momentum_isSelfAdjoint (h43_latAdv_sa v nu i)

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ) :
    ((latticeFullHamiltonianCLM v nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric := by
  exact (h43_latHam_sa v nu).isSymmetric

