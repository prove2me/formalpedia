-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:32:13.473349+00:00
-- url     : https://prove2.me/submissions/24f3629b-c34b-42da-87a3-4af7872acae8

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLagData_hFull_apply
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
theorem h43_lag_apply (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) (x : (latticeLagData v w fr hnu).D) :
    ((latticeLagData v w fr hnu).hFull x : L2Z) = latticeLagCLM v w fr nu (x : L2Z) := by
  have hP : ∀ i (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).P i y : L2Z) = momentum (y : L2Z) := fun _ _ => rfl
  have hQ : ∀ i (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).Q i y : L2Z) = momentum (y : L2Z) := fun _ _ => rfl
  have hD : ∀ i (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).drive i y : L2Z) = velocityOp (v i) (y : L2Z) := fun _ _ => rfl
  have hC : ∀ (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).constraintOp y : L2Z) = velocityOp w (y : L2Z) := fun _ => rfl
  have hnu' : (latticeLagData v w fr hnu).nu = nu := rfl
  have hf : (latticeLagData v w fr hnu).force = fr := rfl
  simp only [LagrangianFullData.hFull, LagrangianFullData.kinetic, LagrangianFullData.viscous,
    LagrangianFullData.drift, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, hP, hQ, hD, hC, hnu', hf]
  simp only [latticeLagCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply]

theorem solution (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) (x : (latticeLagData v w fr hnu).D) :
    ((latticeLagData v w fr hnu).hFull x : L2Z) = latticeLagCLM v w fr nu (x : L2Z) := by
  exact h43_lag_apply v w fr hnu x

