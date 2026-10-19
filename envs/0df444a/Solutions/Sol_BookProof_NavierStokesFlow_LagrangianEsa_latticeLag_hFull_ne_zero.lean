-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:33:11.687958+00:00
-- url     : https://prove2.me/submissions/d2829989-8f08-4f08-9b63-4348af491158

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
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
      ((latticeLagData v w fr hnu).P i y : L2Z) = BookProof.ChapterContinuityUnitaryInfinite.momentum (y : L2Z) := fun _ _ => rfl
  have hQ : ∀ i (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).Q i y : L2Z) = BookProof.ChapterContinuityUnitaryInfinite.momentum (y : L2Z) := fun _ _ => rfl
  have hD : ∀ i (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).drive i y : L2Z) = BookProof.ChapterContinuityUnitaryInfinite.velocityOp (v i) (y : L2Z) := fun _ _ => rfl
  have hC : ∀ (y : (latticeLagData v w fr hnu).D),
      ((latticeLagData v w fr hnu).constraintOp y : L2Z) = BookProof.ChapterContinuityUnitaryInfinite.velocityOp w (y : L2Z) := fun _ => rfl
  have hnu' : (latticeLagData v w fr hnu).nu = nu := rfl
  have hf : (latticeLagData v w fr hnu).force = fr := rfl
  simp only [LagrangianFullData.hFull, LagrangianFullData.kinetic, LagrangianFullData.viscous,
    LagrangianFullData.drift, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, hP, hQ, hD, hC, hnu', hf]
  simp only [latticeLagCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply]

theorem h43_mom_apply (f : L2Z) (k : ℤ) :
    ((BookProof.ChapterContinuityUnitaryInfinite.momentum f : L2Z) : ℤ → ℂ) k = (-Complex.I / 2) * ((f : ℤ → ℂ) (k + 1) - (f : ℤ → ℂ) (k + -1)) := rfl

theorem h43_smul_apply (c : ℂ) (f : L2Z) (k : ℤ) : ((c • f : L2Z) : ℤ → ℂ) k = c * (f : ℤ → ℂ) k := rfl

theorem h43_single_apply (j k : ℤ) : ((lp.single 2 j (1 : ℂ) : L2Z) : ℤ → ℂ) k = if k = j then 1 else 0 := by
  rw [lp.single_apply, Pi.single_apply]

theorem h43_lag_ne_zero :
    (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).hFull ≠ 0 := by
  intro h
  let x : (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).D :=
    ⟨lp.single 2 0 1, lpSingle_mem_lpFiniteModes 0 1⟩
  have e := congrArg (fun T => (((T x : _) : L2Z) : ℤ → ℂ) 0) h
  simp only at e
  rw [h43_lag_apply] at e
  change _ = (0 : ℂ) at e
  have hv : BookProof.ChapterContinuityUnitaryInfinite.velocityOp zeroField = 0 := by
    ext f k; simp [zeroField]
  have hL : latticeLagCLM (fun _ => zeroField) zeroField (fun _ => 0) 0 = ((3 / 2 : ℝ) : ℂ) • (BookProof.ChapterContinuityUnitaryInfinite.momentum * BookProof.ChapterContinuityUnitaryInfinite.momentum) := by
    simp only [latticeLagCLM, hv, smul_zero, Finset.sum_const_zero, add_zero, Complex.ofReal_zero, zero_smul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1; push_cast; norm_num
  rw [hL] at e
  have e2 : ((((3 / 2 : ℝ) : ℂ) • (BookProof.ChapterContinuityUnitaryInfinite.momentum * BookProof.ChapterContinuityUnitaryInfinite.momentum)) (x : L2Z) : ℤ → ℂ) 0 =
      ((3 / 2 : ℝ) : ℂ) * ((-Complex.I / 2) * ((-Complex.I / 2) * ((if (0:ℤ) + 1 + 1 = 0 then 1 else 0) - (if (0:ℤ) + 1 + -1 = 0 then 1 else 0)) - (-Complex.I / 2) * ((if (0:ℤ) + -1 + 1 = 0 then 1 else 0) - (if (0:ℤ) + -1 + -1 = 0 then 1 else 0)))) := by
    rw [ContinuousLinearMap.smul_apply, h43_smul_apply, ContinuousLinearMap.mul_apply, h43_mom_apply,
      h43_mom_apply, h43_mom_apply]
    simp only [x, h43_single_apply]
  rw [e2] at e
  norm_num at e
  exact Complex.I_ne_zero (by linear_combination e)

theorem solution :
    (latticeLagData (fun _ => zeroField) zeroField (fun _ => 0) (le_refl (0 : ℝ))).hFull ≠ 0 := by
  exact h43_lag_ne_zero

