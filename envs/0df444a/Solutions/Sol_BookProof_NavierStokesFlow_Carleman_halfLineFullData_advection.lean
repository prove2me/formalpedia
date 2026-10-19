-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:11:11.12083+00:00
-- url     : https://prove2.me/submissions/e8f689e5-d5d8-4492-abdb-4a0b944fe39f

import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_weyl_momOp_diagOp
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_sum
-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa
open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_diag_add (a b : ℕ → ℝ) : diagOp a + diagOp b = diagOp (fun n => a n + b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, diagOp_coe, diagFun,
    Complex.ofReal_add]
  ring

open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_diag_sub (a b : ℕ → ℝ) : diagOp a - diagOp b = diagOp (fun n => a n - b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.sub_apply, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, diagOp_coe, diagFun,
    Complex.ofReal_sub]
  ring

open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_diag_smul (r : ℝ) (a : ℕ → ℝ) : (r : ℂ) • diagOp a = diagOp (fun n => r * a n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.smul_apply, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, diagOp_coe,
    diagFun, Complex.ofReal_mul, smul_eq_mul]
  ring

open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_diag_zero : diagOp (fun _ => (0:ℝ)) = 0 := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp [diagFun]

open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_diag_comp (a b : ℕ → ℝ) : (diagOp a).comp (diagOp b) = diagOp (fun n => a n * b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.comp_apply, diagOp_coe, diagFun, Complex.ofReal_mul]
  ring

open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_diag_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) :
    (∑ i ∈ s, diagOp (a i)) = diagOp (fun n => ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact h43_diag_zero.symm
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, ih, h43_diag_add]
    congr 1; funext n; rw [Finset.sum_insert hx]

open BookProof.NavierStokesFlow.DiagonalEsa BookProof.NavierStokesFlow.FullEsa in
theorem h43_diagFull_ham (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    (diagFullData c p nu).hamiltonian = diagOp (diagFullSymbol c p nu) := by
  show (∑ i : Fin 3, ((diagOp (p i)).comp ((∑ j : Fin 3, (diagOp (c (nsVelIdx j))).comp
      (diagOp (c (nsGradIdx i j)))) - (nu : ℂ) • diagOp (c (nsLapIdx i)))
      + ((∑ j : Fin 3, (diagOp (c (nsVelIdx j))).comp
      (diagOp (c (nsGradIdx i j)))) - (nu : ℂ) • diagOp (c (nsLapIdx i))).comp (diagOp (p i))) :
      lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ) = _
  simp only [h43_diag_comp]
  simp only [h43_diag_sum, h43_diag_smul, h43_diag_sub, h43_diag_comp, h43_diag_add]
  congr 1; funext n
  unfold diagFullSymbol
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

open BookProof.NavierStokesFlow.DiagonalEsa BookProof.NavierStokesFlow.FullEsa
  BookProof.NavierStokesFlow.Carleman in
theorem h43_hl_adv (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) :
    (halfLineFullData c nu).advection i = diagOp (halfLineAlpha c nu i) := by
  show ((∑ j : Fin 3, (diagOp (c (nsVelIdx j))).comp (diagOp (c (nsGradIdx i j))))
      - (nu : ℂ) • diagOp (c (nsLapIdx i)) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ) = _
  simp only [h43_diag_comp]
  rw [h43_diag_sum, h43_diag_smul, h43_diag_sub]
  rfl

open BookProof.NavierStokesFlow.DiagonalEsa BookProof.NavierStokesFlow.FullEsa
  BookProof.NavierStokesFlow.Carleman in
theorem h43_hl_ham (c : Fin 15 → ℕ → ℝ) (nu : ℝ) :
    (halfLineFullData c nu).hamiltonian = tridiagOp (nsCoupling (halfLineSymbol c nu)) := by
  show (∑ i : Fin 3, (momOp.comp ((∑ j : Fin 3, (diagOp (c (nsVelIdx j))).comp
      (diagOp (c (nsGradIdx i j)))) - (nu : ℂ) • diagOp (c (nsLapIdx i)))
      + ((∑ j : Fin 3, (diagOp (c (nsVelIdx j))).comp
      (diagOp (c (nsGradIdx i j)))) - (nu : ℂ) • diagOp (c (nsLapIdx i))).comp momOp) :
      lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ) = _
  simp only [h43_diag_comp]
  simp only [h43_diag_sum, h43_diag_smul, h43_diag_sub, weyl_momOp_diagOp]
  rw [tridiagOp_sum]
  congr 1; funext n
  simp only [nsCoupling, halfLineSymbol, halfLineAlpha, Complex.ofReal_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib]

theorem solution (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) :
    (halfLineFullData c nu).advection i = diagOp (halfLineAlpha c nu i) := by
  exact h43_hl_adv c nu i

