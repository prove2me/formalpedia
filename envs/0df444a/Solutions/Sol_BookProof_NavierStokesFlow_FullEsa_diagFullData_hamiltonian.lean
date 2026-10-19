-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:33:08.879001+00:00
-- url     : https://prove2.me/submissions/2723d543-22fe-41fc-bca1-84ace4a63a5b

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)
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

theorem solution (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    (diagFullData c p nu).hamiltonian = diagOp (diagFullSymbol c p nu) := by
  exact h43_diagFull_ham c p nu

