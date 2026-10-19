-- Prove2me | solution 2 for BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:52:08.652634+00:00
-- url     : https://prove2.me/submissions/c069b8cd-0bf6-4055-882f-7e1af1e0b83f

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_NSFullData_hasZeroDeficiencyOn_of_total_eigenvectors
-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn
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
theorem h43_diagOp_basis (c : ℕ → ℝ) (n : ℕ) : diagOp c (basis n) = ((c n : ℂ)) • basis n := by
  apply Subtype.ext
  ext k
  show diagFun c _ k = _
  simp only [diagFun, basis, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = n
  · subst h; simp
  · simp [lp.single_apply, h]

open BookProof.NavierStokesFlow.DiagonalEsa in
theorem h43_basis_total (w : lp (fun _ : ℕ => ℂ) 2)
    (h : ∀ i, (inner ℂ (((basis i : BookProof.NavierStokesFlow.lpFiniteModes ℕ) :
      lp (fun _ : ℕ => ℂ) 2)) w : ℂ) = 0) : w = 0 := by
  ext n
  have := h n
  simp only [basis] at this
  rw [lp.inner_single_left] at this
  simpa using this
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
open BookProof.NavierStokesFlow.DiagonalEsa BookProof.NavierStokesFlow.FullEsa in
theorem h43_diagFull_zd (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn (diagFullData c p nu).D (diagFullData c p nu).hamiltonian := by
  refine NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors (diagFullData c p nu)
    (fun n => basis n) (diagFullSymbol c p nu) ?_ ?_
  · intro n
    rw [h43_diagFull_ham]
    exact h43_diagOp_basis _ n
  · intro w hw
    exact h43_basis_total w hw

theorem solution :
    HasZeroDeficiencyOn diagUnboundedData.D diagUnboundedData.hamiltonian := by
  exact h43_diagFull_zd _ _ _

