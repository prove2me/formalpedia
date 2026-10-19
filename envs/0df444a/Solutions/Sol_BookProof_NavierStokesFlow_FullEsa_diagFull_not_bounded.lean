-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:47:51.728511+00:00
-- url     : https://prove2.me/submissions/aea9fee6-f560-4f31-a47b-17af76ab064c

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded
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
open BookProof.NavierStokesFlow.DiagonalEsa BookProof.NavierStokesFlow.FullEsa in
theorem h43_diagUnb_ham : diagUnboundedData.hamiltonian = diagOp (fun n => -(2 * (n : ℝ))) := by
  show (diagFullData _ _ _).hamiltonian = _
  rw [h43_diagFull_ham]
  congr 1; funext n
  have h1 : ∀ j : Fin 3, (nsVelIdx j = nsLapIdx 0) = False := by decide
  have h2 : ∀ i j : Fin 3, (nsGradIdx i j = nsLapIdx 0) = False := by decide
  have h3 : (nsLapIdx 1 = nsLapIdx 0) = False := by decide
  have h4 : (nsLapIdx 2 = nsLapIdx 0) = False := by decide
  simp only [diagFullSymbol, Fin.sum_univ_three, h1, h2, h3, h4, if_false, if_true]
  simp

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
theorem h43_norm_basis (n : ℕ) : ‖basis n‖ = 1 := by
  show ‖(lp.single 2 n (1:ℂ) : lp (fun _ : ℕ => ℂ) 2)‖ = 1
  rw [lp.norm_single (by norm_num)]; simp

theorem solution :
    ¬ ∃ C : ℝ, ∀ f : diagUnboundedData.D, ‖diagUnboundedData.hamiltonian f‖ ≤ C * ‖f‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (basis n)
  have e := LinearMap.congr_fun h43_diagUnb_ham (basis n)
  have e2 : ‖diagUnboundedData.hamiltonian (basis n)‖ = ‖diagOp (fun n => -(2 * (n : ℝ))) (basis n)‖ := by
    exact congrArg norm e
  rw [e2] at this
  change _ ≤ C * ‖(basis n : BookProof.NavierStokesFlow.lpFiniteModes ℕ)‖ at this
  rw [h43_diagOp_basis, norm_smul, h43_norm_basis] at this
  simp at this
  have : (0:ℝ) ≤ n := n.cast_nonneg
  linarith

