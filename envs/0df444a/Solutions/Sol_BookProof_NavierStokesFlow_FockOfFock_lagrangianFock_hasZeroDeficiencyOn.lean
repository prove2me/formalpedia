-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:45:53.524785+00:00
-- url     : https://prove2.me/submissions/9a79742c-fb4d-48f3-800b-7690f3d8afaa

import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_hasZeroDeficiencyOn
-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
open BookProof.NavierStokesFlow.FockOfFock in
theorem h43_lpd_coe {ι : Type*} (c : ι → ℝ) (f : BookProof.NavierStokesFlow.lpFiniteModes ι) (n : ι) :
    (((lpDiag c f : BookProof.NavierStokesFlow.lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) n
      = (c n : ℂ) * ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) n := rfl

open BookProof.NavierStokesFlow.FockOfFock in
theorem h43_lpd_add {ι : Type*} (a b : ι → ℝ) : lpDiag a + lpDiag b = lpDiag (fun n => a n + b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, h43_lpd_coe,
    Complex.ofReal_add]; ring

open BookProof.NavierStokesFlow.FockOfFock in
theorem h43_lpd_smul {ι : Type*} (r : ℝ) (a : ι → ℝ) : (r : ℂ) • lpDiag a = lpDiag (fun n => r * a n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.smul_apply, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    h43_lpd_coe, Complex.ofReal_mul]; ring

open BookProof.NavierStokesFlow.FockOfFock in
theorem h43_lpd_comp {ι : Type*} (a b : ι → ℝ) : (lpDiag a).comp (lpDiag b) = lpDiag (fun n => a n * b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.comp_apply, h43_lpd_coe, Complex.ofReal_mul]; ring

open BookProof.NavierStokesFlow.FockOfFock in
theorem h43_lpd_zero {ι : Type*} : lpDiag (fun _ : ι => (0:ℝ)) = 0 := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp [h43_lpd_coe]

open BookProof.NavierStokesFlow.FockOfFock in
theorem h43_lpd_sum {ι κ : Type*} (s : Finset κ) (a : κ → ι → ℝ) :
    (∑ i ∈ s, lpDiag (a i)) = lpDiag (fun n => ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact h43_lpd_zero.symm
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, ih, h43_lpd_add]
    congr 1; funext n; rw [Finset.sum_insert hx]

theorem solution (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) :
    HasZeroDeficiencyOn (lagrangianFockData nu hnu p q dr force cst).D
      (lagrangianFockData nu hnu p q dr force cst).hFull := by
  show HasZeroDeficiencyOn (FockDom M)
    ((((1 / 2 : ℝ) : ℂ) • ∑ i : Fin 3, (lpDiag (confEnergy (p i))).comp (lpDiag (confEnergy (p i))))
      + (((nu : ℝ) : ℂ) • ∑ i : Fin 3, (lpDiag (confEnergy (q i))).comp (lpDiag (confEnergy (q i))))
      + (∑ i : Fin 3, ((force i : ℝ) : ℂ) • lpDiag (confEnergy (dr i)))
      + lpDiag (confEnergy cst))
  simp only [h43_lpd_comp, h43_lpd_sum, h43_lpd_smul, h43_lpd_add]
  exact lpDiag_hasZeroDeficiencyOn _

