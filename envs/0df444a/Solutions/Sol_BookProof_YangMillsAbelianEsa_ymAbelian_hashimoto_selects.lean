-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T11:40:47.490377+00:00
-- url     : https://prove2.me/submissions/02fd7481-5124-47c5-9865-1c29b8b172ca

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Theorems.Thm_BookProof_YangMillsAbelianEsa_ymAbelian_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_EsaClosure_hashimoto_multishift_selects_esa
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ (L2d 99)) (γ : ℕ → ℂ)
    (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (X : ℕ → L2d 99 →L[ℂ] L2d 99),
      IsSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) 0) A ∧
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2d 99 →ₗ[ℂ] L2d 99))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (L2d 99) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Filter.Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) Filter.atTop
        (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (L2d 99)) (A' : Dom' →ₗ[ℂ] L2d 99),
        IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2d 99) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  hashimoto_multishift_selects_esa b _ polyGaussCore_dense
      (ymHamiltonian_symmetricOn (coreRepPoly 99) 0)
      ymAbelian_essentiallySelfAdjointOn_core γ hγ
