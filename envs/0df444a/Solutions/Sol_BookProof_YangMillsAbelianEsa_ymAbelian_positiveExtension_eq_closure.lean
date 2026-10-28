-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:45:10.766005+00:00
-- url     : https://prove2.me/submissions/e55864aa-1c38-4f19-8b3a-3341e7f930bd

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Theorems.Thm_BookProof_YangMillsAbelianEsa_ymAbelian_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_EsaClosure_positiveExtension_eq_closure_of_esa
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
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

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {Dom : Submodule ℂ (L2d 99)}
    {A : Dom →ₗ[ℂ] L2d 99}
    (hA : IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) 0) A) :
    Dom = clDom (ymHamiltonian (coreRepPoly 99) 0) ∧
      ∀ (x : L2d 99) (h : x ∈ Dom) (h' : x ∈ clDom (ymHamiltonian (coreRepPoly 99) 0)),
        A ⟨x, h⟩ = clExt (ymHamiltonian (coreRepPoly 99) 0) polyGaussCore_dense
          (ymHamiltonian_symmetricOn (coreRepPoly 99) 0) ⟨x, h'⟩ :=
  positiveExtension_eq_closure_of_esa polyGaussCore_dense
      (ymHamiltonian_symmetricOn (coreRepPoly 99) 0)
      ymAbelian_essentiallySelfAdjointOn_core hA
