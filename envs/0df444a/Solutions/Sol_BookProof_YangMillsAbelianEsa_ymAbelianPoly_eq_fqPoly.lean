-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.ymAbelianPoly_eq_fqPoly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:54:42.235882+00:00
-- url     : https://prove2.me/submissions/7674f5e5-cf90-4d9a-8a07-35e607cf0935

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.ymAbelianPoly_eq_fqPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Theorems.Thm_BookProof_YangMillsAbelianEsa_sum_ymMagVec_X
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_mulXPoly_apply
import Theorems.Thm_BookProof_YangMillsAbelianEsa_gramWeyl_eq
import Theorems.Thm_BookProof_YangMillsAbelianEsa_sum_ymMomVec_mom
import Theorems.Thm_BookProof_HermiteRelative_momPoly_eq_ymMomOp
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.FullQuadratic
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
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
theorem ym_apply_aux (p : MvPolynomial (Fin 99) ℂ) :
    ymAbelianPoly p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m : Fin 24,
              BookProof.YangMillsHermite.momOp (ymMomIdx m) (BookProof.YangMillsHermite.momOp (ymMomIdx m) p))
            + ∑ m : Fin 24, mulOp (magPoly 0 (decodeSpace m) (decodeColor m))
                (mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) p)) := by
  simp only [ymAbelianPoly, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]

theorem ym_magX_aux (m : Fin 24) :
    ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • mulXPoly (d := 99) n
      = mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) := by
  refine LinearMap.ext fun q => ?_
  rw [← BookProof.YangMillsAbelianEsa.sum_ymMagVec_X m]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, BookProof.NavierStokesFlow.DifferentialL2.mulXPoly_apply,
    BookProof.YangMillsHermite.mulOp, LinearMap.mulLeft_apply, Finset.sum_mul, smul_mul_assoc]

open BookProof BookProof.YangMillsAbelianEsa in
theorem solution : ymAbelianPoly = fqPoly ymFqP ymFqQ 0 0 0 := by 
  refine LinearMap.ext fun p => ?_
  have hfo : foPoly (d := 99) 0 0 p = 0 := by simp [foPoly]
  have hP := BookProof.YangMillsAbelianEsa.gramWeyl_eq ymMomVec (fun i => momPoly (d := 99) i) p
  have hQ := BookProof.YangMillsAbelianEsa.gramWeyl_eq ymMagVec (fun i => mulXPoly (d := 99) i) p
  have hfq : fqPoly ymFqP ymFqQ 0 0 0 p
      = (∑ i : Fin 99, ∑ j : Fin 99,
          ((ymFqP i j : ℝ) : ℂ) • weylProd (momPoly i) (momPoly j) p)
        + ∑ i : Fin 99, ∑ j : Fin 99,
            ((ymFqQ i j : ℝ) : ℂ) • weylProd (mulXPoly i) (mulXPoly j) p := by
    rw [fqPoly, fqQuadPoly]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Pi.zero_apply,
      Complex.ofReal_zero, zero_smul, add_zero, hfo]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  rw [hfq]
  simp only [ymFqP, ymFqQ] at hP hQ ⊢
  rw [hP, hQ, ym_apply_aux, smul_add]
  simp only [BookProof.YangMillsAbelianEsa.sum_ymMomVec_mom, ym_magX_aux]
  simp only [BookProof.HermiteRelative.momPoly_eq_ymMomOp]
