-- Prove2me | solution 2 for BookProof.FullQuadratic.fqOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:37:37.693118+00:00
-- url     : https://prove2.me/submissions/7dea8a3d-2223-451c-9b2c-b95b48b2156d

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStep
import Definitions.Def_ChapterCarlemanSimplex
import Definitions.Def_ChapterModeQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_weylProd_polySym
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_add
import Theorems.Thm_BookProof_HermiteRelative_polySym_sum
import Theorems.Thm_BookProof_HermiteRelative_polySym_foPoly
import Theorems.Thm_BookProof_HermiteRelative_polySym_momPoly
import Theorems.Thm_BookProof_HermiteRelative_polySym_mulXPoly
import Theorems.Thm_BookProof_HermiteRelative_symmetricOn_of_polySym
-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqOp_symmetric
open BookProof.HermiteProductCore
open BookProof.FullQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

open BookProof.YangMillsHermite in
theorem fq_polySym (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (fqPoly P Q S b b') := by
  have hterm : ∀ i j : Fin d, PolySym
      ((((P i j : ℝ) : ℂ) • weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • weylProd (mulXPoly i) (momPoly j)) :
        Module.End ℂ (MvPolynomial (Fin d) ℂ)) := fun i j =>
    PolySym.add (PolySym.add
      (PolySym.real_smul (weylProd_polySym (BookProof.HermiteRelative.polySym_momPoly i)
        (BookProof.HermiteRelative.polySym_momPoly j)))
      (PolySym.real_smul (weylProd_polySym (BookProof.HermiteRelative.polySym_mulXPoly i)
        (BookProof.HermiteRelative.polySym_mulXPoly j))))
      (PolySym.real_smul (weylProd_polySym (BookProof.HermiteRelative.polySym_mulXPoly i)
        (BookProof.HermiteRelative.polySym_momPoly j)))
  have hq : PolySym (fqQuadPoly P Q S : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :=
    BookProof.HermiteRelative.polySym_sum Finset.univ _ (fun i _ =>
      BookProof.HermiteRelative.polySym_sum Finset.univ _ (fun j _ => hterm i j))
  exact PolySym.add hq (BookProof.HermiteRelative.polySym_foPoly b b')

theorem solution (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (fqOp P Q S b b') :=
  BookProof.HermiteRelative.symmetricOn_of_polySym (fq_polySym P Q S b b')
