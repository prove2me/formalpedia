-- Prove2me | solution 1 for BookProof.FullQuadratic.fqQuadPoly_hermiteMv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T13:57:50.502612+00:00
-- url     : https://prove2.me/submissions/9d250b64-90dc-4d1a-9bb9-d4a1f77bbd4d

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.fqQuadPoly_hermiteMv
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Theorems.Thm_BookProof_FullQuadratic_fqTerm_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FullQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (P Q S : Fin d → Fin d → ℝ) (a : Fin d →₀ ℕ) :
    fqQuadPoly P Q S (hermiteMv a)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a
        + ∑ i, ∑ j, (fqAmp P Q S i j • hermiteMv (a + pvec i j)
            + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
                * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
                  • hermiteMv (a - pvec i j)
            + (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)) := by

  classical
  rw [fqQuadPoly, LinearMap.sum_apply]
  have hterm : ∀ i : Fin d, (∑ j, (((P i j : ℝ) : ℂ)
        • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j)))
        (hermiteMv a)
      = ∑ j, (fqAmp P Q S i j • hermiteMv (a + pvec i j)
        + ((starRingEnd ℂ) (fqMl P Q S i j) * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
            * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • hermiteMv (a - pvec i j)
        + (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0)) := by
    intro i
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => fqTerm_hermiteMv P Q S i j a
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- split the double sum into its five families
  simp only [Finset.sum_add_distrib]
  -- the diagonal family
  have hdiag : ∑ i : Fin d, ∑ j : Fin d,
      (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a := by
    have h1 : ∀ i : Fin d, ∑ j : Fin d,
        (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0)
        = (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a := by
      intro i
      rw [Finset.sum_ite_eq Finset.univ i (fun _ => (((Q i i + P i i / 4 : ℝ) : ℂ))
        • hermiteMv a)]
      simp
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.sum_smul, fqSymbol]
    push_cast
    ring_nf
  -- the exchange families combine after swapping the two indices
  have hswap : ∑ i : Fin d, ∑ j : Fin d,
      ((starRingEnd ℂ) (fqMl P Q S i j) * (a i : ℂ)) • hermiteMv (shiftm a j i)
      = ∑ i : Fin d, ∑ j : Fin d,
        ((starRingEnd ℂ) (fqMl P Q S j i) * (a j : ℂ)) • hermiteMv (shiftm a i j) :=
    Finset.sum_comm
  have hcomb : ∀ i j : Fin d,
      ((starRingEnd ℂ) (fqMl P Q S j i) * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
        = (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j) := by
    intro i j
    rw [fqExch]
    module
  have hfinal : ∑ i : Fin d, ∑ j : Fin d,
        ((starRingEnd ℂ) (fqMl P Q S j i) * (a j : ℂ)) • hermiteMv (shiftm a i j)
      + ∑ i : Fin d, ∑ j : Fin d, (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
      = ∑ i : Fin d, ∑ j : Fin d, (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hcomb i j
  rw [hdiag, hswap, ← hfinal]
  abel
