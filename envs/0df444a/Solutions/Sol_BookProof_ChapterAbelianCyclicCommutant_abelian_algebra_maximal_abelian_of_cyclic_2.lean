-- Prove2me | solution 2 for BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:23:25.043234+00:00
-- url     : https://prove2.me/submissions/f38259d9-dd95-49e5-b0ec-93fbdf20103d

import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_centralizer_repSet
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_bicommutant_repSet
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_commutant_repSet_isCommutative_inc
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_repSet_gelfandRep
import Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_denseRange_repVec_gelfandRep
-- Generated from ChapterAbelianCyclicCommutant.lean — theorem solution
open BookProof.ChapterAbelianCyclicCommutant


noncomputable section

open MeasureTheory Complex WeakDual


open BookProof.ChapterLinftyMultiplication BookProof.ChapterLinftyMaximalAbelian
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralCommutant
open BookProof.ChapterAbelianCyclicModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

variable {A : Type*} [CommCStarAlgebra A]
theorem solution (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)
    (hcyc : DenseRange fun a : A => rho a xi) :
    (Set.range fun a : A => rho a).centralizer.centralizer
        = (Set.range fun a : A => rho a).centralizer ∧
      ∀ S R : H →L[ℂ] H, S ∈ (Set.range fun a : A => rho a).centralizer →
        R ∈ (Set.range fun a : A => rho a).centralizer → S * R = R * S := by
  have hcyc' := denseRange_repVec_gelfandRep hcyc
  rw [← repSet_gelfandRep rho]
  refine ⟨?_, fun S R hS hR => commutant_repSet_isCommutative_inc (gelfandRep rho) xi hcyc' hS hR⟩
  rw [bicommutant_repSet (gelfandRep rho) xi hcyc', centralizer_repSet (gelfandRep rho) xi hcyc']
