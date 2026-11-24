-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.idxB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.645156+00:00
-- url     : https://prove2.me/submissions/4120781c-5516-4381-a281-65ed1b47c57c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_hstar
import Theorems.Thm_P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_isSymm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_nondeg
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice RationalHermitianForm
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {D : ℕ} (w : HeightOneSpectrum (𝓞 K)) (A B C : Submodule (𝓞 K) (Fin D → K))
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) :
    idx w A B = - idx w B A ∧ idx w A C = idx w A B + idx w B C ∧
      (B ≤ A → idx w A B = Formalism.HermitianLatticesTheory.locLen w.asIdeal A B) := by
  have hH : (1 : Matrix (Fin D) (Fin D) K)ᴴ = 1 := Matrix.conjTranspose_one
  have hs := hform_isSymm (1 : Matrix (Fin D) (Fin D) K) (herm_entry' hH)
  have hn := hform_nondeg (1 : Matrix (Fin D) (Fin D) K) hs (by simp)
  have : w.asIdeal.IsMaximal := w.isMaximal
  have h := Formalism.HermitianLatticesTheory.indexBasic (𝓞 K) K (Fin D → K) (hform 1) hs hn hstar w.asIdeal A B C hA hB hC
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
end Formalism.DivisionValues.exponent_index_lattice
