-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:11.542908+00:00
-- url     : https://prove2.me/submissions/e7f3a470-e547-4620-b284-94d119e5f7c4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_exists_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
theorem _root_.solution (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) : Algebra.adjoin F {a} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton a)))
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
