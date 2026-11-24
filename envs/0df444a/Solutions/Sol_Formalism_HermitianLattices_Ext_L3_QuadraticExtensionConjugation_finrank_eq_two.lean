-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:03.698796+00:00
-- url     : https://prove2.me/submissions/21822961-928c-4fb2-9e58-d1ac5cdbefba

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_exists_star_ne
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : finrank F K = 2 := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  have hli : LinearIndependent F ![(1 : K), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply ha
      have htK : algebraMap F K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      have hA : a = algebraMap F K (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff htK]
        linear_combination hst
      exact (hF a).2 ⟨_, hA.symm⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), a]) := by
    intro x _
    obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
    apply Submodule.add_mem
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)
  rw [Module.finrank_eq_card_basis (Basis.mk hli hsp)]
  simp
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
