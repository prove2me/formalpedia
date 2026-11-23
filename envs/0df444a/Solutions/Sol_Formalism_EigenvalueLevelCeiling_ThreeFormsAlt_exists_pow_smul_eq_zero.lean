-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.exists_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:45.012629+00:00
-- url     : https://prove2.me/submissions/002e6467-f9f0-4532-8e42-74611f05130b

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
open IsLocalRing
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (O : Type) [CommRing O] [IsLocalRing O] (ϖ : O)
    (hϖ : ϖ ∈ maximalIdeal O) (M : Type) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, ∀ x : M, ϖ ^ n • x = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun x => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hmm : m = maximalIdeal O := IsLocalRing.eq_maximalIdeal hm
    subst hmm
    have hk : ∀ x : M, ϖ • x ∈ N := by
      intro x
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply f.injective
      rw [map_smul, map_zero]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f (Submodule.Quotient.mk x))
      rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ hϖ
    refine ⟨n + 1, fun x => ?_⟩
    have := hn ⟨ϖ • x, hk x⟩
    rw [pow_succ, mul_smul]
    simpa using congrArg Subtype.val this
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
