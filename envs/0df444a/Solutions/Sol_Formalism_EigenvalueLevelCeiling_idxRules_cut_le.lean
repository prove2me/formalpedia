-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:18.84288+00:00
-- url     : https://prove2.me/submissions/05dc1289-eea0-4e04-827d-f2ae8d84b1df

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (p : Ideal R) [p.IsPrime] (W' : Submodule K V) (A B : Submodule R V)
    (hfin : Module.length R (↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype) ≠ ⊤) :
    locLen p (A ⊓ W'.restrictScalars R) (B ⊓ W'.restrictScalars R) ≤ locLen p A B := by
  unfold locLen
  refine ENat.toNat_le_toNat ?_ hfin
  have hle : localization₂ p (A ⊓ W'.restrictScalars R) ≤ localization₂ p A := locBasic_locS_mono _ inf_le_left
  let f : (↥(localization₂ p (A ⊓ W'.restrictScalars R)) ⧸
        (localization₂ p (B ⊓ W'.restrictScalars R)).comap (localization₂ p (A ⊓ W'.restrictScalars R)).subtype) →ₗ[R]
      (↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (by
      rintro ⟨x, hx⟩ hxB
      exact locBasic_locS_mono _ inf_le_left hxB)
  refine Module.length_le_of_injective f ?_
  rw [injective_iff_map_eq_zero]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    intro hx
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨x, s, hs, hsx⟩ := x
    obtain ⟨t, ht, htx⟩ := hx
    refine ⟨s * t, mul_mem hs ht, ?_, ?_⟩
    · rw [mul_smul]
      exact B.smul_mem s htx
    · rw [mul_comm, mul_smul]
      exact (W'.restrictScalars R).smul_mem t hsx.2
end Formalism.EigenvalueLevelCeiling
