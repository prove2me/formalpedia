-- Prove2me | solution 1 for Bl.general_b_fact_left_alt.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:44.252689+00:00
-- url     : https://prove2.me/submissions/d21d62a2-c2bb-438d-a1b6-773bcb300431

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_SArith
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Lemmata_GeneralBFactLeftAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left_alt
namespace Bl.general_b_fact_left_alt
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsLattice.{0, 0, 0} E Λ →
    ∀ (v : S.V),
      Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} c 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} c v)) := by
  intro E _ _ _ S Λ hΛ v
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]; trivial
  obtain ⟨y, hy, z, rfl⟩ :=
    (IsLocalization.mem_span_iff (R := NumberField.RingOfIntegers E)
      (M := nonZeroDivisors (NumberField.RingOfIntegers E)) (S := E)).mp hv
  rw [Submodule.span_eq] at hy
  refine ⟨z, nonZeroDivisors.coe_ne_zero z, ?_⟩
  rw [← IsScalarTower.algebraMap_smul E (z : NumberField.RingOfIntegers E), smul_smul,
    IsLocalization.mk'_spec', map_one, one_smul]
  exact hy
end Bl.general_b_fact_left_alt
