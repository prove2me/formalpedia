-- Prove2me | solution 1 for Bl.general_b_fact_left_alt_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:29.329795+00:00
-- url     : https://prove2.me/submissions/e50175c8-2bf1-4b17-9294-3beb864da869

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
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
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Lemmata_GeneralBFactLeftAltForm_MQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left_alt_form
namespace Bl.general_b_fact_left_alt_form
theorem _root_.solution :
  ∀ {O : Type} [inst : CommRing.{0} O]
  [inst_1 : @IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))]
  [@IsDiscreteValuationRing.{0} O inst inst_1] {W : Type} [inst_3 : AddCommGroup.{0} W]
  [inst_4 :
    @Module.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
      (@OreLocalization.instSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
      (@AddCommGroup.toAddCommMonoid.{0} W inst_3)]
  [inst_5 :
    @Module.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} W inst_3)]
  [inst_6 :
    @IsScalarTower.{0, 0, 0} O (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
      (@OreLocalization.instSMulOfIsScalarTower.{0, 0, 0} O O O
        (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        (@Monoid.toMulAction.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst)))
        (@instSMulOfMul.{0} O
          (@Distrib.toMul.{0} O
            (@instDistribOfSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        (@instSMulOfMul.{0} O
          (@Distrib.toMul.{0} O
            (@instDistribOfSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        _ _)
      (@SMulZeroClass.toSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
        (@AddZero.toZero.{0} W
          (@AddZeroClass.toAddZero.{0} W
            (@AddMonoid.toAddZeroClass.{0} W
              (@SubNegMonoid.toAddMonoid.{0} W
                (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
          (@AddMonoid.toAddZeroClass.{0} W
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
            (@OreLocalization.instMonoid.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
              (@nonZeroDivisors.{0} O
                (@Semiring.toMonoidWithZero.{0} O
                  (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
              (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3)))
            (@Module.toDistribMulAction.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
              (@OreLocalization.instSemiring.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
                (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                  (@nonZeroDivisors.{0} O
                    (@Semiring.toMonoidWithZero.{0} O
                      (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4))))
      (@SMulZeroClass.toSMul.{0, 0} O W
        (@AddZero.toZero.{0} W
          (@AddZeroClass.toAddZero.{0} W
            (@AddMonoid.toAddZeroClass.{0} W
              (@SubNegMonoid.toAddMonoid.{0} W
                (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} O W
          (@AddMonoid.toAddZeroClass.{0} W
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))
          (@DistribMulAction.toDistribSMul.{0, 0} O W
            (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
            (@SubNegMonoid.toAddMonoid.{0} W (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3)))
            (@Module.toDistribMulAction.{0, 0} O W
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5))))]
  (M :
    @Submodule.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)
  (y : W),
  @Membership.mem.{0, 0} W
      (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
        (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
          (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
        (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4)
      (@SetLike.instMembership.{0, 0}
        (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4)
        W
        (@Submodule.setLike.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_4))
      (@Formalism.MainNotions.G.MQ.{0, 0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) W (@FractionRing.field.{0} O inst inst_1) inst_3 inst_4 O
        inst inst_5
        (@OreLocalization.instAlgebra.{0, 0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
          (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
            (@nonZeroDivisors.{0} O
              (@Semiring.toMonoidWithZero.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
          O (@CommRing.toCommSemiring.{0} O inst) (@Algebra.id.{0} O (@CommRing.toCommSemiring.{0} O inst)))
        inst_6 M)
      y →
    @Exists.{1} O fun (a : O) ↦
      And
        (@Ne.{1} O a
          (@OfNat.ofNat.{0} O (nat_lit 0)
            (@Zero.toOfNat0.{0} O
              (@MulZeroClass.toZero.{0} O
                (@instMulZeroClassOfSemiring.{0} O
                  (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))))
        (@Membership.mem.{0, 0} W
          (@Submodule.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
            (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)
          (@SetLike.instMembership.{0, 0}
            (@Submodule.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)
            W
            (@Submodule.setLike.{0, 0} O W (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5))
          M
          (@HSMul.hSMul.{0, 0, 0} O W W
            (@instHSMul.{0, 0} O W
              (@SMulZeroClass.toSMul.{0, 0} O W
                (@AddZero.toZero.{0} W
                  (@AddZeroClass.toAddZero.{0} W
                    (@AddMonoid.toAddZeroClass.{0} W
                      (@SubNegMonoid.toAddMonoid.{0} W
                        (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))))
                (@DistribSMul.toSMulZeroClass.{0, 0} O W
                  (@AddMonoid.toAddZeroClass.{0} W
                    (@SubNegMonoid.toAddMonoid.{0} W
                      (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3))))
                  (@DistribMulAction.toDistribSMul.{0, 0} O W
                    (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
                    (@SubNegMonoid.toAddMonoid.{0} W
                      (@AddGroup.toSubNegMonoid.{0} W (@AddCommGroup.toAddGroup.{0} W inst_3)))
                    (@Module.toDistribMulAction.{0, 0} O W
                      (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                      (@AddCommGroup.toAddCommMonoid.{0} W inst_3) inst_5)))))
            a y)) := by
  intro O _ _ _ W _ _ _ _ M y hy
  rw [Formalism.MainNotions.G.MQ] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨b, hb, hbx⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨(s : O) * b, mul_ne_zero (nonZeroDivisors.ne_zero s.2) hb, ?_⟩
    have key : ((s : O) * b) • (c • x) = r • (b • x) := by
      rw [← algebraMap_smul (Formalism.MainNotions.G.KK O) ((s : O) * b) (c • x), smul_smul,
        ← algebraMap_smul (Formalism.MainNotions.G.KK O) r (b • x), ← algebraMap_smul (Formalism.MainNotions.G.KK O) b x, smul_smul]
      congr 1
      rw [map_mul, ← hrs]
      ring
    rw [key]
    exact M.smul_mem r hbx
end Bl.general_b_fact_left_alt_form
