-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.discr_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:46.07713+00:00
-- url     : https://prove2.me/submissions/33efcafb-000c-41e3-b118-dcb8b1809bf6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_isTotallyReal

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
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : 0 < discr F := by
  haveI := isTotallyReal hK hF
  first
    | exact NumberField.discr_pos_of_isTotallyReal F
    | (have h := NumberField.sign_discr F
       rw [IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero] at h
       exact Int.sign_eq_one_iff_pos.mp h)
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
