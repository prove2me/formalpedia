-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.isTotallyReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:09.103497+00:00
-- url     : https://prove2.me/submissions/93bf7fa5-5fda-4020-b512-5b296a3dc85a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_star_algebraMap

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
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : IsTotallyReal F := by
  obtain ⟨-, hconj, -⟩ := hK
  refine ⟨fun w => ?_⟩
  obtain ⟨v, rfl⟩ := NumberField.InfinitePlace.comap_surjective (k := F) (K := K) w
  try dsimp only
  rw [← NumberField.InfinitePlace.mk_embedding v, NumberField.InfinitePlace.comap_mk]
  by_contra h
  rw [NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isComplex_mk_iff] at h
  apply h
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext u
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hconj, star_algebraMap hF]
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
