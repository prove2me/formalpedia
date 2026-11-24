-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:46.396261+00:00
-- url     : https://prove2.me/submissions/e16dd683-46e6-404c-9f08-dfc4a48fd01c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop

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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  obtain ⟨hTC, hconj, -⟩ := hK
  by_contra h
  push_neg at h
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
  have hc := hTC.isComplex w
  rw [NumberField.InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext a
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hconj, h]
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
