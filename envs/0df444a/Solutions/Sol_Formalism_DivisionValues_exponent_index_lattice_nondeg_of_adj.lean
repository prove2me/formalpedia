-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.nondeg_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:17.985431+00:00
-- url     : https://prove2.me/submissions/4d7b6d42-8fca-436b-b107-49670720ce56

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

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
variable {K V W : Type} [Field K] [StarRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution (hV : V →ₗ⋆[K] V →ₗ[K] K) (hVn : hV.Nondegenerate)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hWs : hW.IsSymm) (E : W →ₗ[K] V) (P : V →ₗ[K] W)
    (adj : ∀ x z, hW (P x) z = hV x (E z)) (hE : Function.Injective E) : hW.Nondegenerate := by
  have hR : hW.SeparatingRight := by
    intro z hz
    apply hE
    rw [map_zero]
    exact hVn.2 (E z) (fun x => by rw [← adj]; exact hz (P x))
  exact ⟨fun w hw => hR w (fun z => hWs.isRefl w z (hw z)), hR⟩
end Formalism.DivisionValues.exponent_index_lattice
