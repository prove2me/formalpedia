-- Prove2me | solution 1 for Formalism.L2.DIV.mem_valLatF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:28.738839+00:00
-- url     : https://prove2.me/submissions/de35b764-4218-4f30-87b1-76aa9f72b89a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {Cl V : Type}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V) (x : Fin n → K) :
    x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by
  first
  | exact ⟨fun h c => h c (Set.mem_univ c), fun h c _ => h c⟩
  | (unfold valLatF; simp [Submodule.mem_pi])
  | (simp only [valLatF, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, forall_const,
      LinearMap.restrictScalars_apply])
end Formalism.L2.DIV
