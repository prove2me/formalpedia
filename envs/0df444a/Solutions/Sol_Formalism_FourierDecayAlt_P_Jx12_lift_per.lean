-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx12.lift_per
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:07.428616+00:00
-- url     : https://prove2.me/submissions/40db96fb-1973-4d21-addc-87c612a62637

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx12_mem_idl_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx12
namespace Formalism.FourierDecayAlt.P.Jx12
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ)
    (y : E) : y ∈ S6.liftLat E g ν s ↔ (g : E) ^ 2 * y ∈ S6.perLat E g (-ν) s := by
  have h1 : y ∈ S6.zsub E (S6.idl E g (-1) (-ν)) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g 1 (-ν)) := by
    have h := mem_idl_shift E g hg (-1) (-ν) y
    rwa [show (-1 : ℤ) + 2 = 1 by norm_num] at h
  have h2 : ∀ z : E, z ∈ S6.zsub E (S6.idl E g 0 (-ν)) ↔
      (g : E) ^ 2 * z ∈ S6.zsub E (S6.idl E g 2 (-ν)) := fun z => by
    have h := mem_idl_shift E g hg 0 (-ν) z
    rwa [zero_add] at h
  have hφ : (LinearMap.id - ((-1 : ℤ) ^ s) • S6.conjZ E : E →ₗ[ℤ] E) ((g : E) ^ 2 * y) =
      (g : E) ^ 2 * (LinearMap.id - ((-1 : ℤ) ^ s) • S6.conjZ E : E →ₗ[ℤ] E) y := by
    show (g : E) ^ 2 * y - ((-1 : ℤ) ^ s) • (IsCMField.complexConj E) ((g : E) ^ 2 * y) =
      (g : E) ^ 2 * (y - ((-1 : ℤ) ^ s) • (IsCMField.complexConj E) y)
    rw [map_mul, map_pow, map_natCast, zsmul_eq_mul, zsmul_eq_mul]
    ring
  unfold S6.liftLat S6.perLat S6.twLat
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap, hφ, h1, h2]
end Formalism.FourierDecayAlt.P.Jx12
