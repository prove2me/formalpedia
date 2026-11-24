-- Prove2me | solution 1 for Formalism.L2.Col.GSD.map_intNab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:18.223857+00:00
-- url     : https://prove2.me/submissions/9cb96c23-a84f-4cdd-85a9-30fb81e8fbeb

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_coordOf_mem_nabLat

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
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) :
    S.intNab.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).nabLat := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    exact (S.coordOf_mem_nabLat h s φ).mpr hφ
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.coordOf h s).symm x, ?_, ?_⟩
    · rw [← S.coordOf_mem_nabLat h s, LinearEquiv.apply_symm_apply]
      exact hx
    · simp
end Formalism.L2.Col.GSD
