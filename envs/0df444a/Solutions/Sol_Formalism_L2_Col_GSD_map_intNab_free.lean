-- Prove2me | solution 1 for Formalism.L2.Col.GSD.map_intNab_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:30.387168+00:00
-- url     : https://prove2.me/submissions/2308b4c1-f099-49c9-809e-995c248e4f8a

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intNab_iff
import Theorems.Thm_Formalism_L2_Col_GSD_resFree_apply

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
theorem _root_.solution (h : S.Ok) (s : S.Sec) (hf : S.Free) :
    S.intNab.map ((S.resFree h s hf : S.EqFun →ₗ[K] (S.Cl → S.V)).restrictScalars (𝓞 K)) =
      Submodule.pi Set.univ fun c => S.Nab (s.rep c) := by
  ext f
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    rw [Submodule.mem_pi]
    intro c _
    exact hφ (s.rep c)
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.resFree h s hf).symm f, ?_, ?_⟩
    · rw [S.mem_intNab_iff h s]
      intro c
      rw [← S.resFree_apply h s hf, LinearEquiv.apply_symm_apply]
      exact (Submodule.mem_pi.mp hx) c (Set.mem_univ c)
    · simp
end Formalism.L2.Col.GSD
