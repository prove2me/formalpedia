-- Prove2me | solution 1 for Formalism.L2.Col.GSD.mem_intOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:08.18382+00:00
-- url     : https://prove2.me/submissions/64bc7c77-5f35-4153-8340-ec7ae3700a2d

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
theorem _root_.solution (N : S.D → Submodule (𝓞 K) S.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K))) (s : S.Sec)
    (φ : S.EqFun) : φ ∈ S.intOf N ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ N (s.rep c) := by
  constructor
  · intro hφ c
    exact hφ (s.rep c)
  · intro hφ d
    have e := s.mv_smul d
    rw [← e, φ.2, hN]
    exact Submodule.mem_map_of_mem (hφ (S.cls d))
end Formalism.L2.Col.GSD
