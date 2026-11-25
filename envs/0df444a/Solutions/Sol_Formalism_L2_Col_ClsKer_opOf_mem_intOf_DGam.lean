-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.opOf_mem_intOf_DGam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:49.996866+00:00
-- url     : https://prove2.me/submissions/a71081ba-57d4-437f-adc3-bae5cf733672

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_ClsKer_opOf_mem_intOf

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
namespace Formalism.L2.Col
namespace ClsKer
theorem _root_.solution {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (φ : S.EqFun) (hφ : φ ∈ S.intOf N) :
    ((S.toCSDOf h s).DGam : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by
  letI := h.fintypeCl
  exact A.opOf_mem_intOf h s N N' hk _ (fun c => by unfold CSD.DGam; exact Finset.dvd_lcm (Finset.mem_univ c)) φ hφ
end ClsKer
end Formalism.L2.Col
