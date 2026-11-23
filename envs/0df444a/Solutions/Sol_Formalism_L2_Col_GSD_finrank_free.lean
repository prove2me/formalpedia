-- Prove2me | solution 1 for Formalism.L2.Col.GSD.finrank_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:56.262904+00:00
-- url     : https://prove2.me/submissions/9ef2943e-cad7-4f4b-b03a-2b19037694b0

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
theorem _root_.solution (h : S.Ok) (hf : S.Free) : finrank K S.EqFun = Nat.card S.Cl * finrank K S.V := by
  letI := h.fintypeCl
  haveI : Module.Finite K S.V := Module.Finite.of_basis S.bV
  rw [(S.resFree h S.outSec hf).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Nat.card_eq_fintype_card]
end Formalism.L2.Col.GSD
