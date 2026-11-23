-- Prove2me | solution 1 for Formalism.L2.Col.GSD.restr_card_stab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:37.988645+00:00
-- url     : https://prove2.me/submissions/50336d65-8380-4f6b-9511-7c37eca7cf28

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
theorem _root_.solution (T : SubMulAction S.G S.D) (t : T) :
    Nat.card (MulAction.stabilizer (S.restr T).G (show (S.restr T).D from t)) =
      Nat.card (MulAction.stabilizer S.G (t : S.D)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
end Formalism.L2.Col.GSD
