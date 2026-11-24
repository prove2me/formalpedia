-- Prove2me | solution 1 for Formalism.L2.Col.GSD.card_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:21.135447+00:00
-- url     : https://prove2.me/submissions/2a299575-14f7-4094-b5be-48dcd3620742

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_card_stab_smul

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
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (s : (tv K).Sec) (d : Option ℤˣ) :
    Nat.card (MulAction.stabilizer ℤˣ (s.rep ((tv K).cls d))) = Nat.card (MulAction.stabilizer ℤˣ d) := by
  obtain ⟨g, hg⟩ := ((tv K).cls_eq_iff _ _).mp (s.spec ((tv K).cls d))
  rw [← hg]
  exact (tv K).card_stab_smul g d
end Formalism.L2.Col.GSD
