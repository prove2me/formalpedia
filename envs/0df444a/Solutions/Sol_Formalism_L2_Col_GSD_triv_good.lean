-- Prove2me | solution 1 for Formalism.L2.Col.GSD.triv_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:47.246675+00:00
-- url     : https://prove2.me/submissions/7fe0cf81-5513-4c4c-ae2d-f067dd48cf39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Theorems.Thm_Formalism_L2_Col_GSD_triv_ok
import Theorems.Thm_Formalism_L2_DIV_CSD_one_good


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
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K) (G D : Type) [Group G] [MulAction G D]
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h1 : Finite (MulAction.orbitRel.Quotient G D))
    (h2 : ∀ d : D, Finite (MulAction.stabilizer G d)) : (triv K G D).Good 1 where
  ok := triv_ok K G D h1 h2
  symm := (CSD.one_good K).symm
  nondeg := (CSD.one_good K).nondeg
  nab_lat := fun _ => (CSD.one_good K).nab_lat ()
  del_le := fun _ => le_rfl
  s_pos := Nat.one_pos
  dual_le := fun _ => (CSD.one_good K).dual_le ()
  del_dual := fun _ => (CSD.one_good K).del_dual ()
end Formalism.L2.Col.GSD
