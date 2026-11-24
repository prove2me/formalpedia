-- Prove2me | solution 1 for Formalism.L2.Col.GSD.csOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:24.579642+00:00
-- url     : https://prove2.me/submissions/6c2ccdcc-c6bf-4456-93f6-0f63266db6f2

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_wt_eq
import Theorems.Thm_Formalism_L2_Col_GSD_card_stab_smul
import Theorems.Thm_Formalism_L2_Col_GSD_Sec_exists_smul

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
theorem _root_.solution (h : S.Ok) (s s' : S.Sec) {M : Type} [AddCommGroup M] [Module K M] (F : S.D → M)
    (hF : ∀ (g : S.G) (d : S.D), F (g • d) = F d) : S.csOf h s F = S.csOf h s' F := by
  unfold csOf
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := Sec.exists_smul s s' c
  rw [S.wt_eq h s c, S.wt_eq h s' c, ← hg, S.card_stab_smul, hF]
end Formalism.L2.Col.GSD
