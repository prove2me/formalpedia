-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:22:07.136502+00:00
-- url     : https://prove2.me/submissions/98375712-1964-4cb8-ba3e-29b33a270d03

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
variable (S : HermForm K r)
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution {κ : Type} (s : Finset κ) (x : κ → Fin r → K) (y : Fin r → K) :
    S.h (∑ j ∈ s, x j) y = ∑ j ∈ s, S.h (x j) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => S.h x y) (fun a b => h_add_left S a b y)) x s
end Formalism.L2.Pj.FundamentalDomainD5
