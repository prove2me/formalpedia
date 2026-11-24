-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.h_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:22:08.326002+00:00
-- url     : https://prove2.me/submissions/f28cc6f2-36b4-444d-ae04-270cb7dba9d8

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_add_right

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
theorem _root_.solution {κ : Type} (s : Finset κ) (x : Fin r → K) (y : κ → Fin r → K) :
    S.h x (∑ j ∈ s, y j) = ∑ j ∈ s, S.h x (y j) := by
  exact map_sum (AddMonoidHom.mk' (fun y => S.h x y) (fun a b => h_add_right S x a b)) y s
end Formalism.L2.Pj.FundamentalDomainD5
