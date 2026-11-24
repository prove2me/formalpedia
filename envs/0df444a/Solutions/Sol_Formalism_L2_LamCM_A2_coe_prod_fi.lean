-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.coe_prod_fi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:48.364064+00:00
-- url     : https://prove2.me/submissions/c40451dd-557d-48a8-a874-dfe080ed6356

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ j ∈ s, I j : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ j ∈ s, (I j : Submodule (𝓞 K) K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FractionalIdeal.coe_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coe_mul, ih]
end Formalism.L2.LamCM.A2
