-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_monomial_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:50.644672+00:00
-- url     : https://prove2.me/submissions/0e09410d-a3b1-42f2-9072-646d6dc7ac5a

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockL_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution {σ : Type} (u : σ →₀ ℕ) (c : K) (g : MvPolynomial σ K) :
    fockL (monomial u c) g = star c * g.coeff u * (mfact u : K) := by
  classical
  rw [fockL_apply, fockS_eq_sum _ _ {u} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]
end Formalism.L2.DIV
