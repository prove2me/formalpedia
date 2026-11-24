-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_X_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:54:15.052819+00:00
-- url     : https://prove2.me/submissions/1174470b-9386-44e8-92f5-27fb38b08400

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockL_symm
import Theorems.Thm_Formalism_L2_DIV_fockL_pderiv_X

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
theorem _root_.solution {σ : Type} [DecidableEq σ] (v : σ) (f g : MvPolynomial σ K) :
    fockL (X v * f) g = fockL f (pderiv v g) := by
  rw [fockL_symm, ← fockL_pderiv_X, ← fockL_symm]
end Formalism.L2.DIV
