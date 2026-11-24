-- Prove2me | solution 1 for Formalism.L2.DIV.embGL_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:00.448348+00:00
-- url     : https://prove2.me/submissions/53cd55fa-62f2-4129-8240-eeb61411d4c5

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas

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
namespace Formalism.L2.DIV
theorem _root_.solution {E K : Type} [Field E] [Field K] {ι : Type} {n : ℕ} (emb : ι → E →+* K) (γ : GL (Fin n) E) (τ : ι) :
    ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γ : Matrix (Fin n) (Fin n) E).map (emb τ) := rfl
end Formalism.L2.DIV
