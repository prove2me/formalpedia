-- Prove2me | solution 1 for Formalism.L2.DIV.pairP_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:20.926005+00:00
-- url     : https://prove2.me/submissions/64a77ccc-9e9d-4d16-9a7d-7c785b4d69fb

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
theorem _root_.solution {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    pairP lam G F F' = gramTw lam G / extNorm K lam * fockL F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) F') := rfl
end Formalism.L2.DIV
