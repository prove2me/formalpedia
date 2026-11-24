-- Prove2me | solution 1 for Formalism.L2.DIV.pairK_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:23.936442+00:00
-- url     : https://prove2.me/submissions/4fe653f7-1fbf-4a0a-b04d-304683f7ae23

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
    (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) : pairK lam G x y = pairP lam G x.1 y.1 :=
  LinearMap.domRestrict₁₂_apply _ _ _ x y
end Formalism.L2.DIV
