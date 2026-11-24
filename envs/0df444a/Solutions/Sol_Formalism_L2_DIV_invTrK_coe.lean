-- Prove2me | solution 1 for Formalism.L2.DIV.invTrK_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.571004+00:00
-- url     : https://prove2.me/submissions/3af5ebe8-c195-4b3f-a4c9-59c32b2295ce

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
theorem _root_.solution {K : Type} [Field K] {ι : Type} {n : ℕ} (g : ι → GL (Fin n) K) (τ : ι) :
    ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := rfl
end Formalism.L2.DIV
