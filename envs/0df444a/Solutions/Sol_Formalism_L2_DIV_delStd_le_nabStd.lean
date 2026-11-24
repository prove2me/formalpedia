-- Prove2me | solution 1 for Formalism.L2.DIV.delStd_le_nabStd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:14.427201+00:00
-- url     : https://prove2.me/submissions/4ede959e-0e84-4fb5-8372-8762e259e77b

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_natW_antitone
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual


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
theorem _root_.solution (K : Type) [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    delStd K lam ≤ nabStd K lam := by
  refine Submodule.span_mono ?_
  rintro P ⟨F, hF, rfl⟩
  exact ⟨F, fun τ => Submodule.map_mono (Formalism.GradedWeylDivisibility.weylLeDual (𝓞 K) n n le_rfl _ (natW_antitone (lam τ))) (hF τ), rfl⟩
end Formalism.L2.DIV
