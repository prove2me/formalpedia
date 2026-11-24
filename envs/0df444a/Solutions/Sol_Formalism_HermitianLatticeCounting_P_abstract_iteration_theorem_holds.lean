-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.abstract_iteration_theorem_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:47.118849+00:00
-- url     : https://prove2.me/submissions/6f060c8c-e72e-46e3-9668-b3a85dc32bfc

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_iterate_sum_lower_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_filtered_iterate_norm_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.SuperharmonicMomentBound := by
  intro Ω W ι _ _ ν Eop Ph κ Nw Fil c hm hI hk hF hN q j w hw
  calc ∫⁻ g, κ g ^ q * Ph w g ∂ν
      ≤ ∫⁻ g, ∑ σ : Fin q → ι, Ph ((List.ofFn σ).foldr Eop w) g ∂ν :=
        lintegral_mono fun g => iterate_sum_lower_bound Eop (fun w => Ph w g) (κ g) zero_le (fun w => hk w g) q w
    _ = ∑ σ : Fin q → ι, Nw ((List.ofFn σ).foldr Eop w) := by
        rw [lintegral_finsetSum _ (fun σ _ => hm _)]
        exact Finset.sum_congr rfl fun σ _ => hI _
    _ ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w :=
        filtered_iterate_norm_bound Eop Nw Fil c (fun _ => zero_le) hF hN q j w hw
end Formalism.HermitianLatticeCounting.P
