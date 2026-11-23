-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.prod_roots_unity_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:00.87792+00:00
-- url     : https://prove2.me/submissions/fe1f7957-1366-490e-bef0-cec55b1b3cdc

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mem_mu_iff_pow_eq_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_mem_units_of_mem_mu
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_injOn_mu
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_surjOn_mu_nonzero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_wilson_zmod_prod_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hl : l ≠ 2) : ∏ d ∈ mu l, d = -1 := by
  have hp : ∏ d ∈ mu l, d ∈ mu l := (mem_mu_iff_pow_eq_one l).mpr (by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun d hd => (mem_mu_iff_pow_eq_one l).mp hd)
  have hm1 : (-1 : ℤ_[l]) ∈ mu l :=
    (mem_mu_iff_pow_eq_one l).mpr ((Fact.out : l.Prime).even_sub_one hl).neg_one_pow
  apply toZMod_injOn_mu l hp hm1
  rw [map_prod, map_neg, map_one, ← wilson_zmod_prod_units l]
  exact Finset.prod_nbij _ (toZMod_mem_units_of_mem_mu l) (toZMod_injOn_mu l) (toZMod_surjOn_mu_nonzero l) (fun _ _ => rfl)
end Formalism.CohomologicalDescent.HeightDescentMinors
