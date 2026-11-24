-- Prove2me | solution 1 for Formalism.REAL.prod_ofFn_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:56.676468+00:00
-- url     : https://prove2.me/submissions/5f612fec-0f67-4535-96d9-3275af8b42ab

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Theorems.Thm_Formalism_REAL_prod_ofFn_apply_of_eigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V) (j : Fin m),
      F j v = 0 → (∀ k, j < k → F k v = c k • v) → (List.ofFn F).prod v = 0 := by
  intro m
  induction m with
  | zero => intro F c v j; exact j.elim0
  | succ m ih =>
    intro F c v j hj hk
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    cases j using Fin.cases with
    | zero =>
      rw [prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v (fun i => hk i.succ (Fin.succ_pos i)),
        map_smul, hj, smul_zero]
    | succ j' =>
      rw [ih (fun i => F i.succ) (fun i => c i.succ) v j' hj
        (fun i hi => hk i.succ (Fin.succ_lt_succ_iff.mpr hi)), map_zero]
end Formalism.REAL
