-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fejer.wt_succ_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:45.10084+00:00
-- url     : https://prove2.me/submissions/a2b32552-9fb2-4757-85df-98a06cde4d92

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FacSuccOfNotMem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fejer_fac_succ_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fejer
open Real Finset Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Fejer
theorem _root_.solution (N : ℕ) (τ : Fin d → ℤ)
    (hτ : τ ∉ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)) :
    wt (N + 1) τ = 0 := by
  rw [Fintype.mem_piFinset] at hτ
  simp only [not_forall] at hτ
  obtain ⟨j, hj⟩ := hτ
  unfold wt
  exact Finset.prod_eq_zero (Finset.mem_univ j) (fac_succ_of_not_mem N (τ j) hj)
end Formalism.FourierDecayAlt.P.Fejer
