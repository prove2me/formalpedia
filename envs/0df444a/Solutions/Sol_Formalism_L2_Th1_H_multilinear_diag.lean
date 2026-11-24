-- Prove2me | solution 1 for Formalism.L2.Th1.H.multilinear_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:24.269804+00:00
-- url     : https://prove2.me/submissions/a4314d95-c83f-4911-8633-918eb4f684b0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin k => n → ℂ) ℂ) (v : n → ℂ) :
    D (fun _ => v) = ∑ f : Fin k → n, (∏ j, v (f j)) * D fun j => Pi.single (f j) (1 : ℂ) := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℂ) : n → ℂ) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : D (fun _ => v) = D (fun _ : Fin k => ∑ i, v i • (Pi.single i (1 : ℂ) : n → ℂ)) := by
    rw [← hv]
  rw [h1, D.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [D.map_smul_univ (fun j => v (f j)) (fun j => Pi.single (f j) (1 : ℂ)), smul_eq_mul]
end Formalism.L2.Th1.H
