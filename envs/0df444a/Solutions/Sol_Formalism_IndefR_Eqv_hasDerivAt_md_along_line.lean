-- Prove2me | solution 1 for Formalism.IndefR.Eqv.hasDerivAt_md_along_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:16.011461+00:00
-- url     : https://prove2.me/submissions/6f998eff-a511-4d61-9698-daa76ccb6bdf

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) : ∀ (n : ℕ) (v : Fin n → V) (h : ℝ) (a w : V),
    HasDerivAt (fun s : ℝ => md φ n v h (a + s • w)) (md (fun y => fderiv ℝ φ y w) n v h a) 0
  | 0, v, h, a, w => by
    simp only [md]
    have h1 : HasDerivAt (fun s : ℝ => a + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
    exact ((hφ.differentiable (by simp)) a).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  | n + 1, v, h, a, w => by
    simp only [md]
    have e1 : ∀ s : ℝ, a + s • w + h • v 0 = (a + h • v 0) + s • w := fun s => by abel
    have h1 := solution hφ n (Fin.tail v) h (a + h • v 0) w
    have h2 := solution hφ n (Fin.tail v) h a w
    simp_rw [e1]
    exact (h1.sub h2).div_const h
end Formalism.IndefR.Eqv
