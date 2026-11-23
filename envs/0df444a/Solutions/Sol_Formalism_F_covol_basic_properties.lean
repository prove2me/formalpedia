-- Prove2me | solution 1 for Formalism.F.covol_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:13.976393+00:00
-- url     : https://prove2.me/submissions/7c9505c0-003b-43af-956e-bfbc6d1ee191

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Theorems.Thm_Formalism_F_discreteTopology_span_singleton
import Theorems.Thm_Formalism_F_covol_eq_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : CovolBasic := by
  intro E _ _ _
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance
    rw [covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]
    simp [Matrix.det_isEmpty]
  · intro v hv
    haveI := discreteTopology_span_singleton hv
    have hli : LinearIndependent ℤ (fun _ : Unit => v) := by
      have hR : LinearIndependent ℝ (fun _ : Unit => v) := by
        rw [linearIndependent_unique_iff]
        first
          | exact hv
          | (intro r hr; exact (smul_eq_zero.1 hr).resolve_right hv)
      first
        | exact hR.restrict_scalars' ℤ
        | exact hR.restrict_scalars (by intro a c h; simpa using h)
    have hr : span ℤ (Set.range fun _ : Unit => v) = span ℤ ({v} : Set E) := by
      rw [Set.range_const]
    let b : Basis Unit ℤ (span ℤ ({v} : Set E)) := (Basis.span hli).map (LinearEquiv.ofEq _ _ hr)
    have hb : (fun i => (b i : E)) = fun _ => v := by
      funext i
      simp [b, Basis.span_apply]
    rw [covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
end Formalism.F
