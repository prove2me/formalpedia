-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.lin_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:23.768029+00:00
-- url     : https://prove2.me/submissions/dd11f27e-c253-485c-b763-7d53025964c9

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
variable (R)
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') (k : ℕ)
    (h : ∀ v, ∃ v', LiftRel R k Z Z' φ v v') :
    ∃ F : (Fin n → R) →ₗ[R] (Fin n → R), ∀ v, LiftRel R k Z Z' φ v (F v) := by
  let Γ := liftSub R k Z Z' φ
  let f : Γ →ₗ[R] (Fin n → R) := (LinearMap.fst R _ _).comp Γ.subtype
  have hf : Function.Surjective f := fun v => by
    obtain ⟨v', h'⟩ := h v
    exact ⟨⟨(v, v'), h'⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨(LinearMap.snd R _ _).comp (Γ.subtype.comp s), fun v => ?_⟩
  have h1 : ((s v : Γ) : (Fin n → R) × (Fin n → R)).1 = v := LinearMap.congr_fun hs v
  have h2 : LiftRel R k Z Z' φ ((s v : Γ) : (Fin n → R) × (Fin n → R)).1
      ((s v : Γ) : (Fin n → R) × (Fin n → R)).2 := (s v).2
  rw [h1] at h2
  exact h2
end Formalism.FourierDecayAlt.P.A5x2
