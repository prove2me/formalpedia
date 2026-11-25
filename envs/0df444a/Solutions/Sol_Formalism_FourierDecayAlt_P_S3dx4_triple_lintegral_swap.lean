-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.triple_lintegral_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:44:21.401731+00:00
-- url     : https://prove2.me/submissions/c5159a9c-dd4e-41cf-81c0-4499beec034c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_triple_integrand_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    [SFinite μG] [SFinite μp] [SFinite μq] :
    ∫⁻ x, ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp ∂μG =
      ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γi x p q ∂μG ∂μq ∂μp := by
  have h1 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq) := by
    have hm := triple_integrand_measurable he1 he2 γi
      (α := (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
      (X := fun z => z.1.1) (Pp := fun z => z.1.2) (Qq := fun z => z.2)
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd
    exact hm.lintegral_prod_right'
  rw [lintegral_lintegral_swap h1.aemeasurable]
  refine lintegral_congr fun p => ?_
  have h2 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Phi3 e1 e2 γi x p q) :=
    triple_integrand_measurable he1 he2 γi (X := fun z : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => z.1)
      (Pp := fun _ => p) (Qq := fun z => z.2) continuous_fst continuous_const continuous_snd
  exact lintegral_lintegral_swap h2.aemeasurable
end Formalism.FourierDecayAlt.P.S3dx4
