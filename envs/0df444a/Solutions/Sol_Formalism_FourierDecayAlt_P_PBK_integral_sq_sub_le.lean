-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.integral_sq_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:03:16.536595+00:00
-- url     : https://prove2.me/submissions/fe30c2c9-ed70-4984-894f-1fc60a3a2518

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).1).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.1).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]
end Formalism.FourierDecayAlt.P.PBK
