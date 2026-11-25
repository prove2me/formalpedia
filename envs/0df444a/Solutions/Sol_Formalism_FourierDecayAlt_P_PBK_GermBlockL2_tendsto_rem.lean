-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.GermBlockL2.tendsto_rem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:54.74864+00:00
-- url     : https://prove2.me/submissions/378d0933-10a1-4634-828a-69982f069601

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_eventually_ne_cocompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_eventually_rate_cocompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_sq_sub_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_inner_germ


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
variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}
namespace Formalism.FourierDecayAlt.P.PBK
namespace GermBlockL2
theorem _root_.solution [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ] (hG : GermBlockL2 μ Y U A N)
    {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ τ : ℂ) :
    Tendsto (fun x => ∫ D, ⟪U (h, x + σ) D - A (h, x + σ) D, A (h', x + τ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨B, hB⟩ := hG.sup
  obtain ⟨ab, hab, hdom⟩ := hG.dom h' hh'
  obtain ⟨ab0, hab0, hdom0⟩ := hG.dom h hh
  refine tendsto_integral_inner_germ μ (fun x => fun D => U (h, x + σ) D - A (h, x + σ) D)
    (fun x => A (h', x + τ)) ab hab (2 * B + 2 * ∫ D, ab0 D ^ 2 ∂μ) ?_ ?_ ?_
  · filter_upwards [eventually_ne_cocompact (-σ)] with x hx
    have hx' : x + σ ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
    have hu := hG.memU h hh _ hx'
    have ha := hG.memA h hh _ hx'
    refine ⟨hu.sub ha, ?_⟩
    have h1 := integral_sq_sub_le hu ha hab0 (hdom0 _ hx')
    have hb := hB h hh _ hx'
    beta_reduce
    linarith
  · filter_upwards [eventually_ne_cocompact (-τ)] with x hx
    exact hdom _ (fun h0 => hx (eq_neg_of_add_eq_zero_left h0))
  · intro K hK hK0 δ hδ
    obtain ⟨C, hC⟩ := hG.germ h hh K hK hK0
    filter_upwards [eventually_ne_cocompact (-σ), eventually_rate_cocompact σ C δ hδ] with x hx hr
    have hx' : x + σ ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
    filter_upwards [hC _ hx'] with D hD hDK
    exact (hD hDK).trans hr
end GermBlockL2
end Formalism.FourierDecayAlt.P.PBK
