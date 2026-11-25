-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Fk_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:21.652818+00:00
-- url     : https://prove2.me/submissions/500f53f9-bc52-4139-b7aa-37cab368139b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integral_norm_sq_eq_one
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integral_inner_mul_inner_eq_norm_sq_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {μS ν : Measure G} [SFinite μS] [SFinite ν] (hq : IsQuot μ μS ν)
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W)
    (hΦ : Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    ∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) = ((1 / d : ℝ) : ℂ) := by
  have hWc : Continuous W := hW.2.2.2.2.1
  have hL2 := hW.2.2.2.2.2.2.2
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hmap : μ = Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μS) := by
    ext s hs
    rw [Measure.map_apply hm hs, ← lintegral_indicator_one hs, hq _ (measurable_one.indicator hs),
      ← lintegral_indicator_one (hm hs),
      lintegral_prod _ ((measurable_one.indicator (hm hs)).aemeasurable)]
    first
      | rfl
      | (simp only [Set.indicator_apply, Set.mem_preimage]; rfl)
  have hinner : ∀ z, ∫ y, Fk σ w W z y.1 y.2 ∂(ν.prod μS) = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
    intro z
    have hg := integral_inner_mul_inner_eq_norm_sq_div hσ hd hW z
    have hgc : Continuous (fun x : G => ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ) :=
      (hWc.inner continuous_const).mul (continuous_const.inner (hσ.2.2.2 w))
    rw [hmap, integral_map hm.aemeasurable hgc.aestronglyMeasurable] at hg
    exact hg
  rw [integral_prod _ hΦ]
  refine (integral_congr_ae (ae_of_all _ fun z => hinner z)).trans ?_
  first
    | rw [integral_complex_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]
    | rw [integral_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]
end Formalism.L2.S.Pv.EnergyAbs
