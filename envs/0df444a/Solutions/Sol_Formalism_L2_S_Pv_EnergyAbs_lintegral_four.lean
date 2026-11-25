-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.lintegral_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:03.366366+00:00
-- url     : https://prove2.me/submissions/9ffba2a6-c62e-4f20-974d-c5ed284f0ade

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (f : G → G → G → G → ℝ≥0∞) (hf : Measurable (fun q : G × G × G × G => f q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    ∫⁻ p, f p.1.1 p.2.1 p.1.2 p.2.2 ∂((ν.prod μS).prod (ν'.prod μS')) =
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', f z z' s s' ∂μS' ∂μS ∂ν' ∂ν := by
  have hm : Measurable (fun p : (G × G) × (G × G) => f p.1.1 p.2.1 p.1.2 p.2.2) := by
    have hg : Measurable (fun p : (G × G) × (G × G) => (p.1.1, p.2.1, p.1.2, p.2.2)) := by fun_prop
    exact hf.comp hg
  have h1 : Measurable fun x : G × G => ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS') :=
    hm.lintegral_prod_right'
  calc ∫⁻ p, f p.1.1 p.2.1 p.1.2 p.2.2 ∂((ν.prod μS).prod (ν'.prod μS'))
      = ∫⁻ x, ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS') ∂(ν.prod μS) :=
        lintegral_prod (fun p : (G × G) × (G × G) => f p.1.1 p.2.1 p.1.2 p.2.2) hm.aemeasurable
    _ = ∫⁻ z, ∫⁻ s, ∫⁻ y, f z y.1 s y.2 ∂(ν'.prod μS') ∂μS ∂ν :=
        lintegral_prod (fun x : G × G => ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS')) h1.aemeasurable
    _ = ∫⁻ z, ∫⁻ s, ∫⁻ z', ∫⁻ s', f z z' s s' ∂μS' ∂ν' ∂μS ∂ν := by
        refine lintegral_congr fun z => lintegral_congr fun s => ?_
        have hg : Measurable (fun y : G × G => (z, y.1, s, y.2)) := by fun_prop
        exact lintegral_prod (fun y : G × G => f z y.1 s y.2) (hf.comp hg).aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', f z z' s s' ∂μS' ∂μS ∂ν' ∂ν := by
        refine lintegral_congr fun z => ?_
        have hg : Measurable (fun p : (G × G) × G => (z, p.1.2, p.1.1, p.2)) := by fun_prop
        have hk : Measurable (fun p : (G × G) × G => f z p.1.2 p.1.1 p.2) := hf.comp hg
        have hk' : Measurable (fun x : G × G => ∫⁻ s', f z x.2 x.1 s' ∂μS') :=
          hk.lintegral_prod_right'
        exact lintegral_lintegral_swap (f := fun s z' => ∫⁻ s', f z z' s s' ∂μS') hk'.aemeasurable
end Formalism.L2.S.Pv.EnergyAbs
