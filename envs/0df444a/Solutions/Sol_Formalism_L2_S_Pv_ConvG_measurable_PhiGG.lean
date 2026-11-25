-- Prove2me | solution 1 for Formalism.L2.S.Pv.ConvG.measurable_PhiGG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:46.201514+00:00
-- url     : https://prove2.me/submissions/68280047-9a42-4f16-ba6b-b617d8726a15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG

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
open scoped InnerProductSpace ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.ConvG
open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']
namespace Formalism.L2.S.Pv.ConvG
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : G × G => PhiGG σ w W W' γ p.1 p.2) := by
  unfold PhiGG
  have h1 : Continuous (fun p : G × G => ⟪σ p.1 w, σ γ (σ p.2 w)⟫_ℂ) :=
    Continuous.inner (𝕜 := ℂ) ((hσ.2.2.2 w).comp continuous_fst)
      ((σ γ).continuous.comp ((hσ.2.2.2 w).comp continuous_snd))
  exact ((h1.enorm.measurable).mul ((hW.comp continuous_fst).enorm.measurable)).mul
    ((hW'.comp continuous_snd).enorm.measurable)
end Formalism.L2.S.Pv.ConvG
