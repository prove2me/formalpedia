-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.measurable_bInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:31.581318+00:00
-- url     : https://prove2.me/submissions/371447b9-38c9-4534-b475-193a1d9ea61f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_continuous_coef5

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun q : G × G × G × G => bInt σ w W W' γ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold bInt
  have h1 : Measurable fun q : G × G × G × G =>
      ‖⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ‖ₑ :=
    (continuous_enorm.comp (continuous_coef5 hσ w γ)).measurable
  have h2 : Measurable fun q : G × G × G × G => ‖W q.1‖ₑ :=
    (continuous_enorm.comp (hW.comp continuous_fst)).measurable
  have h3 : Measurable fun q : G × G × G × G => ‖W' q.2.1‖ₑ :=
    (continuous_enorm.comp (hW'.comp (continuous_fst.comp continuous_snd))).measurable
  exact (h1.mul h2).mul h3
end Formalism.L2.S.Pv.EnergyAbs
