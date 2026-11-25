-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.fY_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:47.674319+00:00
-- url     : https://prove2.me/submissions/3543b6c2-8258-443f-98f0-98aba52a283e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv

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
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p = fY σ w W e p := by
  simp only [fY]
  simp_rw [smul_smul, ← Finset.sum_smul]
  congr 1
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W (p.2⁻¹ * p.1)) e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.L2.S.Pv.EnergyAbs
