-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.gvec_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:42.681806+00:00
-- url     : https://prove2.me/submissions/924fa29a-7dc6-4f1d-afe6-683cb680dad8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
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
theorem _root_.solution (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x y : G) :
    ⟪gvec σ w W x, gvec σ w W y⟫_ℂ = ⟪W y, W x⟫_ℂ * ⟪σ x w, σ y w⟫_ℂ := by
  have hb : ∑ i, ⟪W y, stdOrthonormalBasis ℂ V i⟫_ℂ * ⟪stdOrthonormalBasis ℂ V i, W x⟫_ℂ = ⟪W y, W x⟫_ℂ := by
    exact (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W y) (W x)
  rw [← hb, Finset.sum_mul]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gvec, PiLp.toLp_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring
end Formalism.L2.S.Pv.EnergyAbs
