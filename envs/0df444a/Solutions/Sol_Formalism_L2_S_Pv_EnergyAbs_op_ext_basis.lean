-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.op_ext_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:50.863545+00:00
-- url     : https://prove2.me/submissions/82d5e74c-33d3-42cf-98e3-23540ae4d5db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc

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
theorem _root_.solution (X Z : V' →L[ℂ] V)
    (h : ∀ i j, ⟪stdOrthonormalBasis ℂ V i, X (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
      ⟪stdOrthonormalBasis ℂ V i, Z (stdOrthonormalBasis ℂ V' j)⟫_ℂ) : X = Z := by
  have hcol : ∀ j, X (stdOrthonormalBasis ℂ V' j) = Z (stdOrthonormalBasis ℂ V' j) := by
    intro j
    first
    | exact ext_inner_left_basis (stdOrthonormalBasis ℂ V).toBasis (fun i => by simpa using h i j)
    | (apply (stdOrthonormalBasis ℂ V).repr.injective
       ext i
       simpa [OrthonormalBasis.repr_apply_apply] using h i j)
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ V').toBasis.ext (fun j => by simpa using hcol j)
end Formalism.L2.S.Pv.EnergyAbs
