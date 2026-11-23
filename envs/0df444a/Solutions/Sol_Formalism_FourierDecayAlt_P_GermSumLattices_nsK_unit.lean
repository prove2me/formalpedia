-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.nsK_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:46.117372+00:00
-- url     : https://prove2.me/submissions/5ef30d2b-437a-414d-a708-c13f6eb2f784

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_tri_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (hMM : MM R) (h h' : Point K) (z : Kˣ) :
    NsK R ψ (m + 1) h h' (z : K) = ((modK R (z : K) ^ (m ^ 2 + m) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) z) := by
  unfold NsK
  rw [dif_pos z.isUnit, IsUnit.unit_of_val_units]
  unfold Ns
  rw [(hMM z z).2, Nat.add_sub_cancel, mul_comm (m + 1) m, tri_pow]
end Formalism.FourierDecayAlt.P.GermSumLattices
