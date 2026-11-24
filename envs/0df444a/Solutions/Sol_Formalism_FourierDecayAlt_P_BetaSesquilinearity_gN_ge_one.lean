-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:56:45.126317+00:00
-- url     : https://prove2.me/submissions/8a47ce8d-f05c-472a-b356-2ede1b9cb77d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_eq_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH0 : Hpk k r ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun h0 ⟨r, by omega⟩) ⟨r, by omega⟩
    clear h0 hg' hg
    simp [Hpk] at h1 <;> split_ifs at h1 <;> norm_num at h1
  have hn : 0 < ‖Hpk k r‖ := norm_pos_iff.mpr hH0
  have h2 : ‖Hpk k r‖ ≤ ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by
    calc ‖Hpk k r‖ = ‖gᴴ * Hpk k r * g‖ := by rw [hg']
      _ ≤ ‖gᴴ * Hpk k r‖ * ‖g‖ := norm_mul_le _ _
      _ ≤ ‖gᴴ‖ * ‖Hpk k r‖ * ‖g‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by rw [Matrix.frobenius_norm_conjTranspose]
  rw [gN_eq_frob]
  by_contra hlt
  push_neg at hlt
  have h3 : ‖g‖ * ‖g‖ < 1 := by nlinarith [norm_nonneg g]
  nlinarith [mul_pos (sub_pos.mpr h3) hn]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
