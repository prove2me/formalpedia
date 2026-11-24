-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.ffl_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:25:00.667573+00:00
-- url     : https://prove2.me/submissions/e69cb2ce-64e5-424b-91b1-b65eddbfc77b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (s : ℂ) {i : Fin (r + 1)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' i D) : (fun g => s • J g) ∈ FFl k r z z' π π' i D := by
  obtain ⟨hS, hL, hR, hπ⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hS _ hg₀
    exact ⟨U, fun g => s • F g, hU, hgU, hF.const_smul s, fun g hg hgG => by
      show s • J g = s • F g
      rw [hJF g hg hgG]⟩
  · intro g hg n hn
    show s • J (n * g) = _ • s • J g
    rw [hL g hg n hn, smul_comm]
  · intro g hg n hn
    show s • J (g * n) = _ • s • J g
    rw [hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show s • J (h * g * h') = (π h).comp ((s • J g).comp (π' h'))
    rw [hπ g hg h hh h' hh']
    ext v
    simp
end Formalism.FourierDecayAlt.P.Qx3
