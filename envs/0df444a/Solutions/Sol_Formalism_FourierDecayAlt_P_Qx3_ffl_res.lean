-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.ffl_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:22.014018+00:00
-- url     : https://prove2.me/submissions/89001c02-0844-40f1-a5aa-6d458edb10e5

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_nlev_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_uw_glev

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
theorem _root_.solution {j i : Fin (r + 1)} (hji : j ≤ i) {w₀ : Mx k r} (hw : w₀ ∈ Glev k r j)
    (hcomm : ∀ g ∈ Glev k r i, w₀ * g = g * w₀) {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' j D) :
    (fun g => J (w₀ * g)) ∈ FFl k r z z' π π' i {g | w₀ * g ∈ D} := by
  obtain ⟨hS, hL, hR, hπ⟩ := hJ
  have hmem : ∀ g ∈ Glev k r i ∩ {g | w₀ * g ∈ D}, w₀ * g ∈ Glev k r j ∩ D :=
    fun g hg => ⟨glev_mul hw (glev_mono hji hg.1), hg.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hS _ (hmem g₀ hg₀)
    exact ⟨{g | w₀ * g ∈ U}, fun g => F (w₀ * g), hU.preimage (mulLeftL w₀).continuous, hgU,
      hF.comp (mulLeftL w₀).contDiff.contDiffOn (fun _ h => h),
      fun g hg hgG => hJF _ hg (glev_mul hw (glev_mono hji hgG))⟩
  · intro g hg n hn
    show J (w₀ * (n * g)) = _ • J (w₀ * g)
    rw [← Matrix.mul_assoc, hcomm n hn.2, Matrix.mul_assoc]
    exact hL _ (hmem g hg) n (nlev_mono hji hn)
  · intro g hg n hn
    show J (w₀ * (g * n)) = _ • J (w₀ * g)
    rw [← Matrix.mul_assoc]
    exact hR _ (hmem g hg) n (nlev_mono hji hn)
  · intro g hg h hh h' hh'
    show J (w₀ * (h * g * h')) = _
    have e : w₀ * (h * g * h') = h * (w₀ * g) * h' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm h (uw_glev i hh), Matrix.mul_assoc h w₀ g]
    rw [e]
    exact hπ _ (hmem g hg) h hh h' hh'
end Formalism.FourierDecayAlt.P.Qx3
