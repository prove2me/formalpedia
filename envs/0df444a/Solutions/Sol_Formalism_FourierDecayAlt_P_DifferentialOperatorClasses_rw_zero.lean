-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.rw_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:48.920458+00:00
-- url     : https://prove2.me/submissions/6461bcfd-4bc7-42e4-a21a-eb2a9e10c06e

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_gf_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ v : List (B.Mat k r), (∀ X ∈ v, B.inLie k r X) →
      ∀ g ∈ B.GV k r, Gf k r D.z D.z' g < ε → B.Rw v G g = 0 := by
  intro v
  induction v with
  | nil =>
    intro _ g hg hlt
    by_contra h
    exact absurd (hG g hg h) (not_le.2 hlt)
  | cons X v ih =>
    intro hv g hg hlt
    have hX : B.inLie k r X := hv X (by simp)
    have hv' : ∀ Y ∈ v, B.inLie k r Y := fun Y hY => hv Y (by simp [hY])
    simp only [B.Rw, List.foldr_cons]
    show deriv (fun t : ℝ => List.foldr RdV G v (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0
    have hc : Continuous fun t : ℝ => Gf k r D.z D.z' (g * NormedSpace.exp ((t : ℂ) • X)) :=
      (gf_cont k r D.z D.z').comp (B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => Gf k r D.z D.z' (g * NormedSpace.exp ((t : ℂ) • X))) 0 < ε := by
      show Gf k r D.z D.z' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) < ε
      rw [B5.curve_zero]; exact hlt
    have hev := (hc.tendsto 0).eventually (gt_mem_nhds h0)
    have : (fun t : ℝ => List.foldr RdV G v (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 :=
      hev.mono fun t ht => ih hv' _ (B5.curve_mem hg hX t) ht
    rw [this.deriv_eq, deriv_const]
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
