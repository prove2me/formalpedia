-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.wsum_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:17.225867+00:00
-- url     : https://prove2.me/submissions/074b2b7c-6b55-445f-8208-d096c140f88a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_ckOn_Rw_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {O : Set (Mat k r)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j)
    {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => wsum L f (crv (false, X) g t)) (wsum (L.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by
  have hgU : g ∈ O ∩ GV k r := ⟨hgO, hgG⟩
  have hword : ∀ cw ∈ L, HasDerivAt (fun t : ℝ => Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)))
      (Rw (X :: cw.2) f g) 0 := by
    intro cw hcw
    obtain ⟨h1, h2⟩ := hL cw hcw
    obtain ⟨U, f', hU, hgU', hf', he⟩ := ckOn_Rw_loc h1 (by omega) hf g hgU
    have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU')
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)) = f' (g * NormedSpace.exp ((t : ℂ) • X)) := by
      filter_upwards [hmem] with t ht
      exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    have hf'd : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
      rw [hγ0]
      exact (hf'.contDiffAt (hU.mem_nhds hgU')).differentiableAt (by simp)
    exact ((hf'd.comp (0 : ℝ) hγ.differentiableAt).congr_of_eventuallyEq hev).hasDerivAt
  have key : ∀ L' : List (ℂ × List (Mat k r)), (∀ cw ∈ L', cw ∈ L) →
      HasDerivAt (fun t : ℝ => wsum L' f (g * NormedSpace.exp ((t : ℂ) • X)))
        (wsum (L'.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by
    intro L'
    induction L' with
    | nil => intro _; simpa [wsum] using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons cw L' ih =>
      intro hsub
      simp only [List.map_cons, wsum_cons]
      exact ((hword cw (hsub cw (by simp))).const_smul cw.1).add (ih (fun c hc => hsub c (by simp [hc])))
  have hcrv : ∀ t : ℝ, crv (false, X) g t = g * NormedSpace.exp ((t : ℂ) • X) := fun t => by simp [crv]
  simp only [hcrv]
  exact key L (fun _ h => h)
end Formalism.FourierDecayAlt.P.JFxB
