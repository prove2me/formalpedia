-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.top_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:11:56.369978+00:00
-- url     : https://prove2.me/submissions/572d9945-8ec6-4df9-a780-da18e3439b6e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {O : Set (Mat k r)} (hO : IsOpen O) {L : List (ℂ × List (Mat k r))} {j N : ℕ} (hL : WOK L j)
    (hjN : j + 1 ≤ N) (op : (Mat k r → E) → (Mat k r → E))
    (hop : ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r → op f g = wsum L f g)
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn (N : ℕ∞) (O ∩ GV k r) f)
    (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    Top (Q.EH k r) u c d (op f) g = wsum (stepL k r u c d L) f g := by
  have hf' : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf'', he⟩ := hf g₀ hg₀
    exact ⟨U, f', hU, hgU, hf''.of_le (WithTop.coe_le_coe.2 (by exact_mod_cast hjN)), he⟩
  have hcong : ∀ Y, inLie k r Y → RdV Y (op f) g = RdV Y (wsum L f) g := by
    intro Y hY
    have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g Y 0
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by simp
    have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • Y) ∈ O :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hgO)
    show deriv (fun t : ℝ => op f (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y))) 0
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hmem] with t ht
    exact hop f hf _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hY t)
  have hder : ∀ Y, inLie k r Y → RdV Y (wsum L f) g = wsum (L.map fun cw => (cw.1, Y :: cw.2)) f g := by
    intro Y hY
    have h := wsum_hasDeriv (O := O) hL hf' hY hgO hgG
    have hcrv : (fun t : ℝ => wsum L f (crv (false, Y) g t)) =
        fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y)) := by
      funext t
      simp [crv]
    rw [hcrv] at h
    exact h.deriv
  show (if c = d then u • op f g else 0) + Q.EH k r c d (op f) g = wsum (stepL k r u c d L) f g
  have hEH : Q.EH k r c d (op f) g =
      RdV (Xa k r c d) (op f) g + Complex.I • RdV (Xb k r c d) (op f) g := rfl
  rw [hEH, hcong _ (Xa_lie c d), hcong _ (Xb_lie c d), hder _ (Xa_lie c d), hder _ (Xb_lie c d),
    hop f hf g hgO hgG]
  simp only [stepL, wsum_append, wsum_scale]
  split_ifs with hcd
  · rw [wsum_scale]
  · rw [wsum_nil]
end Formalism.FourierDecayAlt.P.JFxB
