-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.rdV_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:26.68921+00:00
-- url     : https://prove2.me/submissions/d8e1feae-16f4-4af5-8083-23cd1a4b8e9b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hasDerivAt_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_rdV_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (hD : IsOpen D) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) (hL : LeftEq k r z i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) (n : Mx k r) (hn : n ∈ Nlev k r i) :
    RdV X f (n * g) = psi k r z cStd n • RdV X f g := by
  have hmul : ∀ a b : Mx k r, a ∈ Glev k r i → b ∈ Glev k r i → a * b ∈ Glev k r i := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, fun c hc => ?_⟩
    · show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
      have h1 : aᴴ * Hpk k r * a = Hpk k r := ha1
      have h2 : bᴴ * Hpk k r * b = Hpk k r := hb1
      rw [Matrix.conjTranspose_mul]
      calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
        _ = Hpk k r := by rw [h1, h2]
    · obtain ⟨e1, e2⟩ := ha2 c hc
      obtain ⟨f1, f2⟩ := hb2 c hc
      exact ⟨by rw [← Matrix.mulVec_mulVec, f1, e1], by rw [← Matrix.mulVec_mulVec, f2, e2]⟩
  obtain ⟨U1, F1, hU1, hgU1, hF1, hfF1⟩ := hf g hg
  have hd := hasDerivAt_ext i X hX f F1 U1 g hU1 hgU1 hg.1 hF1 hfF1
  have hpath : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (hasDerivAt_ext i X hX (fun y : Mx k r => y) (fun y => y) Set.univ g isOpen_univ (Set.mem_univ _) hg.1
      contDiffOn_id (fun _ _ _ => rfl)).continuousAt
  have hev : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D := by
    apply hpath.preimage_mem_nhds
    have e0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    rw [e0]
    exact hD.mem_nhds hg.2
  have heq : (fun t : ℝ => f (n * g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      fun t => psi k r z cStd n • f (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hev] with t ht
    rw [mul_assoc]
    exact hL _ ⟨hmul _ _ hg.1 (hX t), ht⟩ n hn
  have h2 : HasDerivAt (fun t : ℝ => f (n * g * NormedSpace.exp ((t : ℂ) • X)))
      (psi k r z cStd n • fderiv ℝ F1 g (g * X)) 0 := (hd.const_smul _).congr_of_eventuallyEq heq
  show deriv (fun t : ℝ => f (n * g * NormedSpace.exp ((t : ℂ) • X))) 0 = psi k r z cStd n • RdV X f g
  rw [h2.deriv, rdV_ext i X hX f F1 U1 g hU1 hgU1 hg.1 hF1 hfF1]
end Formalism.FourierDecayAlt.Q.EabLie
