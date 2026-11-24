-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.rdV_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:56:38.117835+00:00
-- url     : https://prove2.me/submissions/232c31ef-a786-465a-bfa4-840c9cc56ebd

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_hasDerivAt_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Smooth
section Rd
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
private lemma Glev_mul_mem {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  refine ⟨?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg.1, hh.1]
  · obtain ⟨e1, e2⟩ := hg.2 a ha
    obtain ⟨f1, f2⟩ := hh.2 a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, f1, e1], by rw [← Matrix.mulVec_mulVec, f2, e2]⟩
private lemma continuousAt_mul_exp_smul_of_mem_Glev (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    {g : Mx k r} (hg : g ∈ Glev k r i) :
    ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
  (Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext i X hX (fun x => x) (fun x => x) Set.univ g isOpen_univ
    (Set.mem_univ _) hg contDiffOn_id (fun _ _ _ => rfl)).continuousAt
end Rd
section Fold
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
end Fold
end Formalism.FourierDecayAlt.Q.TPresMain
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (hD : IsOpen D) (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) : RdV X f g = RdV X f' g := by
  simp only [RdV]
  apply Filter.EventuallyEq.deriv_eq
  have hc := continuousAt_mul_exp_smul_of_mem_Glev X hX hg.1
  have hD' : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' D ∈ 𝓝 (0 : ℝ) := by
    apply hc.preimage_mem_nhds
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    exact hD.mem_nhds hg.2
  filter_upwards [hD'] with t ht
  exact h _ ⟨Glev_mul_mem hg.1 (hX t), ht⟩
end Formalism.FourierDecayAlt.Q.TPresMain
