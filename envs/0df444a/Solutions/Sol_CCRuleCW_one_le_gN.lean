-- Prove2me | solution 1 for CCRuleCW.one_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:38:58.365904+00:00
-- url     : https://prove2.me/submissions/dbd482c7-7289-4cf0-ac8b-a77f7e512eee

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Theorems.Thm_CCRuleCW_Hpk_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate Nat
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
open scoped Matrix.Norms.Frobenius
namespace CCRuleCW
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have e : B.gN g = ‖g‖ := by
    rw [Matrix.frobenius_norm_def]
    unfold B.gN
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.sq_norm]
    norm_cast
  have hH : 0 < ‖Formalism.QuantumDeterminants.Hpk k r‖ := norm_pos_iff.2 (Hpk_ne_zero k r)
  have h1 : ‖Formalism.QuantumDeterminants.Hpk k r‖ ≤ ‖g‖ ^ 2 * ‖Formalism.QuantumDeterminants.Hpk k r‖ := by
    calc ‖Formalism.QuantumDeterminants.Hpk k r‖ = ‖gᴴ * Formalism.QuantumDeterminants.Hpk k r * g‖ := by rw [hg']
      _ ≤ ‖gᴴ * Formalism.QuantumDeterminants.Hpk k r‖ * ‖g‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖gᴴ‖ * ‖Formalism.QuantumDeterminants.Hpk k r‖ * ‖g‖ := by
          gcongr; exact Matrix.frobenius_norm_mul _ _
      _ = ‖g‖ ^ 2 * ‖Formalism.QuantumDeterminants.Hpk k r‖ := by rw [Matrix.frobenius_norm_conjTranspose]; ring
  have h2 : 1 ≤ ‖g‖ ^ 2 := by
    by_contra hc
    replace hc := lt_of_not_ge hc
    have := mul_lt_mul_of_pos_right hc hH
    linarith
  rw [e]
  nlinarith [norm_nonneg g]
end CCRuleCW
