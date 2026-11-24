-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.trace_Hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:26:14.258368+00:00
-- url     : https://prove2.me/submissions/aede76bc-dfa3-409f-864e-3b62f27d059b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (k r : ℕ) : (Hpk k r).trace = ((k + r : ℕ) : ℂ) - ((r + 1 : ℕ) : ℂ) := by
  have h1 : ∀ i : Fin (2 * r + k + 1), Hpk k r i i =
      (fun n : ℕ => (if r ≤ n ∧ n < r + k then (1 : ℂ) else 0) - (if n = r + k then 1 else 0)) i.val := by
    intro i
    unfold Hpk
    simp only [and_true]
    split_ifs <;> first | (exfalso; omega) | simp
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range
    (fun n : ℕ => (if r ≤ n ∧ n < r + k then (1 : ℂ) else 0) - (if n = r + k then 1 else 0)) (2 * r + k + 1),
    Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have f1 : (Finset.range (2 * r + k + 1)).filter (fun n => r ≤ n ∧ n < r + k) = Finset.Ico r (r + k) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have f2 : (Finset.range (2 * r + k + 1)).filter (fun n => n = r + k) = {r + k} := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
  rw [f1, f2]
  simp
  ring
end Formalism.FourierDecayAlt.P.HermitianFormFactor
