-- Prove2me | solution 1 for Formalism.QuantumDeterminants.uW_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:44.548216+00:00
-- url     : https://prove2.me/submissions/fe9e4955-4009-45d6-a24f-65bfaf1eec5a

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution (l : Fin m) (x : Fin m → ℂ) (a : ℂ) (t : ℝ) :
    uW l (x + t • (Pi.single l a : Fin m → ℂ)) = (star (x l) + (t : ℂ) * star a)⁻¹ *
      (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) := by
  have hl : (x + t • (Pi.single l a : Fin m → ℂ)) l = x l + t * a := by
    simp [Complex.real_smul]
  have hk : ∀ k ∈ Finset.univ.erase l, (x + t • (Pi.single l a : Fin m → ℂ)) k = x k := by
    intro k hk
    simp [Finset.ne_of_mem_erase hk]
  have hprod : ∏ k, Complex.normSq ((x + t • (Pi.single l a : Fin m → ℂ)) k) =
      Complex.normSq (x l + t * a) * ∏ k ∈ Finset.univ.erase l, Complex.normSq (x k) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hl]
    congr 1
    exact Finset.prod_congr rfl fun k hk' => by rw [hk k hk']
  have key : (star (x l) + (t : ℂ) * star a)⁻¹ =
      (x l + t * a) * (((Complex.normSq (x l + t * a))⁻¹ : ℝ) : ℂ) := by
    have e : star (x l) + (t : ℂ) * star a = (starRingEnd ℂ) (x l + t * a) := by
      simp [Complex.star_def, map_add, map_mul, Complex.conj_ofReal]
    rw [e, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj]
  unfold uW
  rw [hprod, hl, key, mul_inv, Complex.ofReal_mul]
  ring
end Formalism.QuantumDeterminants
