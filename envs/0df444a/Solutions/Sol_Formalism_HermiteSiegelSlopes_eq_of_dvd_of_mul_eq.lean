-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.eq_of_dvd_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:05.590725+00:00
-- url     : https://prove2.me/submissions/866a29fc-e0be-445d-9c79-0b9417c408ad

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {a1 a2 b1 b2 : ℕ} (h1 : b1 ∣ a1) (h2 : b2 ∣ a2) (h : b1 * b2 = a1 * a2)
    (h0 : a1 * a2 ≠ 0) : b1 = a1 := by
  have ha1 : a1 ≠ 0 := left_ne_zero_of_mul h0
  have ha2 : a2 ≠ 0 := right_ne_zero_of_mul h0
  have hb1 := Nat.le_of_dvd (Nat.pos_of_ne_zero ha1) h1
  have hb2 := Nat.le_of_dvd (Nat.pos_of_ne_zero ha2) h2
  have hb2pos : 0 < b2 := Nat.pos_of_ne_zero (fun h' => h0 (by rw [← h, h', mul_zero]))
  by_contra hne
  have hlt : b1 < a1 := lt_of_le_of_ne hb1 hne
  have hlt2 : b1 * b2 < a1 * a2 :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hb2pos) (mul_le_mul_of_nonneg_left hb2 (Nat.zero_le a1))
  rw [h] at hlt2
  exact lt_irrefl _ hlt2
end Formalism.HermiteSiegelSlopes
