-- Prove2me | solution 1 for Formalism.QuantumDeterminants.dslowk_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:43.056207+00:00
-- url     : https://prove2.me/submissions/15b91746-942a-40a4-bb47-4a03523c2988

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution {n : ℕ} {lam : Fin n → ℝ} {c : ℝ} (hanti : StrictAnti lam)
    (hint : ∀ x, ∃ m : ℤ, lam x - c = m) {a b : Fin n} (hab : a < b) :
    ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) ≤ lam a - lam b := by
  choose m hm using hint
  have key : ∀ j (hj : j < n), (a : ℕ) ≤ j → m ⟨j, hj⟩ + (j : ℤ) ≤ m a + ((a : ℕ) : ℤ) := by
    intro j
    induction j with
    | zero =>
      intro hj ha
      have : a = ⟨0, hj⟩ := Fin.ext (by simp; omega)
      subst this; simp
    | succ j ih =>
      intro hj ha
      rcases Nat.lt_or_ge (a : ℕ) (j + 1) with h | h
      · have ih' := ih (by omega) (by omega)
        have hlt : lam ⟨j + 1, hj⟩ < lam ⟨j, by omega⟩ := hanti (Fin.mk_lt_mk.mpr (by omega))
        have e1 := hm ⟨j + 1, hj⟩
        have e2 := hm ⟨j, by omega⟩
        have h3 : ((m ⟨j + 1, hj⟩ : ℤ) : ℝ) < (m ⟨j, by omega⟩ : ℝ) := by linarith
        have h4 : m ⟨j + 1, hj⟩ < m ⟨j, by omega⟩ := by exact_mod_cast h3
        push_cast; omega
      · have : a = ⟨j + 1, hj⟩ := Fin.ext (by simp; omega)
        subst this; simp
  have hb := key b b.isLt (le_of_lt (Fin.lt_def.mp hab))
  simp only [Fin.eta] at hb
  have e1 := hm a
  have e2 := hm b
  have hbR : ((m b : ℤ) : ℝ) + ((b : ℕ) : ℝ) ≤ (m a : ℝ) + ((a : ℕ) : ℝ) := by exact_mod_cast hb
  linarith
end Formalism.QuantumDeterminants
