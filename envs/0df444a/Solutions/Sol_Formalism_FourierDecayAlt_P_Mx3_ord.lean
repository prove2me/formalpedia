-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.ord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:19.917364+00:00
-- url     : https://prove2.me/submissions/59cdab15-2f39-40f1-aed4-992c41c4133c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (k : ℕ) (u u' ρ : ℕ → ℝ) (hI : I.Interlaces k u u' ρ) (l : ℕ) (hl : l ∈ Icc 1 (k - 1)) :
    (∀ i ∈ Icc 1 k, i ≤ l → u l ≤ u i ∧ u' l ≤ u' i) ∧ (∀ i ∈ Icc 1 k, l < i → u i ≤ u (l + 1) ∧ u' i ≤ u' (l + 1)) ∧
    (∀ j ∈ Icc 1 (k - 1), j < l → u l + 1 / 2 ≤ ρ j ∧ u' l + 1 / 2 ≤ ρ j) ∧
    (∀ j ∈ Icc 1 (k - 1), l < j → ρ j + 1 / 2 ≤ u (l + 1) ∧ ρ j + 1 / 2 ≤ u' (l + 1)) := by
  have hm := mono k u u' ρ hI
  have hl' := Finset.mem_Icc.1 hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    have c := hm (l - i) i hi'.1 (by omega)
    have e : i + (l - i) = l := by omega
    rwa [e] at c
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    have c := hm (i - (l + 1)) (l + 1) (by omega) (by omega)
    have e : l + 1 + (i - (l + 1)) = i := by omega
    rwa [e] at c
  · intro j hj h
    have hj' := Finset.mem_Icc.1 hj
    have b := hI j hj
    have c := hm (l - (j + 1)) (j + 1) (by omega) (by omega)
    have e : j + 1 + (l - (j + 1)) = l := by omega
    rw [e] at c
    constructor <;> linarith [b.2.2.1, b.2.2.2, c.1, c.2]
  · intro j hj h
    have hj' := Finset.mem_Icc.1 hj
    have b := hI j hj
    have c := hm (j - (l + 1)) (l + 1) (by omega) (by omega)
    have e : l + 1 + (j - (l + 1)) = j := by omega
    rw [e] at c
    constructor <;> linarith [b.1, b.2.1, c.1, c.2]
end Formalism.FourierDecayAlt.P.Mx3
