-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.stepD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:01.825539+00:00
-- url     : https://prove2.me/submissions/02af5a09-f10e-425c-a03d-fe6aabba82d9

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_F_perm
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_letter_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
variable (N : ℕ)
variable {S : Subring R}
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
theorem _root_.solution (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (D : ℕ) (hD : 1 ≤ D) (ih : ∀ l, Valid S (D + 1) l → piN N (F ρ l) ∈ SQ N S) :
    ∀ c (l : List (R × ℕ × G)), Valid S D l → l.countP (fun L => L.2.1 = D) = c →
      piN N (F ρ l) ∈ SQ N S := by
  intro c
  induction c with
  | zero =>
    intro l hl hc
    apply ih
    intro L hL
    refine ⟨(hl L hL).1, ?_⟩
    have h1 := (hl L hL).2
    have h2 : ¬ (L.2.1 = D) := by
      have := List.countP_eq_zero.1 hc L hL
      simpa using this
    omega
  | succ c ihc =>
    intro l hl hc
    obtain ⟨L0, hL0, hd0⟩ : ∃ L0 ∈ l, L0.2.1 = D := by
      have : 0 < l.countP (fun L => L.2.1 = D) := by omega
      obtain ⟨a, ha, hpa⟩ := List.countP_pos_iff.1 this
      exact ⟨a, ha, by simpa using hpa⟩
    have hperm := List.perm_cons_erase hL0
    rw [F_perm ρ hperm, key N ρ L0 (by omega) _]
    refine (SQ N S).mul_mem (letter_mem N ρ hS L0 (hl L0 hL0).1) ?_
    apply ihc
    · intro L hL
      simp only [elim, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hL
      rcases hL with hL | ⟨L', hL', k, hk, rfl⟩
      · exact hl L (List.mem_of_mem_erase hL)
      · have h' := hl L' (List.mem_of_mem_erase hL')
        refine ⟨S.mul_mem (S.pow_mem (hl L0 hL0).1 _) h'.1, ?_⟩
        simp only [newL]
        have := h'.2
        omega
    · have hc' := hperm.countP_eq (fun L => L.2.1 = D)
      rw [List.countP_cons_of_pos (by simpa using hd0)] at hc'
      rw [elim, List.countP_append]
      have hz : (List.flatMap (fun L => (List.range N).map (fun k => newL L0 L (k + 1)))
          (l.erase L0)).countP (fun L => L.2.1 = D) = 0 := by
        rw [List.countP_eq_zero]
        intro L hL
        simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hL
        obtain ⟨L', hL', k, hk, rfl⟩ := hL
        have h' := hl L' (List.mem_of_mem_erase hL')
        have hm : L0.2.1 ≤ (k + 1) * L0.2.1 := Nat.le_mul_of_pos_left L0.2.1 (by omega)
        have := h'.2
        intro hc2
        have hc3 := of_decide_eq_true hc2
        simp only [newL] at hc3
        omega
      omega
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
