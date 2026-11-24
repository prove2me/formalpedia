-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.PRun_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:40.721726+00:00
-- url     : https://prove2.me/submissions/a0813364-97fb-4da5-ade7-a5fcb1f8c418

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_snocF_lt
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_snocF_last
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_even_mod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ b j t d : ℕ} {ev : Bool} {u : Fin j → ℕ}
    (hu : PRun n T L₂ b j t d u) (hd : d ≤ t) (hev : ev = decide (Even (b + t)))
    (hnone : ∀ x, t - d < x → x ≤ t → (b + x) % n ∉ T)
    (hT : (b + (t + 1)) % n ∈ T) (hok : okG L₂ j d ev = true) :
    PRun n T L₂ b (j + 1) (t + 1) 0 (snocF u (t + 1)) := by
  obtain ⟨hmono, hle, htop, hevu, hgap, hlast⟩ := hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c hac
    have hac' : a.val < c.val := hac
    by_cases ha : a.val < j
    · rw [snocF_lt u _ a ha]
      by_cases hc : c.val < j
      · rw [snocF_lt u _ c hc]
        exact hmono (show (⟨a.val, ha⟩ : Fin j) < ⟨c.val, hc⟩ from hac')
      · rw [snocF_last u _ c hc]
        have := hle ⟨a.val, ha⟩
        omega
    · exfalso
      have := c.isLt
      omega
  · intro l
    by_cases hl : l.val < j
    · rw [snocF_lt u _ l hl]; exact (hle _).trans (Nat.le_succ _)
    · rw [snocF_last u _ l hl]
  · intro l
    by_cases hl : l.val < j
    · rw [snocF_lt u _ l hl]; exact htop _
    · rw [snocF_last u _ l hl]; exact hT
  · intro l
    by_cases hl : l.val < j
    · rw [snocF_lt u _ l hl]; exact hevu _
    · rw [snocF_last u _ l hl, even_mod hn]
      by_cases hj : j = 0
      · have hev' : ev = false := by simpa [okG, hj] using hok
        rw [hev'] at hev
        have hne : ¬ Even (b + t) := by simpa using hev.symm
        rw [← add_assoc, Nat.even_add_one]
        exact hne
      · have hok' : (d + 1) % 2 = 0 ∧ L₂ < 2 * (d + 1) := by simpa [okG, hj] using hok
        have hprev := hevu ⟨j - 1, by omega⟩
        rw [hlast (by omega), even_mod hn] at hprev
        have hdd : Even (d + 1) := Nat.even_iff.2 hok'.1
        have : b + (t + 1) = (b + (t - d)) + (d + 1) := by omega
        rw [this]
        exact hprev.add hdd
  · intro l hl
    have hl0 : l.val < j := by omega
    rw [snocF_lt u _ l hl0]
    by_cases hl1 : l.val + 1 < j
    · rw [snocF_lt u _ ⟨l.val + 1, hl⟩ hl1]
      exact hgap ⟨l.val, hl0⟩ hl1
    · rw [snocF_last u _ ⟨l.val + 1, hl⟩ hl1]
      have hj : j ≠ 0 := by omega
      have hok' : (d + 1) % 2 = 0 ∧ L₂ < 2 * (d + 1) := by simpa [okG, hj] using hok
      have hul : u ⟨l.val, hl0⟩ = t - d := by
        have := hlast (by omega)
        have e : (⟨l.val, hl0⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [e]; exact this
      rw [hul]
      refine ⟨by omega, ?_⟩
      intro x h1 h2
      exact hnone x h1 (by omega)
  · intro _
    rw [snocF_last u _ _ (by simp)]
    rfl
end Formalism.G0.TopsWeightFunctionBounds
