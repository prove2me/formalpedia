-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.exists_bad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:01.125676+00:00
-- url     : https://prove2.me/submissions/56286a63-4dda-4986-acc3-2c53a288330e

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hm : IsMirab h) (hu : ¬ IsUniU h) :
    ∃ s l : Fin n, l ≤ s ∧ (∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0) ∧
      h s.castSucc l.castSucc ≠ if l = s then 1 else 0 := by
  classical
  have hlast : h (Fin.last n) (Fin.last n) = 1 ∧ ∀ b, b < Fin.last n → h (Fin.last n) b = 0 :=
    ⟨by rw [hm]; simp, fun b hb => by rw [hm, if_neg hb.ne]⟩
  have hex : ∃ j, ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0) := by
    by_contra hno
    push_neg at hno
    exact hu ⟨fun i => (hno i).1, fun i j hji => (hno i).2 j hji⟩
  obtain ⟨j1, hj1⟩ := hex
  let S := Finset.univ.filter fun j => ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0)
  have hSne : S.Nonempty := ⟨j1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj1⟩⟩
  set j0 := S.max' hSne with hj0def
  have hj0 : ¬ (h j0 j0 = 1 ∧ ∀ b, b < j0 → h j0 b = 0) := (Finset.mem_filter.1 (S.max'_mem hSne)).2
  have hgood : ∀ j, j0 < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0 := by
    intro j hj
    by_contra hb
    exact absurd (S.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) (not_le.2 hj)
  have hne : j0 ≠ Fin.last n := fun he => hj0 (he ▸ hlast)
  set s := j0.castPred hne with hsdef
  have hs : s.castSucc = j0 := Fin.castSucc_castPred j0 hne
  have hgood' : ∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0 := by
    rw [hs]
    exact hgood
  by_cases hd : h j0 j0 = 1
  · have hb : ∃ b, b < j0 ∧ h j0 b ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hj0 ⟨hd, hno⟩
    obtain ⟨b, hb0, hbne⟩ := hb
    have hbl : b ≠ Fin.last n := (lt_of_lt_of_le hb0 (Fin.le_last _)).ne
    refine ⟨s, b.castPred hbl, ?_, hgood', ?_⟩
    · rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred, hs]
      exact hb0.le
    · have hlt : b.castPred hbl ≠ s := by
        intro he
        have := congrArg Fin.castSucc he
        rw [Fin.castSucc_castPred, hs] at this
        exact hb0.ne this
      rw [if_neg hlt]
      simpa [Fin.castSucc_castPred, hs] using hbne
  · refine ⟨s, s, le_rfl, hgood', ?_⟩
    rw [if_pos rfl]
    simpa [hs] using hd
end Formalism.EigenvalueLevelCeiling
