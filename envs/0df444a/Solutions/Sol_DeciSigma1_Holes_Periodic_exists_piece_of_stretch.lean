-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.exists_piece_of_stretch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:29.394654+00:00
-- url     : https://prove2.me/submissions/46fc798c-05e7-4a0f-8eda-c414af3a4047

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_isPrimitive
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsPrimitive_ne_nil
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_union
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_window_rotate
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (W : Fin k → List α) (l : Fin k) {d x y : ℕ}
    (hxy : x + 2 * d ≤ y) (hy : y ≤ (W l).length) (hper : PeriodicOn (W l) d x y)
    (hprim : IsPrimitive (((W l).drop x).take d)) :
    ∃ P : Piece W d, P.coordinate = l ∧ P.start ≤ x ∧ y ≤ P.stop ∧
      IsConjugate P.root (((W l).drop x).take d) ∧
      ((x = 0 ∨ (W l)[x - 1]? ≠ (W l)[x - 1 + d]?) → P.start = x) ∧
      ((y = (W l).length ∨ (W l)[y]? ≠ (W l)[y - d]?) → P.stop = y) := by
  classical
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact absurd (by simp [h]) hprim.ne_nil
    · exact h
  have hexS : ∃ s, s ≤ x ∧ PeriodicOn (W l) d s y := ⟨x, le_rfl, hper⟩
  set s := Nat.find hexS with hs_def
  obtain ⟨hsx, hsper⟩ : s ≤ x ∧ PeriodicOn (W l) d s y := Nat.find_spec hexS
  set e := Nat.findGreatest (fun e => PeriodicOn (W l) d x e) (W l).length with he_def
  have hye : y ≤ e := Nat.le_findGreatest hy hper
  have heper : PeriodicOn (W l) d x e := Nat.findGreatest_spec hy hper
  have hele : e ≤ (W l).length := Nat.findGreatest_le _
  have hper' : PeriodicOn (W l) d s e := by
    have := hsper.union heper (by omega); rwa [max_eq_right hye] at this
  have hwin : (((W l).drop x).take d) = (((W l).drop s).take d).rotate ((x - s) % d) :=
    hper'.window_rotate hele hsx (by omega)
  have hcls : IsConjugate (((W l).drop s).take d) (((W l).drop x).take d) := ⟨_, hwin⟩
  have hmaxL : s = 0 ∨ (W l)[s - 1]? ≠ (W l)[s - 1 + d]? := by
    by_contra hcon
    push Not at hcon
    have h1 : PeriodicOn (W l) d (s - 1) y := by
      intro p hp hpy
      by_cases hps : p = s - 1
      · subst hps; exact hcon.2
      · exact hsper p (by omega) hpy
    have := Nat.find_min' hexS ⟨by omega, h1⟩
    omega
  have hmaxR : e = (W l).length ∨ (W l)[e]? ≠ (W l)[e - d]? := by
    by_contra hcon
    push Not at hcon
    have h1 : PeriodicOn (W l) d x (e + 1) := by
      intro p hp hpe
      by_cases hpe' : p + d < e
      · exact heper p hp hpe'
      · have : p = e - d := by omega
        subst this
        rw [show e - d + d = e by omega]; exact hcon.2.symm
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self e)
      (by have := hcon.1; omega) h1
  refine ⟨⟨l, s, e, by omega, hele, hper', hcls.symm.isPrimitive hprim, hmaxL, hmaxR⟩,
    rfl, hsx, hye, hcls, ?_, ?_⟩
  · intro hbrk
    change s = x
    by_contra hne
    rcases hbrk with h | h
    · omega
    · exact h (hsper (x - 1) (by omega) (by omega))
  · intro hbrk
    change e = y
    by_contra hne
    rcases hbrk with h | h
    · omega
    · apply h
      have := heper (y - d) (by omega) (by omega)
      rw [show y - d + d = y by omega] at this
      exact this.symm
end DeciSigma1.Holes.Periodic
