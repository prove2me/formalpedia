-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.card_tailOccurrences_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:13.699484+00:00
-- url     : https://prove2.me/submissions/5fee59c9-830c-41b3-9737-f6bcaeefc4ab

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_factor_inter_gt
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_longestPeriodicSuffixLength
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_window
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_le_add
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_mem_occurrences
public import Theorems.Thm_DeciSigma1_Words_period_extend_gcd
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__suffixOfLength_5cd134b71b98
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {w : List α} {J P E T Y b : ℕ} (hcov : PeriodicCover w J P E T)
    (hY : longestPeriodicSuffixLength E w < Y) (hb : 1 + T + P * (Y + T + 2 * E * P + 1) ≤ b) :
    ((occurrences w w b).filter (fun e => J + b ≤ e)).card ≤ P := by
  classical
  obtain ⟨fs, hfl, hfv, hunc⟩ := hcov
  set O := (occurrences w w b).filter (fun e => J + b ≤ e) with hO
  set n := w.length with hn
  -- an occurrence ending at `e` copies the last `b` letters, shifted by `n - e`
  have hcopy : ∀ e ∈ O, J + b ≤ e ∧ e ≤ n ∧
      ∀ z, n - b ≤ z → z < n → w[z - (n - e)]? = w[z]? := by
    intro e he
    rw [hO, Finset.mem_filter, mem_occurrences] at he
    obtain ⟨⟨hen, hbn, hocc⟩, hJe⟩ := he
    have hl : (suffixOfLength w b).length = b := by simp [hbn]
    rw [suffix_take_iff hen, hl] at hocc
    refine ⟨hJe, hen, fun z hz hzn => ?_⟩
    have := hocc.2 (z - (n - b)) (by omega)
    rw [getElem?_suffixOfLength, show e - b + (z - (n - b)) = z - (n - e) by omega,
      show w.length - b + (z - (n - b)) = z by omega] at this
    exact this
  rcases O.eq_empty_or_nonempty with hO0 | ⟨e₀, he₀⟩
  · rw [hO0]; simp
  obtain ⟨hJe₀, he₀n, -⟩ := hcopy e₀ he₀
  set r := Y + T + 2 * E * P + 1 with hr
  -- a factor `f` meets the suffix `[n - b, n)` in more than `r` positions
  obtain ⟨f, hf, hfr⟩ := exists_factor_inter_gt (r := r) hunc (x := n - b) (y := n) (by omega)
    le_rfl (by have : fs.length * r ≤ P * r := Nat.mul_le_mul_right _ hfl; omega)
  obtain ⟨hp, hpE, hfn, hfper⟩ := hfv f hf
  set p := f.period with hpdef
  have hP1 : 1 ≤ P := (List.length_pos_of_mem hf).trans_le hfl
  have hEP : 2 * E ≤ 2 * E * P := Nat.le_mul_of_pos_right _ hP1
  set a1 := max f.start (n - b) with ha1
  have hfr' : r < f.stop - a1 := by rw [min_eq_left hfn] at hfr; exact hfr
  -- the first break of the period `p` at or after `f.stop`
  have hex : ∃ j, f.stop + j = n ∨ w[f.stop + j]? ≠ w[f.stop + j - p]? :=
    ⟨n - f.stop, .inl (by omega)⟩
  set o := f.stop + Nat.find hex with ho
  have hmin : ∀ j < Nat.find hex, f.stop + j ≠ n ∧ w[f.stop + j]? = w[f.stop + j - p]? :=
    fun j hj => by simpa using Nat.find_min hex hj
  have hon : o ≤ n := by
    by_contra hlt
    exact (hmin (n - f.stop) (by omega)).1 (by omega)
  have hper : PeriodicOn w p a1 o := by
    intro q hq hqo
    by_cases hqf : q + p < f.stop
    · exact hfper q ((le_max_left _ _).trans hq) hqf
    · have h2 := (hmin (q + p - f.stop) (by omega)).2
      rw [show f.stop + (q + p - f.stop) = q + p by omega, show q + p - p = q by omega] at h2
      exact h2.symm
  have hon' : o < n := by
    rcases lt_or_eq_of_le hon with h | h
    · exact h
    · exfalso
      rw [h] at hper
      have := le_longestPeriodicSuffixLength hp hpE (by omega) hper
      omega
  have hbrk : w[o]? ≠ w[o - p]? := by
    rcases Nat.find_spec hex with h | h
    · omega
    · exact h
  -- each occurrence repeats the periodic interval `[a1, o)` and its break at `o`
  have hC1 : ∀ e ∈ O, PeriodicOn w p (a1 - (n - e)) (o - (n - e)) := by
    intro e he q hq hqo
    obtain ⟨-, -, hc⟩ := hcopy e he
    have e1 := hc (q + (n - e)) (by omega) (by omega)
    have e2 := hc (q + p + (n - e)) (by omega) (by omega)
    rw [show q + (n - e) - (n - e) = q by omega] at e1
    rw [show q + p + (n - e) - (n - e) = q + p by omega] at e2
    rw [e1, e2, show q + p + (n - e) = q + (n - e) + p by omega]
    exact hper _ (by omega) (by omega)
  have hC2 : ∀ e ∈ O, w[o - (n - e)]? ≠ w[o - (n - e) - p]? := by
    intro e he
    obtain ⟨-, -, hc⟩ := hcopy e he
    rw [hc o (by omega) hon', show o - (n - e) - p = o - p - (n - e) by omega,
      hc (o - p) (by omega) (by omega)]
    exact hbrk
  -- a factor of the cover meets the last `r` positions before the repeated break
  have hF : ∀ e, ∃ F : PeriodicFactor, e ∈ O →
      F ∈ fs ∧ 2 * E < min F.stop (o - (n - e)) - max F.start (o - (n - e) - r) := by
    intro e
    by_cases he : e ∈ O
    · obtain ⟨hJe, hen, -⟩ := hcopy e he
      have hl : fs.length * (2 * E) ≤ 2 * E * P := by
        calc fs.length * (2 * E) ≤ P * (2 * E) := Nat.mul_le_mul_right _ hfl
          _ = 2 * E * P := Nat.mul_comm _ _
      obtain ⟨F, hF1, hF2⟩ := exists_factor_inter_gt (r := 2 * E) hunc
        (x := o - (n - e) - r) (y := o - (n - e)) (by omega) (by omega) (by omega)
      exact ⟨F, fun _ => ⟨hF1, hF2⟩⟩
    · exact ⟨⟨0, 0, 0⟩, fun h => absurd h he⟩
  choose F hF using hF
  -- that factor ends at or before the repeated break
  have hstop : ∀ e ∈ O, (F e).stop ≤ o - (n - e) := by
    intro e he
    obtain ⟨hF1, hF2⟩ := hF e he
    obtain ⟨hp', hp'E, hF'n, hF'per⟩ := hfv _ hF1
    obtain ⟨hJe, hen, -⟩ := hcopy e he
    by_contra hlt
    push Not at hlt
    set oe := o - (n - e)
    set c1 := max (F e).start (oe - r)
    have hc1 : oe - c1 > 2 * E := by rw [min_eq_right hlt.le] at hF2; exact hF2
    have h1 : PeriodicOn w p c1 oe := (hC1 e he).mono (by omega) le_rfl
    have h2 : PeriodicOn w (F e).period c1 oe := hF'per.mono (le_max_left _ _) hlt.le
    have hgle : p.gcd (F e).period ≤ (F e).period := Nat.gcd_le_right _ hp'
    have hg := period_extend_gcd (by omega) (by omega) h1 h2 (by omega)
    have hFg := periodicOn_of_window hF'per hg (le_max_left _ _) hlt.le (by omega) hp'
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_left p (F e).period
    have := hFg.eq_of_le_add (p := oe - p) (by omega) c (by
      rw [Nat.mul_comm, ← hc]; omega)
    rw [Nat.mul_comm, ← hc, show oe - p + p = oe by omega] at this
    exact hC2 e he this.symm
  -- distinct occurrences are charged to distinct factors
  have hinj : Set.InjOn F O := by
    intro e he e' he' heq
    by_contra hne
    have key : ∀ e ∈ O, ∀ e' ∈ O, e < e' → F e = F e' → False := by
      intro e he e' he' hlt heq
      have hs := hstop e he
      obtain ⟨-, hF2⟩ := hF e' he'
      obtain ⟨hJe', hen', -⟩ := hcopy e' he'
      obtain ⟨hJe, hen, -⟩ := hcopy e he
      rw [← heq] at hF2
      have := (hC1 e' he') (o - (n - e) - p) (by omega) (by omega)
      rw [show o - (n - e) - p + p = o - (n - e) by omega] at this
      exact hC2 e he this.symm
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key e he e' he' h heq
    · exact key e' he' e he h heq.symm
  calc O.card ≤ fs.toFinset.card :=
        Finset.card_le_card_of_injOn F (fun e he => List.mem_toFinset.mpr (hF e he).1) hinj
    _ ≤ fs.length := List.toFinset_card_le fs
    _ ≤ P := hfl
end DeciSigma1.Holes.Tail
