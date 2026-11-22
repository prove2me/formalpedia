-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.levelCoverProperty_chainBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:39.180799+00:00
-- url     : https://prove2.me/submissions/abc43957-2cb2-4618-be4a-12ca3b302233

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_longestPeriodicSuffixLength
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_le_card_sub_one_of_injOn
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_dvd_of_periodicOn
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_periodicOn
public import Theorems.Thm_DeciSigma1_Holes_Periodic_long_factor_in_piece
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_prefix_drop_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_le_firstRejection
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_le_length
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_nodup
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_prefix_of_lt
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
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
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]
omit [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds σ k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} {m : ℕ} (h : M.Eligible W i)
        (hK : LevelCoverProperty C m M W i) :
    ChainBound (W i) (C.chainLengthBound m + Fintype.card S) := by
  classical
  intro bs hbs
  by_cases h2 : bs.length ≤ 1
  · omega
  push Not at h2
  have hle := hbs.le_length (by omega)
  obtain ⟨fs, hfl, hfv, hunc⟩ := hK.1
  have hLY : longestPeriodicSuffixLength (C.periodBound m) (W i) < C.terminalLengthBound m := hK.2
  have hJn : M.firstRejection W i ≤ (W i).length := StructuralReader.firstRejection_le h
  set A : Finset ℕ := bs.toFinset.image (fun b => (W i).length - b) with hA
  have hcardA : A.card = bs.length := by
    rw [hA, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hbs.nodup]
    intro b hb b' hb' he
    rw [Finset.mem_coe, List.mem_toFinset] at hb hb'
    have := hle b hb; have := hle b' hb'
    simp only at he; omega
  have hAle : ∀ x ∈ A, x ≤ (W i).length := by
    intro x hx; obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx; omega
  have hcmp : ∀ x ∈ A, ∀ y ∈ A, x < y → (W i).drop y <+: (W i).drop x := by
    intro x hx y hy hxy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hy
    rw [List.mem_toFinset] at hb hb'
    have hbb : b' < b := by have := hle b hb; have := hle b' hb'; omega
    exact hbs.prefix_of_lt hb' hb hbb
  have hper : ∀ x ∈ A, ∀ y ∈ A, x < y → PeriodicOn (W i) (y - x) x (W i).length := by
    intro x hx y hy hxy
    have hpre := (prefix_drop_iff (hAle x hx)).mp (hcmp x hx y hy hxy)
    intro p hp1 hp2
    have := hpre.2 (p - x) (by simp; omega)
    rw [List.getElem?_drop, show x + (p - x) = p by omega] at this
    rw [this]; congr 1; omega
  -- the five kinds of start
  set n := (W i).length with hn
  set L := longestPeriodicSuffixLength (C.periodBound m) (W i) with hL
  set J := M.firstRejection W i with hJ
  let Af : PeriodicFactor → Finset ℕ :=
      fun f => A.filter (fun x => f.start ≤ x ∧ x < f.stop ∧ x + L < n)
  have hsub : A ⊆ A.filter (fun x => x ≤ J) ∪ A.filter (fun x => x = n) ∪
      A.filter (fun x => J ≤ x ∧ x < n ∧ ¬ Covers fs x) ∪
      A.filter (fun x => n ≤ x + L ∧ x < n) ∪ fs.toFinset.biUnion Af := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset, Af]
    by_cases h1 : x ≤ J
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hx, h1⟩)))
    by_cases h2 : x = n
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hx, h2⟩)))
    have hxn : x < n := lt_of_le_of_ne (hAle x hx) h2
    by_cases h3 : Covers fs x
    · obtain ⟨f, hf, hfs, hfe⟩ := h3
      by_cases h4 : n ≤ x + L
      · exact Or.inl (Or.inr ⟨hx, h4, hxn⟩)
      · exact Or.inr ⟨f, hf, hx, hfs, hfe, by omega⟩
    · exact Or.inl (Or.inl (Or.inr ⟨hx, by omega, hxn, h3⟩))
  -- starts before the first rejected cut carry distinct live states
  have hH : (A.filter (fun x => x ≤ J)).card ≤ Fintype.card S - 1 := by
    apply card_le_card_sub_one_of_injOn _ id (Set.injOn_id _) (M.runPrefix W i) M.dead
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      exact StructuralReader.runPrefix_ne_of_le_firstRejection h hxy hy.2 (hcmp x hx.1 y hy.1 hxy)
    · intro x _; exact h.runPrefix_ne x
  have hE : (A.filter (fun x => x = n)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    omega
  have hU : (A.filter (fun x => J ≤ x ∧ x < n ∧ ¬ Covers fs x)).card ≤ C.uncoveredBound m := by
    refine le_trans (Finset.card_le_card ?_) hunc
    intro x hx
    simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact ⟨⟨hx.2.1, hx.2.2.1⟩, hx.2.2.2⟩
  have hT : (A.filter (fun x => n ≤ x + L ∧ x < n)).card ≤ L := by
    calc _ ≤ (Finset.Ico (n - L) n).card := Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
      _ ≤ L := by rw [Nat.card_Ico]; omega
  -- each factor contributes at most twice the period bound of the level
  have hAf : ∀ f ∈ fs, (Af f).card ≤ 2 * C.periodBound m := by
    intro f hf
    obtain ⟨hfp, hfE, hfe, hfper⟩ := hfv f hf
    by_cases hshort : f.stop < f.start + 2 * f.period
    · calc (Af f).card ≤ (Finset.Ico f.start f.stop).card := Finset.card_le_card (fun x hx => by
              simp only [Af, Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
        _ ≤ 2 * C.periodBound m := by rw [Nat.card_Ico]; omega
    push Not at hshort
    obtain ⟨d, P, hPl, hPs, hPe, hdvd⟩ : ∃ d, ∃ P : Piece W d, P.coordinate = i ∧ P.start ≤
        f.start ∧ f.stop ≤ P.stop ∧
        d ∣ f.period := by
      obtain ⟨P, h1, h2, h3, h4⟩ := long_factor_in_piece W i hfp hfe hshort hfper
      exact ⟨_, P, h1, h2, h3, h4⟩
    have hdpos : 0 < d := P.period_pos
    have hdle : d ≤ f.period := Nat.le_of_dvd hfp hdvd
    have hPper : PeriodicOn (W i) d P.start P.stop := by have := P.periodicOn; rwa [hPl] at this
    have hPle : P.stop ≤ n := by have := P.stop_le_length; rwa [hPl] at this
    by_cases hterm : P.stop = n
    · have hTl := le_longestPeriodicSuffixLength hdpos (hdle.trans hfE) (by omega) (hterm ▸ hPper)
      have hempty : Af f = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        simp only [Af, Finset.mem_filter] at hx
        omega
      rw [hempty]; simp
    have hbrk : (W i)[P.stop]? ≠ (W i)[P.stop - d]? := by
      have hmaxR := P.right_maximal
      rw [hPl] at hmaxR
      rcases hmaxR with h' | h'
      · exact absurd h' hterm
      · exact h'
    have hone : (A.filter (fun x => P.start ≤ x ∧ x + d ≤ P.stop)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter] at hx hy
      by_contra hne
      have main : ∀ x y, x ∈ A → P.start ≤ x → y ∈ A → y + d ≤ P.stop → x < y → False := by
        intro x y hxA hxs hyA hyd hxy
        have hδ := hper x hxA y hyA hxy
        have hδ' : PeriodicOn (W P.coordinate) (y - x) x P.stop := by
          rw [hPl]; exact hδ.mono le_rfl hPle
        have hdδ := P.dvd_of_periodicOn hxs hδ' (by omega)
        obtain ⟨c, hc⟩ := hdδ
        apply hbrk
        have e1 := hδ (P.stop - (y - x)) (by omega) (by omega)
        rw [show P.stop - (y - x) + (y - x) = P.stop by omega] at e1
        rw [← e1]
        apply hPper.eq_of_mod (by omega) (by omega) (by omega) (by omega)
        rw [hc, Nat.sub_mul_mod (by rw [← hc]; omega)]
        have := Nat.sub_mul_mod (x := P.stop) (k := 1) (n := d) (by omega)
        rw [Nat.mul_one] at this
        rw [this]
      rcases Nat.lt_or_gt_of_ne hne with hxy | hxy
      · exact main x y hx.1 hx.2.1 hy.1 hy.2.2 hxy
      · exact main y x hy.1 hy.2.1 hx.1 hx.2.2 hxy
    have hrest : (A.filter (fun x => P.stop < x + d ∧ x < P.stop)).card ≤ d - 1 := by
      calc _ ≤ (Finset.Ico (P.stop + 1 - d) P.stop).card := Finset.card_le_card (fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
        _ ≤ d - 1 := by rw [Nat.card_Ico]; omega
    calc (Af f).card ≤ (A.filter (fun x => P.start ≤ x ∧ x + d ≤ P.stop) ∪
          A.filter (fun x => P.stop < x + d ∧ x < P.stop)).card :=
          Finset.card_le_card (fun x hx => by
            simp only [Af, Finset.mem_filter, Finset.mem_union] at hx ⊢
            by_cases hxd : x + d ≤ P.stop
            · exact Or.inl ⟨hx.1, by omega, hxd⟩
            · exact Or.inr ⟨hx.1, by omega, by omega⟩)
      _ ≤ 1 + (d - 1) := (Finset.card_union_le _ _).trans (Nat.add_le_add hone hrest)
      _ ≤ 2 * C.periodBound m := by omega
  have hB : (fs.toFinset.biUnion Af).card ≤ (C.pieceCountBase + 1) * (2 * C.periodBound m) := by
    calc (fs.toFinset.biUnion Af).card ≤ ∑ f ∈ fs.toFinset, (Af f).card := Finset.card_biUnion_le
      _ ≤ fs.toFinset.card • (2 * C.periodBound m) :=
          Finset.sum_le_card_nsmul _ _ _ (fun f hf => hAf f (List.mem_toFinset.mp hf))
      _ ≤ (C.pieceCountBase + 1) * (2 * C.periodBound m) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul ((List.toFinset_card_le fs).trans hfl) le_rfl
  have hXK := C.chainLengthBound_ge_cover m
  have htot := (Finset.card_le_card hsub).trans <| (Finset.card_union_le _ _).trans <|
    Nat.add_le_add_right ((Finset.card_union_le _ _).trans <| Nat.add_le_add_right
      ((Finset.card_union_le _ _).trans <| Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
  omega
end DeciSigma1.Holes.Tail
