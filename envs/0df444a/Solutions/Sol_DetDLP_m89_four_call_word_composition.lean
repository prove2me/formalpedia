-- Prove2me | solution 1 for DetDLP.m89_four_call_word_composition
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T19:37:44.549265+00:00
-- url     : https://prove2.me/submissions/124a8c54-477b-40af-bbc0-8ece46cc18c3

import Mathlib
import Definitions.Def_DetDLP_Machine
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open DetDLP DetDLP.MachineComposition
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.M89FourCall

section TapeAndLengthBounds

/-- Canonical binary tape with `revLeft` on the left (headward order) and `right`
starting at the current head position. -/
def bTape (revLeft right : List Bool) : Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.mk (revLeft.map some))
    (Turing.ListBlank.mk (right.map some))

@[simp] theorem bTape_nil_left (w : List Bool) :
    bTape [] w = Turing.Tape.mk₁ (w.map some) := rfl

@[simp] theorem bTape_head_nil (L : List Bool) :
    (bTape L []).head = none := rfl

@[simp] theorem bTape_head_cons (L : List Bool) (b : Bool) (R : List Bool) :
    (bTape L (b :: R)).head = some b := rfl

theorem bTape_write_nil (L : List Bool) (b : Bool) :
    (bTape L []).write (some b) = bTape L [b] := by
  simp [bTape, Turing.Tape.write_mk']

theorem bTape_write_cons (L : List Bool) (a b : Bool) (R : List Bool) :
    (bTape L (a :: R)).write (some b) = bTape L (b :: R) := by
  simp [bTape, Turing.Tape.write_mk']

theorem bTape_move_right_cons (L : List Bool) (b : Bool) (R : List Bool) :
    (bTape L (b :: R)).move .right = bTape (b :: L) R := by
  simp [bTape, Turing.Tape.move_right_mk']

theorem bTape_move_left_cons (L : List Bool) (b : Bool) (R : List Bool) :
    (bTape (b :: L) R).move .left = bTape L (b :: R) := by
  simp [bTape, Turing.Tape.move_left_mk']

theorem bTape_move_left_nil_right (w : List Bool) :
    ((bTape [] w).move .left).head = none ∧
      ((bTape [] w).move .left).move .right = bTape [] w := by
  unfold bTape
  rw [Turing.Tape.move_left_mk']
  simp only [List.map_nil]
  have hblank : (Turing.ListBlank.mk ([] : List (Option Bool))).head = none := rfl
  have htail : (Turing.ListBlank.mk ([] : List (Option Bool))).tail = Turing.ListBlank.mk [] := rfl
  rw [hblank, htail]
  constructor
  · rfl
  · rw [Turing.Tape.move_right_mk']
    simp only [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    have hc : (Turing.ListBlank.mk ([] : List (Option Bool))).cons (none : Option Bool) =
        Turing.ListBlank.mk [] := by
      have hd : (default : Option Bool) = none := rfl
      simpa [hd] using Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk ([] : List (Option Bool)))
    rw [hc]

private theorem nth_tape_mk₁_ne_none {l : List Bool} {z : ℤ}
    (h : (Turing.Tape.mk₁ (l.map some)).nth z ≠ none) :
    0 ≤ z ∧ z.toNat < l.length := by
  cases z with
  | ofNat n =>
    change (Turing.Tape.mk₁ (l.map some)).nth (n : ℤ) ≠ none at h
    rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk] at h
    refine ⟨Int.natCast_nonneg n, ?_⟩
    by_contra hge
    have hle : (l.map some).length ≤ n := by simpa using Nat.le_of_not_lt hge
    exact h (List.getI_eq_default (l.map some) hle)
  | negSucc n =>
    exfalso
    apply h
    change (Turing.ListBlank.mk ([] : List (Option Bool))).nth n = none
    rw [Turing.ListBlank.nth_mk]
    rfl

private theorem nth_tape_mk₁_get {l : List Bool} {n : ℕ} (hn : n < l.length) :
    (Turing.Tape.mk₁ (l.map some)).nth (n : ℤ) = some l[n] := by
  rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk,
    List.getI_eq_getElem _ (by simpa using hn)]
  simp

/-- Absolute cell support stays within `[lower, upper]` along every reachable state. -/
def TapeSupportBound {M : PrimitiveMachine} (c : LocatedCfg M) : Prop :=
  ∀ (i : Fin M.tapeCount) (z : ℤ),
    (c.config.tapes i).nth (z - c.position i) ≠ none →
      c.lower i ≤ z ∧ z ≤ c.upper i

theorem tapeSupportBound_init (M : PrimitiveMachine) (input : List Bool) :
    TapeSupportBound (locatedInit M input) := by
  intro i z hz
  simp only [locatedInit, sub_zero, Int.ofNat_eq_natCast] at hz ⊢
  by_cases hi : i = M.inputTape
  · subst hi
    simp only [PrimitiveMachine.init, ↓reduceIte] at hz ⊢
    rcases nth_tape_mk₁_ne_none hz with ⟨hz0, hlt⟩
    exact ⟨hz0, by omega⟩
  · exfalso
    simp only [PrimitiveMachine.init, hi, ↓reduceIte] at hz
    rcases nth_tape_mk₁_ne_none (l := []) hz with ⟨_, hlt⟩
    simp at hlt

theorem tapeSupportBound_step {M : PrimitiveMachine} {c d : LocatedCfg M}
    (hw : LocatedWellFormed c) (hs : TapeSupportBound c)
    (hstep : locatedStep M c = some d) : TapeSupportBound d := by
  unfold locatedStep at hstep
  cases hcstep : M.step c.config with
  | none => simp [hcstep] at hstep
  | some cfg' =>
    have hd : c.monitor cfg' = d := by simpa [hcstep] using hstep
    subst d
    rcases c with ⟨⟨st, tapes⟩, pos, low, upp⟩
    cases st with
    | inl b => simp [PrimitiveMachine.step] at hcstep
    | inr q =>
      simp only [PrimitiveMachine.step] at hcstep
      cases htr : M.transition q (tapes (M.scan q)).head with
      | inl ans =>
        simp only [htr, Option.some.injEq] at hcstep
        subst hcstep
        intro i z hz
        simpa [LocatedCfg.monitor, htr] using hs i z (by simpa [LocatedCfg.monitor, htr] using hz)
      | inr qa =>
        rcases qa with ⟨q', act⟩
        simp only [htr, Option.some.injEq] at hcstep
        subst hcstep
        intro i z hz
        by_cases hi : i = M.scan q
        · subst i
          cases act with
          | move dir =>
            cases dir with
            | left =>
              simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_self,
                headDisplacement] at hz ⊢
              rw [Turing.Tape.move_left_nth] at hz
              have hz' : (tapes (M.scan q)).nth (z - pos (M.scan q)) ≠ none := by
                simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
              rcases hs (M.scan q) z hz' with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
            | right =>
              simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_self,
                headDisplacement] at hz ⊢
              rw [Turing.Tape.move_right_nth] at hz
              have hz' : (tapes (M.scan q)).nth (z - pos (M.scan q)) ≠ none := by
                simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
              rcases hs (M.scan q) z hz' with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
          | write sym =>
            simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_self,
              headDisplacement, add_zero] at hz ⊢
            rw [Turing.Tape.write_nth] at hz
            by_cases hzp : z = pos (M.scan q)
            · subst z
              rcases hw (M.scan q) with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
            · have hsub : z - pos (M.scan q) ≠ 0 := sub_ne_zero.mpr hzp
              simp only [hsub, ↓reduceIte] at hz
              rcases hs (M.scan q) z hz with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
        · simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_of_ne hi] at hz ⊢
          exact hs i z hz

private theorem tapeSupportBound_trace_aux {M : PrimitiveMachine} {a c : LocatedCfg M} {n : ℕ}
    (hw : LocatedWellFormed a) (hs : TapeSupportBound a)
    (ht : Computation.Trace (locatedStep M) n a c) :
    TapeSupportBound c := by
  induction ht with
  | refl => exact hs
  | cons hstep _ ih =>
    exact ih (locatedWellFormed_step hw hstep) (tapeSupportBound_step hw hs hstep)

theorem tapeSupportBound_trace {M : PrimitiveMachine} {input : List Bool}
    {n : ℕ} {c : LocatedCfg M} (ht : Computation.Trace (locatedStep M) n (locatedInit M input) c) :
    TapeSupportBound c :=
  tapeSupportBound_trace_aux (locatedWellFormed_init M input) (tapeSupportBound_init M input) ht

theorem runsWithin_input_length_le {M : PrimitiveMachine} {out : Fin M.tapeCount}
    {input output : List Bool} {τ σ : ℝ} (h : RunsWithin M out input output τ σ) :
    (input.length : ℝ) ≤ σ := by
  rcases h with ⟨n, c, _, _, _, _, hs⟩
  have h0 := hs 0 (locatedInit M input) (Nat.zero_le n) (.refl _)
  have hlen : input.length ≤ visitedSpace (locatedInit M input) := by
    by_cases h0len : input.length = 0
    · omega
    · have hmem : M.inputTape ∈ (Finset.univ : Finset (Fin M.tapeCount)) := Finset.mem_univ _
      have hterm := Finset.single_le_sum (f := fun i : Fin M.tapeCount =>
        ((locatedInit M input).upper i - (locatedInit M input).lower i + 1).toNat)
        (fun _ _ => Nat.zero_le _) hmem
      have hval : ((locatedInit M input).upper M.inputTape - (locatedInit M input).lower M.inputTape + 1).toNat =
          input.length := by
        simp only [locatedInit, ↓reduceIte, Int.ofNat_eq_natCast]
        omega
      change ((locatedInit M input).upper M.inputTape - (locatedInit M input).lower M.inputTape + 1).toNat ≤
        visitedSpace (locatedInit M input) at hterm
      omega
  exact le_trans (by exact_mod_cast hlen) h0

theorem runsWithin_output_length_le {M : PrimitiveMachine} {out : Fin M.tapeCount}
    {input output : List Bool} {τ σ : ℝ} (h : RunsWithin M out input output τ σ) :
    (output.length : ℝ) ≤ σ := by
  rcases h with ⟨n, c, htr, _, hout, _, hs⟩
  have hbound := hs n c le_rfl htr
  have hsup := tapeSupportBound_trace htr
  have hlen : output.length ≤ visitedSpace c := by
    by_cases h0len : output.length = 0
    · omega
    · have h0lt : 0 < output.length := Nat.pos_of_ne_zero h0len
      have hlt : output.length - 1 < output.length := by omega
      have hne0 : (c.config.tapes out).nth (0 : ℤ) ≠ none := by
        rw [hout, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, nth_tape_mk₁_get h0lt]
        simp
      have hne1 : (c.config.tapes out).nth ((output.length - 1 : ℕ) : ℤ) ≠ none := by
        rw [hout, nth_tape_mk₁_get hlt]
        simp
      have hl0 := (hsup out (c.position out) (by simpa using hne0)).1
      have hu1 := (hsup out (c.position out + (output.length - 1 : ℕ))
        (by simpa using hne1)).2
      have hspan : output.length ≤ (c.upper out - c.lower out + 1).toNat := by omega
      have hterm := Finset.single_le_sum (f := fun i : Fin M.tapeCount =>
        (c.upper i - c.lower i + 1).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ out)
      exact hspan.trans hterm
  exact le_trans (by exact_mod_cast hlen) hbound

end TapeAndLengthBounds

section SequentialComposition

private theorem loc_ext {M : PrimitiveMachine} {c d : LocatedCfg M}
    (hc : c.config = d.config) (hp : c.position = d.position)
    (hl : c.lower = d.lower) (hu : c.upper = d.upper) : c = d := by
  cases c; cases d; simp_all

private theorem cfg_ext' {M : PrimitiveMachine} {c d : M.Cfg}
    (hs : c.state = d.state) (ht : c.tapes = d.tapes) : c = d := by
  cases c; cases d; simp_all

private theorem loc_ext_prog {N : ℕ} {P : Program N} {inTape : Fin N}
    {c d : LocatedCfg (P.machine inTape)}
    (hs : c.config.state = d.config.state)
    (ht : ∀ j : Fin N, c.config.tapes j = d.config.tapes j)
    (hp : ∀ j : Fin N, c.position j = d.position j)
    (hl : ∀ j : Fin N, c.lower j = d.lower j)
    (hu : ∀ j : Fin N, c.upper j = d.upper j) : c = d :=
  loc_ext (cfg_ext' hs (funext ht)) (funext hp) (funext hl) (funext hu)

/-- Sequential composition of two `Program N` routines sharing `inTape`. -/
def seqProg {N : ℕ} (inTape : Fin N) (P₁ P₂ : Program N) : Program N :=
  Program.ofMachine (thenMachine (P₁.machine inTape) P₂)

theorem seqProg_trace {N : ℕ} (inTape : Fin N) (P₁ P₂ : Program N)
    {t0 t1 t2 : Fin N → Turing.Tape (Option Bool)}
    {p0 l0 u0 p1 l1 u1 p2 l2 u2 : Fin N → ℤ}
    {n1 n2 : ℕ} {ans1 ans2 : Bool}
    (hw0 : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (h1 : Computation.Trace (locatedStep (P₁.machine inTape)) n1
      ⟨⟨.inr P₁.start, t0⟩, p0, l0, u0⟩ ⟨⟨.inl ans1, t1⟩, p1, l1, u1⟩)
    (h2 : Computation.Trace (locatedStep (P₂.machine inTape)) n2
      ⟨⟨.inr P₂.start, t1⟩, p1, l1, u1⟩ ⟨⟨.inl ans2, t2⟩, p2, l2, u2⟩) :
    Computation.Trace (locatedStep ((seqProg inTape P₁ P₂).machine inTape)) (n1 + n2)
      ⟨⟨.inr (seqProg inTape P₁ P₂).start, t0⟩, p0, l0, u0⟩
      ⟨⟨.inl ans2, t2⟩, p2, l2, u2⟩ := by
  let a₀ : LocatedCfg (P₁.machine inTape) := ⟨⟨.inr P₁.start, t0⟩, p0, l0, u0⟩
  let b₁ : LocatedCfg (P₁.machine inTape) := ⟨⟨.inl ans1, t1⟩, p1, l1, u1⟩
  let b₂ : LocatedCfg (P₂.machine inTape) := ⟨⟨.inl ans2, t2⟩, p2, l2, u2⟩
  have hwa : LocatedWellFormed a₀ := hw0
  have ha_seg : Segment (P₁.machine inTape) a₀ b₁ n1 (visitedSpace b₁) :=
    segment_iff_final_space.2 ⟨h1, le_rfl⟩
  have hb_seg : Segment (P₂.machine inTape) (restartCfg (P₁.machine inTape) P₂ b₁) b₂ n2
      (visitedSpace b₂) :=
    segment_iff_final_space.2 ⟨h2, le_rfl⟩
  exact (thenMachine_segments (P₁.machine inTape) P₂ hwa ha_seg ⟨ans1, rfl⟩ hb_seg).1

def spanSum {N : ℕ} (l u : Fin N → ℤ) : ℕ :=
  ∑ i : Fin N, (u i - l i + 1).toNat

@[simp] theorem visitedSpace_mk {M : PrimitiveMachine} (st : Bool ⊕ Fin M.stateCount)
    (t : Fin M.tapeCount → Turing.Tape (Option Bool)) (p l u : Fin M.tapeCount → ℤ) :
    visitedSpace (⟨⟨st, t⟩, p, l, u⟩ : LocatedCfg M) = spanSum l u := rfl

theorem spanSum_le_add {N : ℕ} (l0 u0 l1 u1 : Fin N → ℤ) (dec inc : Fin N → ℕ)
    (hl : ∀ j, l0 j - dec j ≤ l1 j) (hu : ∀ j, u1 j ≤ u0 j + inc j)
    (hw0 : ∀ j, l0 j ≤ u0 j) :
    spanSum l1 u1 ≤ spanSum l0 u0 + ∑ j : Fin N, (inc j + dec j) := by
  unfold spanSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hlj := hl j
  have huj := hu j
  have hwj := hw0 j
  omega

private theorem locatedInit_tapes {N : ℕ} (P : Program N) (inTape : Fin N) (input : List Bool)
    (j : Fin N) :
    (locatedInit (P.machine inTape) input).config.tapes j =
      if j = inTape then bTape [] input else bTape [] [] := rfl

private theorem locatedInit_upper {N : ℕ} (P : Program N) (inTape : Fin N) (input : List Bool)
    (j : Fin N) :
    (locatedInit (P.machine inTape) input).upper j =
      if j = inTape then ((input.length - 1 : ℕ) : ℤ) else 0 := by
  simp only [locatedInit, Int.ofNat_eq_natCast]; rfl

end SequentialComposition

section SubmachineEmbedding

/-- Embed a `PrimitiveMachine` `P` into a `N`-tape `Program N` via injective `f`. -/
def embedProgram (P : PrimitiveMachine) {N : ℕ} (f : Fin P.tapeCount → Fin N) : Program N where
  stateCount := P.stateCount
  start := P.start
  scan q := f (P.scan q)
  transition := P.transition

private noncomputable def embCfg {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (inTape : Fin N) (baseTapes : Fin N → Turing.Tape (Option Bool)) (c : P.Cfg) :
    ((embedProgram P f).machine inTape).Cfg where
  state := c.state
  tapes j := by
    classical
    exact if h : ∃ i, f i = j then c.tapes h.choose else baseTapes j

private noncomputable def embLoc {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (inTape : Fin N) (base : LocatedCfg ((embedProgram P f).machine inTape)) (c : LocatedCfg P) :
    LocatedCfg ((embedProgram P f).machine inTape) where
  config := embCfg P f inTape base.config.tapes c.config
  position j := by
    classical
    exact if h : ∃ i, f i = j then base.position j + c.position h.choose else base.position j
  lower j := by
    classical
    exact if h : ∃ i, f i = j then min (base.lower j) (base.position j + c.lower h.choose)
      else base.lower j
  upper j := by
    classical
    exact if h : ∃ i, f i = j then max (base.upper j) (base.position j + c.upper h.choose)
      else base.upper j

private theorem embCfg_apply {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (inTape : Fin N)
    (baseTapes : Fin N → Turing.Tape (Option Bool)) (c : P.Cfg) (i : Fin P.tapeCount) :
    (embCfg P f inTape baseTapes c).tapes (f i) = c.tapes i := by
  classical
  have h : ∃ k, f k = f i := ⟨i, rfl⟩
  simp only [embCfg, dif_pos h]
  rw [hf h.choose_spec]

private theorem embCfg_outside {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (inTape : Fin N) (baseTapes : Fin N → Turing.Tape (Option Bool)) (c : P.Cfg) {j : Fin N}
    (hj : ¬ ∃ i, f i = j) :
    (embCfg P f inTape baseTapes c).tapes j = baseTapes j := by
  classical
  simp only [embCfg, dif_neg hj]

private theorem embLoc_pos_apply {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (inTape : Fin N)
    (base : LocatedCfg ((embedProgram P f).machine inTape))
    (c : LocatedCfg P) (i : Fin P.tapeCount) :
    (embLoc P f inTape base c).position (f i) = base.position (f i) + c.position i := by
  classical
  have h : ∃ k, f k = f i := ⟨i, rfl⟩
  simp only [embLoc, dif_pos h]
  rw [hf h.choose_spec]

private theorem embLoc_lower_apply {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (inTape : Fin N)
    (base : LocatedCfg ((embedProgram P f).machine inTape))
    (c : LocatedCfg P) (i : Fin P.tapeCount) :
    (embLoc P f inTape base c).lower (f i) = min (base.lower (f i)) (base.position (f i) + c.lower i) := by
  classical
  have h : ∃ k, f k = f i := ⟨i, rfl⟩
  simp only [embLoc, dif_pos h]
  rw [hf h.choose_spec]

private theorem embLoc_upper_apply {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (inTape : Fin N)
    (base : LocatedCfg ((embedProgram P f).machine inTape))
    (c : LocatedCfg P) (i : Fin P.tapeCount) :
    (embLoc P f inTape base c).upper (f i) = max (base.upper (f i)) (base.position (f i) + c.upper i) := by
  classical
  have h : ∃ k, f k = f i := ⟨i, rfl⟩
  simp only [embLoc, dif_pos h]
  rw [hf h.choose_spec]

private theorem embLoc_tapes_apply {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (inTape : Fin N)
    (base : LocatedCfg ((embedProgram P f).machine inTape))
    (c : LocatedCfg P) (i : Fin P.tapeCount) :
    (embLoc P f inTape base c).config.tapes (f i) = c.config.tapes i :=
  embCfg_apply P f hf inTape base.config.tapes c.config i

private theorem embLoc_tapes_outside {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (inTape : Fin N) (base : LocatedCfg ((embedProgram P f).machine inTape))
    (c : LocatedCfg P) {j : Fin N} (hj : ¬ ∃ i, f i = j) :
    (embLoc P f inTape base c).config.tapes j = base.config.tapes j :=
  embCfg_outside P f inTape base.config.tapes c.config hj

private theorem locatedStep_inl_prog {N : ℕ} (P : Program N) (inTape : Fin N)
    (c : LocatedCfg (P.machine inTape))
    (q : Fin P.stateCount) (s : Fin N) (ans : Bool)
    (hq : c.config.state = .inr q)
    (hscan : P.scan q = s)
    (htr : P.transition q (c.config.tapes s).head = .inl ans) :
    locatedStep (P.machine inTape) c =
      some ⟨⟨.inl ans, c.config.tapes⟩, c.position, c.lower, c.upper⟩ := by
  rcases c with ⟨⟨st, tp⟩, ps, lw, up⟩
  simp only at hq
  subst hq
  subst hscan
  simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine, htr]

private theorem locatedStep_inr_prog {N : ℕ} (P : Program N) (inTape : Fin N)
    (c : LocatedCfg (P.machine inTape))
    (q q' : Fin P.stateCount) (s : Fin N) (act : Turing.TM0.Stmt (Option Bool))
    (hq : c.config.state = .inr q)
    (hscan : P.scan q = s)
    (htr : P.transition q (c.config.tapes s).head = .inr (q', act)) :
    let tp' := match act with
      | .move d => (c.config.tapes s).move d
      | .write sym => (c.config.tapes s).write sym
    let p' := c.position s + headDisplacement act
    locatedStep (P.machine inTape) c =
      some ⟨⟨.inr q', Function.update (fun k : Fin N => c.config.tapes k) s tp'⟩,
        Function.update (fun k : Fin N => c.position k) s p',
        Function.update (fun k : Fin N => c.lower k) s (min (c.lower s) p'),
        Function.update (fun k : Fin N => c.upper k) s (max (c.upper s) p')⟩ := by
  rcases c with ⟨⟨st, tp⟩, ps, lw, up⟩
  simp only at hq
  subst hq
  subst hscan
  dsimp only at htr
  rcases act with dir | sym <;>
  · simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine, htr,
      Sum.elim_inr, Option.map_some]

private theorem embLoc_step {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (inTape : Fin N)
    (base : LocatedCfg ((embedProgram P f).machine inTape))
    {c d : LocatedCfg P} (h : locatedStep P c = some d) :
    locatedStep ((embedProgram P f).machine inTape) (embLoc P f inTape base c) =
      some (embLoc P f inTape base d) := by
  unfold locatedStep at h ⊢
  cases hc : P.step c.config with
  | none => simp [hc] at h
  | some cfg' =>
    have hd : c.monitor cfg' = d := by simpa [hc] using h
    subst d
    rcases c with ⟨⟨st, tapes⟩, pos, low, upp⟩
    cases st with
    | inl b => simp [PrimitiveMachine.step] at hc
    | inr q =>
      simp only [PrimitiveMachine.step] at hc
      let c₀ : LocatedCfg P := ⟨⟨.inr q, tapes⟩, pos, low, upp⟩
      cases htr : P.transition q (tapes (P.scan q)).head with
      | inl ans =>
        simp only [htr, Option.some.injEq] at hc
        subst hc
        have hmonP : c₀.monitor ⟨.inl ans, tapes⟩ = ⟨⟨.inl ans, tapes⟩, pos, low, upp⟩ := by
          simp [c₀, LocatedCfg.monitor, htr]
        have htr' : (embedProgram P f).transition q
            ((embLoc P f inTape base c₀).config.tapes (f (P.scan q))).head = .inl ans := by
          change P.transition q ((embLoc P f inTape base c₀).config.tapes (f (P.scan q))).head =
            .inl ans
          rw [embLoc_tapes_apply P f hf]
          exact htr
        have hres := locatedStep_inl_prog (embedProgram P f) inTape (embLoc P f inTape base c₀)
          q (f (P.scan q)) ans rfl rfl htr'
        unfold locatedStep at hres
        change Option.map (embLoc P f inTape base c₀).monitor
            (((embedProgram P f).machine inTape).step (embLoc P f inTape base c₀).config) =
          some (embLoc P f inTape base (c₀.monitor ⟨.inl ans, tapes⟩))
        rw [hres, hmonP]
        rfl
      | inr qa =>
        rcases qa with ⟨q', act⟩
        simp only [htr, Option.some.injEq] at hc
        subst hc
        have htr' : (embedProgram P f).transition q
            ((embLoc P f inTape base c₀).config.tapes (f (P.scan q))).head = .inr (q', act) := by
          change P.transition q ((embLoc P f inTape base c₀).config.tapes (f (P.scan q))).head =
            .inr (q', act)
          rw [embLoc_tapes_apply P f hf]
          exact htr
        have hres := locatedStep_inr_prog (embedProgram P f) inTape (embLoc P f inTape base c₀)
          q q' (f (P.scan q)) act rfl rfl htr'
        unfold locatedStep at hres
        change Option.map (embLoc P f inTape base c₀).monitor
            (((embedProgram P f).machine inTape).step (embLoc P f inTape base c₀).config) =
          some (embLoc P f inTape base (c₀.monitor ⟨.inr q', _⟩))
        rw [hres]
        simp only [c₀, LocatedCfg.monitor, htr, Sum.elim_inr]
        refine congrArg some ?_
        apply loc_ext_prog
        · rfl
        · intro j
          dsimp only
          by_cases hj : j = f (P.scan q)
          · subst hj
            rw [Function.update_self]
            cases act <;> dsimp only
            · simp [embLoc_tapes_apply P f hf]
            · simp [embLoc_tapes_apply P f hf]
          · rw [Function.update_of_ne hj]
            by_cases ex : ∃ i, f i = j
            · rcases ex with ⟨i, rfl⟩
              rw [embLoc_tapes_apply P f hf, embLoc_tapes_apply P f hf]
              have hne : i ≠ P.scan q := fun h => hj (by rw [h])
              simp [hne]
            · rw [embLoc_tapes_outside P f inTape base _ ex,
                embLoc_tapes_outside P f inTape base _ ex]
        · intro j
          dsimp only
          by_cases hj : j = f (P.scan q)
          · subst hj
            rw [Function.update_self, embLoc_pos_apply P f hf, embLoc_pos_apply P f hf]
            simp [add_assoc]
          · rw [Function.update_of_ne hj]
            by_cases ex : ∃ i, f i = j
            · rcases ex with ⟨i, rfl⟩
              rw [embLoc_pos_apply P f hf, embLoc_pos_apply P f hf]
              have hne : i ≠ P.scan q := fun h => hj (by rw [h])
              simp [hne]
            · classical
              simp [c₀, embLoc, dif_neg ex]
        · intro j
          dsimp only
          by_cases hj : j = f (P.scan q)
          · subst hj
            rw [Function.update_self, embLoc_lower_apply P f hf, embLoc_pos_apply P f hf,
              embLoc_lower_apply P f hf]
            simp only [c₀, Function.update_self]
            omega
          · rw [Function.update_of_ne hj]
            by_cases ex : ∃ i, f i = j
            · rcases ex with ⟨i, rfl⟩
              rw [embLoc_lower_apply P f hf, embLoc_lower_apply P f hf]
              have hne : i ≠ P.scan q := fun h => hj (by rw [h])
              simp [c₀, hne]
            · classical
              simp [c₀, embLoc, dif_neg ex]
        · intro j
          dsimp only
          by_cases hj : j = f (P.scan q)
          · subst hj
            rw [Function.update_self, embLoc_upper_apply P f hf, embLoc_pos_apply P f hf,
              embLoc_upper_apply P f hf]
            simp only [c₀, Function.update_self]
            omega
          · rw [Function.update_of_ne hj]
            by_cases ex : ∃ i, f i = j
            · rcases ex with ⟨i, rfl⟩
              rw [embLoc_upper_apply P f hf, embLoc_upper_apply P f hf]
              have hne : i ≠ P.scan q := fun h => hj (by rw [h])
              simp [c₀, hne]
            · classical
              simp [c₀, embLoc, dif_neg ex]

/-- Simulate a full `RunsWithin` certificate of `P` inside `embedProgram P f`. -/
theorem embedProgram_run {N : ℕ} (P : PrimitiveMachine) (f : Fin P.tapeCount → Fin N)
    (hf : Function.Injective f) (outP : Fin P.tapeCount) {input output : List Bool} {τ σ : ℝ}
    (inTape : Fin N)
    (hrun : RunsWithin P outP input output τ σ)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw0 : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (ht_in : t0 (f P.inputTape) = bTape [] input)
    (ht_blank : ∀ i, i ≠ P.inputTape → t0 (f i) = bTape [] [])
    (hp0 : ∀ i, p0 (f i) = 0)
    (hu_in : ((input.length - 1 : ℕ) : ℤ) ≤ u0 (f P.inputTape)) :
    ∃ n ans t1 p1 l1 u1,
      Computation.Trace (locatedStep ((embedProgram P f).machine inTape)) n
        ⟨⟨.inr (embedProgram P f).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl ans, t1⟩, p1, l1, u1⟩ ∧
      (n : ℝ) ≤ τ ∧
      (∀ j, l1 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      ((spanSum l1 u1 : ℝ) ≤ (spanSum l0 u0 : ℝ) + σ) ∧
      t1 (f outP) = bTape [] output ∧
      (∀ j, (∀ i, f i ≠ j) → t1 j = t0 j ∧ p1 j = p0 j ∧ l1 j = l0 j ∧ u1 j = u0 j) ∧
      (∀ j, l1 j ≤ l0 j ∧ u0 j ≤ u1 j) := by
  classical
  rcases (runsWithin_iff_final_space _ _ _ _ _ _).1 hrun with
    ⟨n, cP, htr, ⟨ans, hst⟩, hout, hn_le, hs_le⟩
  let base : LocatedCfg ((embedProgram P f).machine inTape) :=
    ⟨⟨.inr (embedProgram P f).start, t0⟩, p0, l0, u0⟩
  have hbase_eq : embLoc P f inTape base (locatedInit P input) = base := by
    apply loc_ext
    · apply cfg_ext'
      · rfl
      · change (fun j : Fin N => (embLoc P f inTape base (locatedInit P input)).config.tapes j) =
          (fun j : Fin N => t0 j)
        funext j
        by_cases ex : ∃ i, f i = j
        · rcases ex with ⟨i, rfl⟩
          change (embCfg P f inTape t0 (locatedInit P input).config).tapes (f i) = t0 (f i)
          rw [embCfg_apply P f hf]
          by_cases hi : i = P.inputTape
          · subst hi; simp [locatedInit, PrimitiveMachine.init, ht_in]
          · simp [locatedInit, PrimitiveMachine.init, hi, ht_blank i hi]
        · exact embCfg_outside P f inTape t0 _ ex
    · change (fun j : Fin N => (embLoc P f inTape base (locatedInit P input)).position j) =
        (fun j : Fin N => p0 j)
      funext j
      by_cases ex : ∃ i, f i = j
      · rcases ex with ⟨i, rfl⟩
        rw [embLoc_pos_apply P f hf]
        simp [base, locatedInit]
      · simp [embLoc, dif_neg ex, base]
    · change (fun j : Fin N => (embLoc P f inTape base (locatedInit P input)).lower j) =
        (fun j : Fin N => l0 j)
      funext j
      by_cases ex : ∃ i, f i = j
      · rcases ex with ⟨i, rfl⟩
        have h : ∃ k, f k = f i := ⟨i, rfl⟩
        simp only [embLoc, dif_pos h, base]
        rw [hf h.choose_spec]
        have hl : l0 (f i) ≤ p0 (f i) := (hw0 (f i)).1
        simp [locatedInit, hl]
      · simp [embLoc, dif_neg ex, base]
    · change (fun j : Fin N => (embLoc P f inTape base (locatedInit P input)).upper j) =
        (fun j : Fin N => u0 j)
      funext j
      by_cases ex : ∃ i, f i = j
      · rcases ex with ⟨i, rfl⟩
        have h : ∃ k, f k = f i := ⟨i, rfl⟩
        simp only [embLoc, dif_pos h, base]
        rw [hf h.choose_spec]
        by_cases hi : i = P.inputTape
        · subst hi
          simp only [locatedInit, ↓reduceIte, hp0, zero_add, Int.ofNat_eq_natCast]
          exact max_eq_left hu_in
        · have hu : 0 ≤ u0 (f i) := by rw [← hp0 i]; exact (hw0 (f i)).2
          simp [locatedInit, hi, hp0 i, hu]
      · simp [embLoc, dif_neg ex, base]
  have hmap := Trace.map (embLoc P f inTape base) (fun _ _ => embLoc_step P f hf inTape base) htr
  rw [hbase_eq] at hmap
  let endCfg := embLoc P f inTape base cP
  have hwf_base : LocatedWellFormed base := hw0
  have hwf_end : LocatedWellFormed endCfg := locatedWellFormed_trace hwf_base hmap
  have hoc : OriginCovered cP := originCovered_trace (originCovered_init P input) htr
  have hspan_term : ∀ j : Fin N,
      (endCfg.upper j - endCfg.lower j + 1).toNat ≤
        (u0 j - l0 j + 1).toNat +
          if h : ∃ i, f i = j then (cP.upper h.choose - cP.lower h.choose + 1).toNat else 0 := by
    intro j
    by_cases ex : ∃ i, f i = j
    · rcases ex with ⟨i, rfl⟩
      have h : ∃ k, f k = f i := ⟨i, rfl⟩
      simp only [dif_pos h, endCfg, embLoc]
      rw [hf h.choose_spec]
      have h0 := hw0 (f i)
      have hc := hoc i
      have hp : p0 (f i) = 0 := hp0 i
      dsimp [base] at h0 hc hp ⊢
      omega
    · simp only [endCfg, embLoc, dif_neg ex, add_zero, base, le_refl]
  have hspace_nat : spanSum endCfg.lower endCfg.upper ≤
      spanSum l0 u0 + visitedSpace cP := by
    unfold spanSum visitedSpace
    calc ∑ j : Fin N, (endCfg.upper j - endCfg.lower j + 1).toNat
        ≤ ∑ j : Fin N, ((u0 j - l0 j + 1).toNat +
            if h : ∃ i, f i = j then (cP.upper h.choose - cP.lower h.choose + 1).toNat else 0) :=
          Finset.sum_le_sum fun j _ => hspan_term j
      _ = spanSum l0 u0 +
            ∑ j : Fin N, (if h : ∃ i, f i = j then
              (cP.upper h.choose - cP.lower h.choose + 1).toNat else 0) :=
          Finset.sum_add_distrib
      _ = spanSum l0 u0 +
            ∑ i : Fin P.tapeCount, (cP.upper i - cP.lower i + 1).toNat := by
          congr 1
          have himg : Finset.image f Finset.univ ⊆ (Finset.univ : Finset (Fin N)) :=
            Finset.subset_univ _
          rw [← Finset.sum_subset himg]
          · rw [Finset.sum_image (f := fun j =>
              if h : ∃ i, f i = j then (cP.upper h.choose - cP.lower h.choose + 1).toNat else 0)
              (fun i₁ _ i₂ _ h => hf h)]
            apply Finset.sum_congr rfl
            intro i _
            have h : ∃ k, f k = f i := ⟨i, rfl⟩
            rw [dif_pos h, hf h.choose_spec]
          · intro j _ hnot
            have hnex : ¬ ∃ i, f i = j := fun ⟨i, hi⟩ =>
              hnot (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩)
            simp [dif_neg hnex]
  have hst_end : endCfg.config.state =
      (.inl ans : Bool ⊕ Fin ((embedProgram P f).machine inTape).stateCount) := by
    simpa [endCfg, embLoc, embCfg, embedProgram, Program.machine] using hst
  have hspace_R : (spanSum endCfg.lower endCfg.upper : ℝ) ≤
      (spanSum l0 u0 : ℝ) + (visitedSpace cP : ℝ) := by
    exact_mod_cast hspace_nat
  have hcfg_eq : endCfg =
      ⟨⟨.inl ans, endCfg.config.tapes⟩, endCfg.position, endCfg.lower, endCfg.upper⟩ :=
    loc_ext (cfg_ext' hst_end rfl) rfl rfl rfl
  refine ⟨n, ans, endCfg.config.tapes, endCfg.position, endCfg.lower, endCfg.upper,
    ?_, hn_le, hwf_end, by linarith [hs_le, hspace_R], ?_, ?_, ?_⟩
  · rw [← hcfg_eq]; exact hmap
  · change (embCfg P f inTape t0 cP.config).tapes (f outP) = bTape [] output
    rw [embCfg_apply P f hf, hout]
    rfl
  · intro j hj
    have hnex : ¬ ∃ i, f i = j := fun ⟨i, hi⟩ => hj i hi
    simp only [endCfg, embLoc, embCfg, dif_neg hnex, base]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · intro j
    by_cases ex : ∃ i, f i = j
    · simp only [endCfg, embLoc, dif_pos ex, base]
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    · simp only [endCfg, embLoc, dif_neg ex, base]
      exact ⟨le_rfl, le_rfl⟩

end SubmachineEmbedding

section TapeRoutines

private theorem step_write {N : ℕ} (P : Program N) (inTape : Fin N)
    (q q' : Fin P.stateCount) (sym : Option Bool) (s : Fin N)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : l0 s ≤ p0 s ∧ p0 s ≤ u0 s)
    (hscan : P.scan q = s)
    (htr : P.transition q (t0 s).head = .inr (q', .write sym)) :
    locatedStep (P.machine inTape) ⟨⟨.inr q, t0⟩, p0, l0, u0⟩ =
      some ⟨⟨.inr q', Function.update t0 s ((t0 s).write sym)⟩, p0, l0, u0⟩ := by
  subst hscan
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine,
    Sum.elim_inr, htr, Option.map_some, headDisplacement, add_zero]
  rw [min_eq_left hw.1, max_eq_left hw.2]
  simp

private theorem step_move_right {N : ℕ} (P : Program N) (inTape : Fin N)
    (q q' : Fin P.stateCount) (s : Fin N)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : l0 s ≤ p0 s ∧ p0 s ≤ u0 s)
    (hscan : P.scan q = s)
    (htr : P.transition q (t0 s).head = .inr (q', .move .right)) :
    locatedStep (P.machine inTape) ⟨⟨.inr q, t0⟩, p0, l0, u0⟩ =
      some ⟨⟨.inr q', Function.update t0 s ((t0 s).move .right)⟩,
        Function.update p0 s (p0 s + 1),
        l0,
        Function.update u0 s (max (u0 s) (p0 s + 1))⟩ := by
  subst hscan
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine,
    Sum.elim_inr, htr, Option.map_some, headDisplacement]
  have hl : min (l0 (P.scan q)) (p0 (P.scan q) + 1) = l0 (P.scan q) :=
    min_eq_left (le_trans hw.1 (by omega))
  rw [hl, Function.update_eq_self]

private theorem step_move_left {N : ℕ} (P : Program N) (inTape : Fin N)
    (q q' : Fin P.stateCount) (s : Fin N)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : l0 s ≤ p0 s ∧ p0 s ≤ u0 s)
    (hscan : P.scan q = s)
    (htr : P.transition q (t0 s).head = .inr (q', .move .left)) :
    locatedStep (P.machine inTape) ⟨⟨.inr q, t0⟩, p0, l0, u0⟩ =
      some ⟨⟨.inr q', Function.update t0 s ((t0 s).move .left)⟩,
        Function.update p0 s (p0 s - 1),
        Function.update l0 s (min (l0 s) (p0 s - 1)),
        u0⟩ := by
  subst hscan
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine,
    Sum.elim_inr, htr, Option.map_some, headDisplacement]
  have hu : max (u0 (P.scan q)) (p0 (P.scan q) + -1) = u0 (P.scan q) :=
    max_eq_left (le_trans (by omega) hw.2)
  rw [hu, Function.update_eq_self, show p0 (P.scan q) + -1 = p0 (P.scan q) - 1 from by omega]

private theorem step_halt {N : ℕ} (P : Program N) (inTape : Fin N)
    (q : Fin P.stateCount) (ans : Bool) (s : Fin N)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hscan : P.scan q = s)
    (htr : P.transition q (t0 s).head = .inl ans) :
    locatedStep (P.machine inTape) ⟨⟨.inr q, t0⟩, p0, l0, u0⟩ =
      some ⟨⟨.inl ans, t0⟩, p0, l0, u0⟩ := by
  subst hscan
  simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine, htr]

private abbrev s3 (k : ℕ) (hk : k < 3 := by decide) : Fin 3 := ⟨k, hk⟩
private abbrev s5 (k : ℕ) (hk : k < 5 := by decide) : Fin 5 := ⟨k, hk⟩
private abbrev s9 (k : ℕ) (hk : k < 9 := by decide) : Fin 9 := ⟨k, hk⟩
private abbrev s13 (k : ℕ) (hk : k < 13 := by decide) : Fin 13 := ⟨k, hk⟩

/-- Rewind tape `t` from `bTape w.reverse []` at position `w.length` back to `bTape [] w` at `0`. -/
def rewindProgram {N : ℕ} (t : Fin N) : Program N where
  stateCount := 3
  start := s3 0
  scan _ := t
  transition q sym :=
    match q.val with
    | 0 => .inr (s3 1, .move .left)
    | 1 => match sym with
      | some _ => .inr (s3 1, .move .left)
      | none => .inr (s3 2, .move .right)
    | _ => .inl true

private theorem rewind_loop {N : ℕ} (t inTape : Fin N) (rev R : List Bool)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (ht : t0 t = bTape rev R) (hr : R ≠ []) :
    Computation.Trace (locatedStep ((rewindProgram t).machine inTape)) (rev.length + 3)
      ⟨⟨.inr (s3 1), t0⟩, p0, l0, u0⟩
      ⟨⟨.inl true, Function.update t0 t (bTape [] (rev.reverse ++ R))⟩,
        Function.update p0 t (p0 t - rev.length),
        Function.update l0 t (min (l0 t) (p0 t - rev.length - 1)),
        u0⟩ := by
  induction rev generalizing R t0 p0 l0 with
  | nil =>
    cases R with
    | nil => exact (hr rfl).elim
    | cons b bs =>
      have hhead : (t0 t).head = some b := by rw [ht]; rfl
      have hs1 := step_move_left (rewindProgram t) inTape (s3 1) (s3 1) t t0 p0 l0 u0
        (hw t) rfl (by rw [hhead]; rfl)
      have hml := bTape_move_left_nil_right (b :: bs)
      let t_s1 := Function.update t0 t ((t0 t).move .left)
      let p_s1 := Function.update p0 t (p0 t - 1)
      let l_s1 := Function.update l0 t (min (l0 t) (p0 t - 1))
      let t_s2 := Function.update t_s1 t ((t_s1 t).move .right)
      let p_s2 := Function.update p_s1 t (p_s1 t + 1)
      let u_s2 := Function.update u0 t (max (u0 t) (p_s1 t + 1))
      have hupd_head : (t_s1 t).head = none := by
        dsimp [t_s1]; rw [Function.update_self, ht]; exact hml.1
      have hs2 := step_move_right (rewindProgram t) inTape (s3 1) (s3 2) t
        t_s1 p_s1 l_s1 u0
        (by dsimp [p_s1, l_s1]; simp only [Function.update_self]; exact ⟨min_le_right _ _, le_trans (by omega) (hw t).2⟩)
        rfl (by rw [hupd_head]; rfl)
      have hs3 := step_halt (rewindProgram t) inTape (s3 2) true t
        t_s2 p_s2 l_s1 u_s2 rfl rfl
      have htr : Computation.Trace (locatedStep ((rewindProgram t).machine inTape)) 3
          ⟨⟨.inr (s3 1), t0⟩, p0, l0, u0⟩
          ⟨⟨.inl true, t_s2⟩, p_s2, l_s1, u_s2⟩ :=
        .cons hs1 (.cons hs2 (.cons hs3 (.refl _)))
      have hu_eq : u_s2 = u0 := by
        have hmax : max (u0 t) (p_s1 t + 1) = u0 t := by
          dsimp [p_s1]; simp only [Function.update_self]; have := (hw t).2; omega
        dsimp [u_s2]; rw [hmax, Function.update_eq_self]
      have ht_eq : t_s2 = Function.update t0 t (bTape [] (b :: bs)) := by
        dsimp [t_s2, t_s1]
        rw [Function.update_idem]
        congr 1
        rw [Function.update_self, ht]
        exact hml.2
      have hp_eq : p_s2 = p0 := by
        dsimp [p_s2, p_s1]
        simp only [Function.update_self, Function.update_idem, sub_add_cancel, Function.update_eq_self]
      rw [ht_eq, hp_eq, hu_eq] at htr
      dsimp only [l_s1] at htr
      simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append,
        Nat.cast_zero, sub_zero]
      convert htr using 1
      apply loc_ext_prog
      · rfl
      · intro j; rfl
      · intro j
        dsimp only [Function.update]
        split_ifs with hj
        · subst hj; rfl
        · rfl
      · intro j; rfl
      · intro j; rfl
  | cons a rest ih =>
    cases R with
    | nil => exact (hr rfl).elim
    | cons b bs =>
      have hhead : (t0 t).head = some b := by rw [ht]; rfl
      have hs1 := step_move_left (rewindProgram t) inTape (s3 1) (s3 1) t t0 p0 l0 u0
        (hw t) rfl (by rw [hhead]; rfl)
      have hml := bTape_move_left_cons rest a (b :: bs)
      have hw' : ∀ j, Function.update l0 t (min (l0 t) (p0 t - 1)) j ≤
          Function.update p0 t (p0 t - 1) j ∧ Function.update p0 t (p0 t - 1) j ≤ u0 j := by
        intro j
        by_cases hj : j = t
        · subst hj; simp only [Function.update_self]; exact ⟨min_le_right _ _, by have := (hw j).2; omega⟩
        · simp only [Function.update_of_ne hj]; exact hw j
      have htail := ih (a :: b :: bs)
        (Function.update t0 t ((t0 t).move .left))
        (Function.update p0 t (p0 t - 1))
        (Function.update l0 t (min (l0 t) (p0 t - 1)))
        hw' (by simp [ht, hml]) (by simp)
      have htr := Computation.Trace.cons hs1 htail
      have hsteps : (rest.length + 3) + 1 = (a :: rest).length + 3 := by simp
      rw [hsteps] at htr
      convert htr using 1
      apply loc_ext_prog
      · rfl
      · intro j; by_cases hj : j = t
        · subst hj; simp [List.append_assoc]
        · simp [hj]
      · intro j; by_cases hj : j = t
        · subst hj; simp only [Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one]; omega
        · simp [hj]
      · intro j; by_cases hj : j = t
        · subst hj; simp only [Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one]; omega
        · simp [hj]
      · intro j; rfl

theorem rewindProgram_run {N : ℕ} (t inTape : Fin N) (w : List Bool)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (hl0 : l0 t ≤ 0)
    (ht : t0 t = bTape w.reverse [])
    (hp : p0 t = w.length) :
    ∃ t1 p1 l1 u1,
      Computation.Trace (locatedStep ((rewindProgram t).machine inTape)) (w.length + 3)
        ⟨⟨.inr (rewindProgram t).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l1, u1⟩ ∧
      t1 t = bTape [] w ∧
      p1 t = 0 ∧
      (∀ j : Fin N, j ≠ t → t1 j = t0 j ∧ p1 j = p0 j) ∧
      (∀ j : Fin N, l1 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      spanSum l1 u1 ≤ spanSum l0 u0 + 1 ∧
      (∀ j : Fin N, l1 j ≤ l0 j ∧ u0 j ≤ u1 j) := by
  have hs0 := step_move_left (rewindProgram t) inTape (s3 0) (s3 1) t t0 p0 l0 u0
    (hw t) rfl rfl
  cases hrev : w.reverse with
  | nil =>
    have hw_nil : w = [] := List.reverse_eq_nil_iff.mp hrev
    subst hw_nil
    have hml := bTape_move_left_nil_right []
    let t_s1 := Function.update t0 t ((t0 t).move .left)
    let p_s1 := Function.update p0 t (p0 t - 1)
    let l_s1 := Function.update l0 t (min (l0 t) (p0 t - 1))
    let t_s2 := Function.update t_s1 t ((t_s1 t).move .right)
    let p_s2 := Function.update p_s1 t (p_s1 t + 1)
    let u_s2 := Function.update u0 t (max (u0 t) (p_s1 t + 1))
    have ht' : t0 t = bTape [] [] := by simpa [List.reverse_nil] using ht
    have hupd_head : (t_s1 t).head = none := by
      dsimp [t_s1]; rw [Function.update_self, ht']; exact hml.1
    have hs1 := step_move_right (rewindProgram t) inTape (s3 1) (s3 2) t
      t_s1 p_s1 l_s1 u0
      (by dsimp [p_s1, l_s1]; simp only [Function.update_self]; exact ⟨min_le_right _ _, by have := (hw t).2; omega⟩)
      rfl (by rw [hupd_head]; rfl)
    have hs2 := step_halt (rewindProgram t) inTape (s3 2) true t t_s2 p_s2 l_s1 u_s2 rfl rfl
    have htr := Computation.Trace.cons hs0 (.cons hs1 (.cons hs2 (.refl _)))
    have ht_eq : t_s2 = Function.update t0 t (bTape [] []) := by
      dsimp [t_s2, t_s1]; rw [Function.update_idem]; congr 1; rw [Function.update_self, ht']; exact hml.2
    have hp_eq : p_s2 = Function.update p0 t 0 := by
      dsimp [p_s2, p_s1]; simp only [Function.update_self, Function.update_idem, hp]; simp
    have hu_eq : u_s2 = u0 := by
      have hmax : max (u0 t) (p_s1 t + 1) = u0 t := by
        dsimp [p_s1]; simp only [Function.update_self]; have := (hw t).2; omega
      dsimp [u_s2]; rw [hmax, Function.update_eq_self]
    rw [ht_eq, hp_eq, hu_eq] at htr
    dsimp only [l_s1] at htr
    refine ⟨Function.update t0 t (bTape [] []), Function.update p0 t 0,
      Function.update l0 t (min (l0 t) (p0 t - 1)), u0, htr, by simp, by simp,
      fun j hj => by simp [hj], ?_, ?_, ?_⟩
    · intro (j : Fin N)
      by_cases hj : j = t
      · rw [hj]; simp only [Function.update_self]
        have hp0 : p0 t = 0 := by simpa using hp
        exact ⟨le_trans (min_le_right _ _) (by omega), by have := (hw t).2; omega⟩
      · simp [hj, hw j]
    · have hs := spanSum_le_add l0 u0 (Function.update l0 t (min (l0 t) (p0 t - 1))) u0
        (fun j => if j = t then 1 else 0) (fun _ => 0)
        (fun j => by
          by_cases hj : j = t
          · rw [hj]; simp [hp]; omega
          · simp [hj])
        (fun _ => by simp) (fun j => le_trans (hw j).1 (hw j).2)
      have hsum : (∑ j : Fin N, (0 + if j = t then 1 else 0)) = 1 := by
        simp [Finset.sum_ite_eq']
      rw [hsum] at hs
      exact hs
    · intro (j : Fin N)
      by_cases hj : j = t
      · rw [hj]; simp
      · simp [hj]
  | cons a rest =>
    have hw_rev : w.reverse = a :: rest := hrev
    have hlen : rest.length + 1 = w.length := by
      have h := congrArg List.length hw_rev
      simpa using h.symm
    have hml : (t0 t).move .left = bTape rest [a] := by
      rw [ht, hw_rev, bTape_move_left_cons]
    have hw' : ∀ j, Function.update l0 t (min (l0 t) (p0 t - 1)) j ≤
        Function.update p0 t (p0 t - 1) j ∧ Function.update p0 t (p0 t - 1) j ≤ u0 j := by
      intro j
      by_cases hj : j = t
      · subst hj; simp only [Function.update_self]; exact ⟨min_le_right _ _, by have := (hw j).2; omega⟩
      · simp [hj, hw j]
    have htail := rewind_loop t inTape rest [a]
      (Function.update t0 t ((t0 t).move .left))
      (Function.update p0 t (p0 t - 1))
      (Function.update l0 t (min (l0 t) (p0 t - 1))) u0 hw'
      (by simp [hml]) (by simp)
    let t_fin : Fin N → Turing.Tape (Option Bool) := Function.update t0 t (bTape [] w)
    let p_fin : Fin N → ℤ := Function.update p0 t 0
    let l_fin : Fin N → ℤ := Function.update l0 t (min (l0 t) (-1))
    have htr0 := Computation.Trace.cons hs0 htail
    have hsteps : (rest.length + 3) + 1 = w.length + 3 := by omega
    rw [hsteps] at htr0
    change Computation.Trace (locatedStep ((rewindProgram t).machine inTape)) (w.length + 3)
        ⟨⟨.inr (rewindProgram t).start, t0⟩, p0, l0, u0⟩ _ at htr0
    have htr : Computation.Trace (locatedStep ((rewindProgram t).machine inTape)) (w.length + 3)
        ⟨⟨.inr (rewindProgram t).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t_fin⟩, p_fin, l_fin, u0⟩ := by
      convert htr0 using 1
      apply loc_ext_prog
      · rfl
      · intro j; by_cases hj : j = t
        · subst hj; simp only [t_fin, Function.update_self]
          have hrev_app : rest.reverse ++ [a] = (a :: rest).reverse := by simp
          rw [hrev_app, ← hw_rev, List.reverse_reverse]
        · simp [t_fin, hj]
      · intro j; by_cases hj : j = t
        · subst hj; simp only [p_fin, Function.update_self]; omega
        · simp [p_fin, hj]
      · intro j; by_cases hj : j = t
        · subst hj; simp only [l_fin, Function.update_self]; omega
        · simp [l_fin, hj]
      · intro j; rfl
    refine ⟨t_fin, p_fin, l_fin, u0, htr, by simp [t_fin], by simp [p_fin],
      fun j hj => by simp [t_fin, p_fin, hj], ?_, ?_, ?_⟩
    · intro j
      dsimp only [p_fin, l_fin]
      by_cases hj : j = t
      · subst hj; simp only [Function.update_self]
        exact ⟨le_trans (min_le_right _ _) (by norm_num), by have := (hw j).2; omega⟩
      · simp [hj, hw j]
    · dsimp only [l_fin]
      have hs := spanSum_le_add l0 u0 (Function.update l0 t (min (l0 t) (-1))) u0
        (fun j => if j = t then 1 else 0) (fun _ => 0)
        (fun j => by
          by_cases hj : j = t
          · subst hj; simp; exact le_min (by omega) (by omega)
          · simp [hj])
        (fun _ => by simp) (fun j => le_trans (hw j).1 (hw j).2)
      have hsum : (∑ j : Fin N, (0 + if j = t then 1 else 0)) = 1 := by
        simp [Finset.sum_ite_eq']
      rw [hsum] at hs
      exact hs
    · intro j
      dsimp only [l_fin]
      by_cases hj : j = t
      · subst hj; simp
      · simp [hj]

/-- Copy from `src` (`bTape L R`) onto `dst` (`bTape L' []`) moving strictly rightward. -/
def copy1Forward {N : ℕ} (src dst : Fin N) : Program N where
  stateCount := 5
  start := s5 0
  scan q := match q.val with | 0 => src | _ => dst
  transition q sym :=
    match q.val with
    | 0 => match sym with
      | none => .inl true
      | some false => .inr (s5 1, .move .right)
      | some true => .inr (s5 2, .move .right)
    | 1 => .inr (s5 3, .write (some false))
    | 3 => .inr (s5 0, .move .right)
    | 2 => .inr (s5 4, .write (some true))
    | _ => .inr (s5 0, .move .right)

theorem copy1Forward_run {N : ℕ} (src dst inTape : Fin N) (hsd : src ≠ dst)
    (L R L' : List Bool) (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (hsrc : t0 src = bTape L R) (hdst : t0 dst = bTape L' []) :
    ∃ t1 p1 u1,
      Computation.Trace (locatedStep ((copy1Forward src dst).machine inTape)) (3 * R.length + 1)
        ⟨⟨.inr (copy1Forward src dst).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ ∧
      t1 src = bTape (R.reverse ++ L) [] ∧
      t1 dst = bTape (R.reverse ++ L') [] ∧
      (∀ j, j ≠ src → j ≠ dst → t1 j = t0 j ∧ p1 j = p0 j ∧ u1 j = u0 j) ∧
      p1 src = p0 src + R.length ∧
      p1 dst = p0 dst + R.length ∧
      (∀ j, l0 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      (∀ j, u0 j ≤ u1 j) ∧
      spanSum l0 u1 ≤ spanSum l0 u0 + 2 * R.length := by
  induction R generalizing L L' t0 p0 u0 with
  | nil =>
    have hhead : (t0 src).head = none := by rw [hsrc]; rfl
    have hs := step_halt (copy1Forward src dst) inTape (s5 0) true src t0 p0 l0 u0 rfl
      (by rw [hhead]; rfl)
    refine ⟨t0, p0, u0, .cons hs (.refl _), by simpa using hsrc, by simpa using hdst,
      fun _ _ _ => ⟨rfl, rfl, rfl⟩, by simp, by simp, hw, fun _ => le_rfl, by simp⟩
  | cons b bs ih =>
    have hhead : (t0 src).head = some b := by rw [hsrc]; rfl
    let q1 : Fin 5 := if b then s5 2 else s5 1
    let q2 : Fin 5 := if b then s5 4 else s5 3
    have hs0 : locatedStep ((copy1Forward src dst).machine inTape)
        ⟨⟨.inr (s5 0), t0⟩, p0, l0, u0⟩ =
        some ⟨⟨.inr q1, Function.update t0 src ((t0 src).move .right)⟩,
          Function.update p0 src (p0 src + 1), l0,
          Function.update u0 src (max (u0 src) (p0 src + 1))⟩ := by
      cases b <;> exact step_move_right (copy1Forward src dst) inTape (s5 0) _ src
        t0 p0 l0 u0 (hw src) rfl (by rw [hhead]; rfl)
    have hsrc1 : Function.update t0 src ((t0 src).move .right) src = bTape (b :: L) bs := by
      simp [hsrc, bTape_move_right_cons]
    have hdst1 : Function.update t0 src ((t0 src).move .right) dst = bTape L' [] := by
      simp [hsd.symm, hdst]
    have hw1_dst : l0 dst ≤ Function.update p0 src (p0 src + 1) dst ∧
        Function.update p0 src (p0 src + 1) dst ≤
          Function.update u0 src (max (u0 src) (p0 src + 1)) dst := by
      simp [hsd.symm, hw dst]
    have hscan1 : (copy1Forward src dst).scan q1 = dst := by cases b <;> rfl
    have hscan2 : (copy1Forward src dst).scan q2 = dst := by cases b <;> rfl
    have htr1 : (copy1Forward src dst).transition q1
        ((Function.update t0 src ((t0 src).move .right)) dst).head = .inr (q2, .write (some b)) := by
      cases b <;> rfl
    have hs1 := step_write (copy1Forward src dst) inTape q1 q2 (some b) dst _ _ _ _
      hw1_dst hscan1 htr1
    have htr2 : (copy1Forward src dst).transition q2
        ((Function.update (Function.update t0 src ((t0 src).move .right)) dst
          ((Function.update t0 src ((t0 src).move .right) dst).write (some b))) dst).head =
        .inr (s5 0, .move .right) := by
      cases b <;> rfl
    have hs2 := step_move_right (copy1Forward src dst) inTape q2 (s5 0) dst _ _ _ _
      hw1_dst hscan2 htr2
    have hsrc2 : Function.update (Function.update (Function.update t0 src ((t0 src).move .right)) dst
        ((Function.update t0 src ((t0 src).move .right) dst).write (some b))) dst
        ((Function.update (Function.update t0 src ((t0 src).move .right)) dst
          ((Function.update t0 src ((t0 src).move .right) dst).write (some b)) dst).move .right) src =
        bTape (b :: L) bs := by
      simp [hsd, hsrc, bTape_move_right_cons]
    have hdst3 : Function.update (Function.update (Function.update t0 src ((t0 src).move .right)) dst
        ((Function.update t0 src ((t0 src).move .right) dst).write (some b))) dst
        ((Function.update (Function.update t0 src ((t0 src).move .right)) dst
          ((Function.update t0 src ((t0 src).move .right) dst).write (some b)) dst).move .right) dst =
        bTape (b :: L') [] := by
      simp [Function.update_self, hdst1, bTape_write_nil, bTape_move_right_cons]
    have hw_next : ∀ j, l0 j ≤
        Function.update (Function.update p0 src (p0 src + 1)) dst
          (Function.update p0 src (p0 src + 1) dst + 1) j ∧
        Function.update (Function.update p0 src (p0 src + 1)) dst
          (Function.update p0 src (p0 src + 1) dst + 1) j ≤
        Function.update (Function.update u0 src (max (u0 src) (p0 src + 1))) dst
          (max (Function.update u0 src (max (u0 src) (p0 src + 1)) dst)
            (Function.update p0 src (p0 src + 1) dst + 1)) j := by
      intro j
      by_cases hj1 : j = dst
      · subst hj1; simp only [Function.update_self, Function.update_of_ne hsd.symm]
        exact ⟨le_trans (hw j).1 (by omega), le_max_right _ _⟩
      · by_cases hj2 : j = src
        · subst hj2; simp only [Function.update_of_ne hj1, Function.update_self]
          exact ⟨le_trans (hw j).1 (by omega), le_max_right _ _⟩
        · simp [hj1, hj2, hw j]
    rcases ih (b :: L) (b :: L') _ _ _ hw_next hsrc2 hdst3 with
      ⟨t1, p1, u1, htail, h1src, h1dst, h1oth, hp1src, hp1dst, hw1, hu1_ge, hspace⟩
    have htr : Computation.Trace (locatedStep ((copy1Forward src dst).machine inTape))
        (3 * (b :: bs).length + 1)
        ⟨⟨.inr (copy1Forward src dst).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ := by
      have hlen : 3 * bs.length + 1 + 1 + 1 + 1 = 3 * (b :: bs).length + 1 := by simp; omega
      rw [← hlen]
      exact .cons hs0 (.cons hs1 (.cons hs2 htail))
    refine ⟨t1, p1, u1, htr, ?_, ?_, ?_, ?_, ?_, hw1, ?_, ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using h1src
    · simpa [List.reverse_cons, List.append_assoc] using h1dst
    · intro j hj1 hj2
      rcases h1oth j hj1 hj2 with ⟨htj, hpj, huj⟩
      simp only [Function.update_of_ne hj2, Function.update_of_ne hj1] at htj hpj huj
      exact ⟨htj, hpj, huj⟩
    · simp only [Function.update_of_ne hsd, Function.update_self] at hp1src
      simp [hp1src]; omega
    · simp only [Function.update_self, Function.update_of_ne hsd.symm] at hp1dst
      simp [hp1dst]; omega
    · intro j
      refine le_trans ?_ (hu1_ge j)
      by_cases hj1 : j = dst
      · subst hj1; simp [hsd.symm]
      · by_cases hj2 : j = src
        · subst hj2; simp [hj1]
        · simp [hj1, hj2]
    · have hu_le : ∀ j, Function.update (Function.update u0 src (max (u0 src) (p0 src + 1))) dst
          (max (Function.update u0 src (max (u0 src) (p0 src + 1)) dst)
            (Function.update p0 src (p0 src + 1) dst + 1)) j ≤
          u0 j + (((if j = src then 1 else 0) + (if j = dst then 1 else 0) : ℕ) : ℤ) := by
        intro j
        by_cases hj1 : j = dst
        · rw [hj1]; simp [hsd.symm]; have := (hw dst).2; omega
        · by_cases hj2 : j = src
          · rw [hj2]; simp [hsd]; have := (hw src).2; omega
          · simp [hj1, hj2]
      have hspace0 := spanSum_le_add l0 u0 l0 _ (fun _ => 0)
        (fun j => (if j = src then 1 else 0) + (if j = dst then 1 else 0))
        (fun _ => by omega) hu_le (fun j => le_trans (hw j).1 (hw j).2)
      have hsum_inc : ∑ j : Fin N, ((if j = src then 1 else 0) + (if j = dst then 1 else 0) + 0) ≤ 2 := by
        simp only [add_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        decide
      simp only [List.length_cons]
      omega

/-- Copy from `src` onto `dst1` and `dst2` simultaneously moving rightward. -/
def copy2Forward {N : ℕ} (src dst1 dst2 : Fin N) : Program N where
  stateCount := 9
  start := s9 0
  scan q := match q.val with
    | 0 => src
    | 1 | 2 | 3 | 4 => dst1
    | _ => dst2
  transition q sym :=
    match q.val with
    | 0 => match sym with
      | none => .inl true
      | some false => .inr (s9 1, .move .right)
      | some true => .inr (s9 2, .move .right)
    | 1 => .inr (s9 3, .write (some false))
    | 3 => .inr (s9 5, .move .right)
    | 5 => .inr (s9 7, .write (some false))
    | 7 => .inr (s9 0, .move .right)
    | 2 => .inr (s9 4, .write (some true))
    | 4 => .inr (s9 6, .move .right)
    | 6 => .inr (s9 8, .write (some true))
    | _ => .inr (s9 0, .move .right)

theorem copy2Forward_run {N : ℕ} (src dst1 dst2 inTape : Fin N)
    (h1 : src ≠ dst1) (h2 : src ≠ dst2) (h12 : dst1 ≠ dst2)
    (L R L1 L2 : List Bool) (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (hsrc : t0 src = bTape L R) (hdst1 : t0 dst1 = bTape L1 []) (hdst2 : t0 dst2 = bTape L2 []) :
    ∃ t1 p1 u1,
      Computation.Trace (locatedStep ((copy2Forward src dst1 dst2).machine inTape)) (5 * R.length + 1)
        ⟨⟨.inr (copy2Forward src dst1 dst2).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ ∧
      t1 src = bTape (R.reverse ++ L) [] ∧
      t1 dst1 = bTape (R.reverse ++ L1) [] ∧
      t1 dst2 = bTape (R.reverse ++ L2) [] ∧
      (∀ j, j ≠ src → j ≠ dst1 → j ≠ dst2 → t1 j = t0 j ∧ p1 j = p0 j ∧ u1 j = u0 j) ∧
      p1 src = p0 src + R.length ∧
      p1 dst1 = p0 dst1 + R.length ∧
      p1 dst2 = p0 dst2 + R.length ∧
      (∀ j, l0 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      (∀ j, u0 j ≤ u1 j) ∧
      spanSum l0 u1 ≤ spanSum l0 u0 + 3 * R.length := by
  induction R generalizing L L1 L2 t0 p0 u0 with
  | nil =>
    have hhead : (t0 src).head = none := by rw [hsrc]; rfl
    have hs := step_halt (copy2Forward src dst1 dst2) inTape (s9 0) true src t0 p0 l0 u0 rfl
      (by rw [hhead]; rfl)
    refine ⟨t0, p0, u0, .cons hs (.refl _), by simpa using hsrc, by simpa using hdst1,
      by simpa using hdst2, fun _ _ _ _ => ⟨rfl, rfl, rfl⟩, by simp, by simp, by simp,
      hw, fun _ => le_rfl, by simp⟩
  | cons b bs ih =>
    have hhead : (t0 src).head = some b := by rw [hsrc]; rfl
    let q1 : Fin 9 := if b then s9 2 else s9 1
    let q2 : Fin 9 := if b then s9 4 else s9 3
    let q3 : Fin 9 := if b then s9 6 else s9 5
    let q4 : Fin 9 := if b then s9 8 else s9 7
    have hs0 : locatedStep ((copy2Forward src dst1 dst2).machine inTape)
        ⟨⟨.inr (s9 0), t0⟩, p0, l0, u0⟩ =
        some ⟨⟨.inr q1, Function.update t0 src ((t0 src).move .right)⟩,
          Function.update p0 src (p0 src + 1), l0,
          Function.update u0 src (max (u0 src) (p0 src + 1))⟩ := by
      cases b <;> exact step_move_right (copy2Forward src dst1 dst2) inTape (s9 0) _ src
        t0 p0 l0 u0 (hw src) rfl (by rw [hhead]; rfl)
    have hw_dst1 : l0 dst1 ≤ Function.update p0 src (p0 src + 1) dst1 ∧
        Function.update p0 src (p0 src + 1) dst1 ≤
          Function.update u0 src (max (u0 src) (p0 src + 1)) dst1 := by
      simp [h1.symm, hw dst1]
    let t_a1 := Function.update t0 src ((t0 src).move .right)
    let t_a1w := Function.update t_a1 dst1 ((t_a1 dst1).write (some b))
    let t_a2 := Function.update t_a1w dst1 ((t_a1w dst1).move .right)
    let t_a2w := Function.update t_a2 dst2 ((t_a2 dst2).write (some b))
    let t_a4 := Function.update t_a2w dst2 ((t_a2w dst2).move .right)
    have hscan1 : (copy2Forward src dst1 dst2).scan q1 = dst1 := by cases b <;> rfl
    have hscan2 : (copy2Forward src dst1 dst2).scan q2 = dst1 := by cases b <;> rfl
    have hscan3 : (copy2Forward src dst1 dst2).scan q3 = dst2 := by cases b <;> rfl
    have hscan4 : (copy2Forward src dst1 dst2).scan q4 = dst2 := by cases b <;> rfl
    have htr1 : ∀ sym, (copy2Forward src dst1 dst2).transition q1 sym = .inr (q2, .write (some b)) :=
      fun _ => by cases b <;> rfl
    have hs1 := step_write (copy2Forward src dst1 dst2) inTape q1 q2 (some b) dst1 t_a1
      (Function.update p0 src (p0 src + 1)) l0 (Function.update u0 src (max (u0 src) (p0 src + 1)))
      hw_dst1 hscan1 (htr1 _)
    have htr2 : ∀ sym, (copy2Forward src dst1 dst2).transition q2 sym = .inr (q3, .move .right) :=
      fun _ => by cases b <;> rfl
    have hs2 := step_move_right (copy2Forward src dst1 dst2) inTape q2 q3 dst1
      t_a1w (Function.update p0 src (p0 src + 1)) l0 (Function.update u0 src (max (u0 src) (p0 src + 1)))
      hw_dst1 hscan2 (htr2 _)
    let p_a2 := Function.update (Function.update p0 src (p0 src + 1)) dst1
      (Function.update p0 src (p0 src + 1) dst1 + 1)
    let u_a2 := Function.update (Function.update u0 src (max (u0 src) (p0 src + 1))) dst1
      (max (Function.update u0 src (max (u0 src) (p0 src + 1)) dst1)
        (Function.update p0 src (p0 src + 1) dst1 + 1))
    have hw_dst2 : l0 dst2 ≤ p_a2 dst2 ∧ p_a2 dst2 ≤ u_a2 dst2 := by
      simp [p_a2, u_a2, h12.symm, h2.symm, hw dst2]
    have htr3 : ∀ sym, (copy2Forward src dst1 dst2).transition q3 sym = .inr (q4, .write (some b)) :=
      fun _ => by cases b <;> rfl
    have hs3 := step_write (copy2Forward src dst1 dst2) inTape q3 q4 (some b) dst2 t_a2
      p_a2 l0 u_a2 hw_dst2 hscan3 (htr3 _)
    have htr4 : ∀ sym, (copy2Forward src dst1 dst2).transition q4 sym = .inr (s9 0, .move .right) :=
      fun _ => by cases b <;> rfl
    have hs4 := step_move_right (copy2Forward src dst1 dst2) inTape q4 (s9 0) dst2
      t_a2w p_a2 l0 u_a2 hw_dst2 hscan4 (htr4 _)
    have hsrc_a4 : t_a4 src = bTape (b :: L) bs := by
      dsimp [t_a4, t_a2w, t_a2, t_a1w, t_a1]
      simp [h2, h1, hsrc, bTape_move_right_cons]
    have hdst1_a4 : t_a4 dst1 = bTape (b :: L1) [] := by
      dsimp [t_a4, t_a2w, t_a2, t_a1w, t_a1]
      simp [h12, h1.symm, hdst1, bTape_write_nil, bTape_move_right_cons]
    have hdst2_a4 : t_a4 dst2 = bTape (b :: L2) [] := by
      dsimp [t_a4, t_a2w, t_a2, t_a1w, t_a1]
      simp [Function.update_self, h12.symm, h2.symm, hdst2, bTape_write_nil, bTape_move_right_cons]
    have hw_a4 : ∀ j, l0 j ≤ Function.update p_a2 dst2 (p_a2 dst2 + 1) j ∧
        Function.update p_a2 dst2 (p_a2 dst2 + 1) j ≤
          Function.update u_a2 dst2 (max (u_a2 dst2) (p_a2 dst2 + 1)) j := by
      intro j
      by_cases hj3 : j = dst2
      · subst hj3; simp only [Function.update_self]; exact ⟨le_trans hw_dst2.1 (by omega), le_max_right _ _⟩
      · by_cases hj2 : j = dst1
        · subst hj2; simp only [Function.update_of_ne hj3, p_a2, u_a2, Function.update_self, Function.update_of_ne h1.symm]
          exact ⟨le_trans (hw j).1 (by omega), le_max_right _ _⟩
        · by_cases hj1 : j = src
          · subst hj1; simp only [Function.update_of_ne hj3, p_a2, u_a2, Function.update_of_ne hj2, Function.update_self]
            exact ⟨le_trans (hw j).1 (by omega), le_max_right _ _⟩
          · simp [hj3, hj2, hj1, p_a2, u_a2, hw j]
    rcases ih (b :: L) (b :: L1) (b :: L2) t_a4 _ _ hw_a4 hsrc_a4 hdst1_a4 hdst2_a4 with
      ⟨t1, p1, u1, htail, h1src, h1dst1, h1dst2, h1oth, hp1src, hp1dst1, hp1dst2, hw1, hu1_ge, hspace⟩
    have htr : Computation.Trace (locatedStep ((copy2Forward src dst1 dst2).machine inTape))
        (5 * (b :: bs).length + 1)
        ⟨⟨.inr (copy2Forward src dst1 dst2).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ := by
      have hlen : 5 * bs.length + 1 + 1 + 1 + 1 + 1 + 1 = 5 * (b :: bs).length + 1 := by simp; omega
      rw [← hlen]
      exact .cons hs0 (.cons hs1 (.cons hs2 (.cons hs3 (.cons hs4 htail))))
    refine ⟨t1, p1, u1, htr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hw1, ?_, ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using h1src
    · simpa [List.reverse_cons, List.append_assoc] using h1dst1
    · simpa [List.reverse_cons, List.append_assoc] using h1dst2
    · intro j hj1 hj2 hj3
      rcases h1oth j hj1 hj2 hj3 with ⟨htj, hpj, huj⟩
      simp only [t_a4, t_a2w, t_a2, t_a1w, t_a1, p_a2, u_a2, Function.update_of_ne hj3,
        Function.update_of_ne hj2, Function.update_of_ne hj1] at htj hpj huj
      exact ⟨htj, hpj, huj⟩
    · simp only [p_a2, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self] at hp1src
      simp [hp1src]; omega
    · simp only [p_a2, Function.update_of_ne h12, Function.update_self, Function.update_of_ne h1.symm] at hp1dst1
      simp [hp1dst1]; omega
    · simp only [p_a2, Function.update_self, Function.update_of_ne h12.symm, Function.update_of_ne h2.symm] at hp1dst2
      simp [hp1dst2]; omega
    · intro j
      refine le_trans ?_ (hu1_ge j)
      by_cases hj3 : j = dst2
      · subst hj3; simp [u_a2, h12.symm, h2.symm]
      · by_cases hj2 : j = dst1
        · subst hj2; simp [u_a2, hj3, h1.symm]
        · by_cases hj1 : j = src
          · subst hj1; simp [u_a2, hj3, hj2]
          · simp [u_a2, hj3, hj2, hj1]
    · have hu_le : ∀ j, Function.update u_a2 dst2 (max (u_a2 dst2) (p_a2 dst2 + 1)) j ≤
          u0 j + (((if j = src then 1 else 0) + (if j = dst1 then 1 else 0) +
            (if j = dst2 then 1 else 0) : ℕ) : ℤ) := by
        intro j
        by_cases hj3 : j = dst2
        · rw [hj3]; simp [u_a2, p_a2, h12.symm, h2.symm]; have := (hw dst2).2; omega
        · by_cases hj2 : j = dst1
          · rw [hj2]; simp [u_a2, p_a2, h12, h1.symm]; have := (hw dst1).2; omega
          · by_cases hj1 : j = src
            · rw [hj1]; simp [u_a2, p_a2, h2, h1]; have := (hw src).2; omega
            · simp [u_a2, hj3, hj2, hj1]
      have hspace0 := spanSum_le_add l0 u0 l0 _ (fun _ => 0)
        (fun j => (if j = src then 1 else 0) + (if j = dst1 then 1 else 0) + (if j = dst2 then 1 else 0))
        (fun _ => by omega) hu_le (fun j => le_trans (hw j).1 (hw j).2)
      have hsum_inc : ∑ j : Fin N, ((if j = src then 1 else 0) + (if j = dst1 then 1 else 0) +
          (if j = dst2 then 1 else 0) + 0) ≤ 3 := by
        simp only [add_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        decide
      simp only [List.length_cons]
      omega

/-- Append `(true :: Encoding.frame w)` from `src` onto `dst` (`bTape acc []`). -/
def appendFrame {N : ℕ} (src dst : Fin N) : Program N where
  stateCount := 13
  start := s13 0
  scan q := match q.val with | 2 => src | _ => dst
  transition q sym :=
    match q.val with
    | 0 => .inr (s13 1, .write (some true))
    | 1 => .inr (s13 2, .move .right)
    | 2 => match sym with
      | none => .inr (s13 3, .write none)
      | some false => .inr (s13 5, .move .right)
      | some true => .inr (s13 9, .move .right)
    | 3 => .inr (s13 4, .write (some false))
    | 4 => .inr (s13 12, .move .right)
    | 12 => .inl true
    | 5 => .inr (s13 6, .write (some true))
    | 6 => .inr (s13 7, .move .right)
    | 7 => .inr (s13 8, .write (some false))
    | 8 => .inr (s13 2, .move .right)
    | 9 => .inr (s13 10, .write (some true))
    | 10 => .inr (s13 11, .move .right)
    | _ => .inr (s13 8, .write (some true))

private theorem appendFrame_loop {N : ℕ} (src dst inTape : Fin N) (hsd : src ≠ dst)
    (L R acc : List Bool) (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (hsrc : t0 src = bTape L R) (hdst : t0 dst = bTape acc []) :
    ∃ t1 p1 u1,
      Computation.Trace (locatedStep ((appendFrame src dst).machine inTape)) (5 * R.length + 4)
        ⟨⟨.inr (s13 2), t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ ∧
      t1 dst = bTape ((Encoding.frame R).reverse ++ acc) [] ∧
      (∀ j, j ≠ src → j ≠ dst → t1 j = t0 j ∧ p1 j = p0 j ∧ u1 j = u0 j) ∧
      p1 dst = p0 dst + (Encoding.frame R).length ∧
      (∀ j, l0 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      (∀ j, u0 j ≤ u1 j) ∧
      spanSum l0 u1 ≤ spanSum l0 u0 + (3 * R.length + 1) := by
  induction R generalizing L acc t0 p0 u0 with
  | nil =>
    have hhead : (t0 src).head = none := by rw [hsrc]; rfl
    have hs0 := step_write (appendFrame src dst) inTape (s13 2) (s13 3) none src
      t0 p0 l0 u0 (hw src) rfl (by rw [hhead]; rfl)
    have ht_noop : Function.update t0 src ((t0 src).write none) = t0 := by
      have : (t0 src).write none = t0 src := by
        rw [hsrc]; exact Turing.Tape.write_self (bTape L [])
      simp [this]
    have hs0' : locatedStep ((appendFrame src dst).machine inTape) ⟨⟨.inr (s13 2), t0⟩, p0, l0, u0⟩ =
        some ⟨⟨.inr (s13 3), t0⟩, p0, l0, u0⟩ :=
      hs0.trans (congrArg some (loc_ext (cfg_ext' rfl ht_noop) rfl rfl rfl))
    have hs1 := step_write (appendFrame src dst) inTape (s13 3) (s13 4) (some false) dst
      t0 p0 l0 u0 (hw dst) rfl rfl
    let t_f := Function.update t0 dst ((t0 dst).write (some false))
    let t_f2 := Function.update t_f dst ((t_f dst).move .right)
    let p_f2 := Function.update p0 dst (p0 dst + 1)
    let u_f2 := Function.update u0 dst (max (u0 dst) (p0 dst + 1))
    have hs2 := step_move_right (appendFrame src dst) inTape (s13 4) (s13 12) dst
      t_f p0 l0 u0 (hw dst) rfl rfl
    have hs3 := step_halt (appendFrame src dst) inTape (s13 12) true dst t_f2 p_f2 l0 u_f2 rfl rfl
    have htr := Computation.Trace.cons hs0' (.cons hs1 (.cons hs2 (.cons hs3 (.refl _))))
    have hdst_fin : t_f2 = Function.update t0 dst (bTape (false :: acc) []) := by
      dsimp [t_f2, t_f]
      simp [Function.update_idem, hdst, bTape_write_nil, bTape_move_right_cons]
    rw [hdst_fin] at htr
    dsimp only [p_f2, u_f2] at htr ⊢
    refine ⟨_, _, _, htr, by simp [Encoding.frame], fun j _ hj2 => by simp [hj2],
      by simp [Encoding.frame], ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = dst
      · rw [hj]; simp only [Function.update_self]; exact ⟨le_trans (hw dst).1 (by omega), le_max_right _ _⟩
      · simp [hj, hw j]
    · intro j
      by_cases hj : j = dst
      · rw [hj]; simp
      · simp [hj]
    · have hs := spanSum_le_add l0 u0 l0 (Function.update u0 dst (max (u0 dst) (p0 dst + 1)))
        (fun _ => 0) (fun j => if j = dst then 1 else 0) (fun _ => by omega)
        (fun j => by
          by_cases hj : j = dst
          · rw [hj]; simp; have := (hw dst).2; omega
          · simp [hj])
        (fun j => le_trans (hw j).1 (hw j).2)
      simp at hs ⊢
      omega
  | cons b bs ih =>
    have hhead : (t0 src).head = some b := by rw [hsrc]; rfl
    let qA : Fin 13 := if b then s13 9 else s13 5
    let qB : Fin 13 := if b then s13 10 else s13 6
    let qC : Fin 13 := if b then s13 11 else s13 7
    have hs0 : locatedStep ((appendFrame src dst).machine inTape)
        ⟨⟨.inr (s13 2), t0⟩, p0, l0, u0⟩ =
        some ⟨⟨.inr qA, Function.update t0 src ((t0 src).move .right)⟩,
          Function.update p0 src (p0 src + 1), l0,
          Function.update u0 src (max (u0 src) (p0 src + 1))⟩ := by
      cases b <;> exact step_move_right (appendFrame src dst) inTape (s13 2) _ src
        t0 p0 l0 u0 (hw src) rfl (by rw [hhead]; rfl)
    have hw1_dst : l0 dst ≤ Function.update p0 src (p0 src + 1) dst ∧
        Function.update p0 src (p0 src + 1) dst ≤
          Function.update u0 src (max (u0 src) (p0 src + 1)) dst := by
      simp [hsd.symm, hw dst]
    let t_s1 := Function.update t0 src ((t0 src).move .right)
    let t_s1w := Function.update t_s1 dst ((t_s1 dst).write (some true))
    let t_s2 := Function.update t_s1w dst ((t_s1w dst).move .right)
    let t_s2w := Function.update t_s2 dst ((t_s2 dst).write (some b))
    let t_n := Function.update t_s2w dst ((t_s2w dst).move .right)
    let p_mid := Function.update p0 src (p0 src + 1)
    let u_mid := Function.update u0 src (max (u0 src) (p0 src + 1))
    let p_step1 := Function.update p_mid dst (p_mid dst + 1)
    let u_step1 := Function.update u_mid dst (max (u_mid dst) (p_mid dst + 1))
    let p_n := Function.update p_step1 dst (p_step1 dst + 1)
    let u_n := Function.update u_step1 dst (max (u_step1 dst) (p_step1 dst + 1))
    have hscanA : (appendFrame src dst).scan qA = dst := by cases b <;> rfl
    have hscanB : (appendFrame src dst).scan qB = dst := by cases b <;> rfl
    have hscanC : (appendFrame src dst).scan qC = dst := by cases b <;> rfl
    have htrA : ∀ sym, (appendFrame src dst).transition qA sym = .inr (qB, .write (some true)) :=
      fun _ => by cases b <;> rfl
    have hs1 := step_write (appendFrame src dst) inTape qA qB (some true) dst
      t_s1 p_mid l0 u_mid hw1_dst hscanA (htrA _)
    have htrB : ∀ sym, (appendFrame src dst).transition qB sym = .inr (qC, .move .right) :=
      fun _ => by cases b <;> rfl
    have hs2 := step_move_right (appendFrame src dst) inTape qB qC dst
      t_s1w p_mid l0 u_mid hw1_dst hscanB (htrB _)
    have hw2_dst : l0 dst ≤ p_step1 dst ∧ p_step1 dst ≤ u_step1 dst := by
      simp only [p_step1, u_step1, p_mid, u_mid, Function.update_self, Function.update_of_ne hsd.symm]
      exact ⟨le_trans (hw dst).1 (by omega), le_max_right _ _⟩
    have htrC : ∀ sym, (appendFrame src dst).transition qC sym = .inr (s13 8, .write (some b)) :=
      fun _ => by cases b <;> rfl
    have hs3 := step_write (appendFrame src dst) inTape qC (s13 8) (some b) dst
      t_s2 p_step1 l0 u_step1 hw2_dst hscanC (htrC _)
    have hs4 := step_move_right (appendFrame src dst) inTape (s13 8) (s13 2) dst
      t_s2w p_step1 l0 u_step1 hw2_dst rfl rfl
    have hw_n : ∀ j, l0 j ≤ p_n j ∧ p_n j ≤ u_n j := by
      intro j
      by_cases hj1 : j = dst
      · subst hj1; simp only [p_n, u_n, Function.update_self]
        exact ⟨le_trans hw2_dst.1 (by omega), le_max_right _ _⟩
      · by_cases hj2 : j = src
        · subst hj2
          simp only [p_n, u_n, p_step1, u_step1, p_mid, u_mid, Function.update_of_ne hj1,
            Function.update_self]
          exact ⟨le_trans (hw j).1 (by omega), le_max_right _ _⟩
        · simp [p_n, u_n, p_step1, u_step1, p_mid, u_mid, hj1, hj2, hw j]
    have hsrc_n : t_n src = bTape (b :: L) bs := by
      dsimp [t_n, t_s2w, t_s2, t_s1w, t_s1]
      simp [hsd, hsrc, bTape_move_right_cons]
    have hdst_n : t_n dst = bTape (b :: true :: acc) [] := by
      dsimp [t_n, t_s2w, t_s2, t_s1w, t_s1]
      simp [Function.update_self, hsd.symm, hdst, bTape_write_nil, bTape_move_right_cons]
    rcases ih (b :: L) (b :: true :: acc) t_n p_n u_n hw_n hsrc_n hdst_n with
      ⟨t1, p1, u1, htail, h1dst, h1oth, hp1dst, hw1, hu1_ge, hspace⟩
    have htr : Computation.Trace (locatedStep ((appendFrame src dst).machine inTape))
        (5 * (b :: bs).length + 4) ⟨⟨.inr (s13 2), t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ := by
      have hlen : 5 * bs.length + 4 + 1 + 1 + 1 + 1 + 1 = 5 * (b :: bs).length + 4 := by simp; omega
      rw [← hlen]
      exact .cons hs0 (.cons hs1 (.cons hs2 (.cons hs3 (.cons hs4 htail))))
    refine ⟨t1, p1, u1, htr, ?_, ?_, ?_, hw1, ?_, ?_⟩
    · change t1 dst = bTape ((true :: b :: Encoding.frame bs).reverse ++ acc) []
      simpa [List.reverse_cons, List.append_assoc] using h1dst
    · intro j hj1 hj2
      rcases h1oth j hj1 hj2 with ⟨htj, hpj, huj⟩
      simp only [t_n, t_s2w, t_s2, t_s1w, t_s1, p_n, p_step1, p_mid, u_n, u_step1, u_mid,
        Function.update_of_ne hj2, Function.update_of_ne hj1] at htj hpj huj
      exact ⟨htj, hpj, huj⟩
    · change p1 dst = p0 dst + ((true :: b :: Encoding.frame bs).length : ℤ)
      simp only [p_n, p_step1, p_mid, Function.update_self, Function.update_of_ne hsd.symm] at hp1dst
      simp only [List.length_cons]
      omega
    · intro j
      refine le_trans ?_ (hu1_ge j)
      by_cases hj1 : j = dst
      · subst hj1
        simp only [u_n, u_step1, u_mid, Function.update_self, Function.update_of_ne hsd.symm]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      · by_cases hj2 : j = src
        · subst hj2
          simp only [u_n, u_step1, u_mid, Function.update_of_ne hj1, Function.update_self]
          exact le_max_left _ _
        · simp [u_n, u_step1, u_mid, hj1, hj2]
    · have hu_le : ∀ j, u_n j ≤
          u0 j + (((if j = src then 1 else 0) + (if j = dst then 2 else 0) : ℕ) : ℤ) := by
        intro j
        by_cases hj1 : j = dst
        · subst hj1
          simp only [u_n, u_step1, u_mid, p_step1, p_mid, Function.update_self,
            Function.update_of_ne hsd.symm, ↓reduceIte]
          have := (hw j).2; omega
        · by_cases hj2 : j = src
          · subst hj2
            simp only [u_n, u_step1, u_mid, Function.update_of_ne hj1, Function.update_self,
              ↓reduceIte]
            have := (hw j).2; omega
          · simp [u_n, u_step1, u_mid, hj1, hj2]
      have hspace0 := spanSum_le_add l0 u0 l0 u_n (fun _ => 0)
        (fun j => (if j = src then 1 else 0) + (if j = dst then 2 else 0))
        (fun _ => by omega) hu_le (fun j => le_trans (hw j).1 (hw j).2)
      have hsum_inc : ∑ j : Fin N, ((if j = src then 1 else 0) + (if j = dst then 2 else 0) + 0) ≤ 3 := by
        simp only [add_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        decide
      simp only [List.length_cons]
      omega

theorem appendFrame_run {N : ℕ} (src dst inTape : Fin N) (hsd : src ≠ dst)
    (w acc : List Bool) (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (hsrc : t0 src = bTape [] w) (hdst : t0 dst = bTape acc []) :
    ∃ t1 p1 u1,
      Computation.Trace (locatedStep ((appendFrame src dst).machine inTape)) (5 * w.length + 6)
        ⟨⟨.inr (appendFrame src dst).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ ∧
      t1 dst = bTape ((true :: Encoding.frame w).reverse ++ acc) [] ∧
      (∀ j, j ≠ src → j ≠ dst → t1 j = t0 j ∧ p1 j = p0 j ∧ u1 j = u0 j) ∧
      p1 dst = p0 dst + (true :: Encoding.frame w).length ∧
      (∀ j, l0 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      (∀ j, u0 j ≤ u1 j) ∧
      spanSum l0 u1 ≤ spanSum l0 u0 + (3 * w.length + 2) := by
  let t_w := Function.update t0 dst ((t0 dst).write (some true))
  let t_pre := Function.update t_w dst ((t_w dst).move .right)
  let p_pre := Function.update p0 dst (p0 dst + 1)
  let u_pre := Function.update u0 dst (max (u0 dst) (p0 dst + 1))
  have hs0 := step_write (appendFrame src dst) inTape (s13 0) (s13 1) (some true) dst
    t0 p0 l0 u0 (hw dst) rfl rfl
  have hs1 := step_move_right (appendFrame src dst) inTape (s13 1) (s13 2) dst
    t_w p0 l0 u0 (hw dst) rfl rfl
  have hw_pre : ∀ j, l0 j ≤ p_pre j ∧ p_pre j ≤ u_pre j := by
    intro j
    by_cases hj : j = dst
    · subst hj; simp only [p_pre, u_pre, Function.update_self]
      exact ⟨le_trans (hw j).1 (by omega), le_max_right _ _⟩
    · simp [p_pre, u_pre, hj, hw j]
  have hsrc_pre : t_pre src = bTape [] w := by
    simp [t_pre, t_w, hsd, hsrc]
  have hdst_pre : t_pre dst = bTape (true :: acc) [] := by
    simp [t_pre, t_w, Function.update_self, hdst, bTape_write_nil, bTape_move_right_cons]
  rcases appendFrame_loop src dst inTape hsd [] w (true :: acc) t_pre p_pre l0 u_pre
      hw_pre hsrc_pre hdst_pre with
    ⟨t1, p1, u1, htail, h1dst, h1oth, hp1dst, hw1, hu1_ge, hspace⟩
  have htr : Computation.Trace (locatedStep ((appendFrame src dst).machine inTape)) (5 * w.length + 6)
      ⟨⟨.inr (appendFrame src dst).start, t0⟩, p0, l0, u0⟩
      ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ := by
    have hlen : 5 * w.length + 4 + 1 + 1 = 5 * w.length + 6 := by omega
    rw [← hlen]
    exact .cons hs0 (.cons hs1 htail)
  refine ⟨t1, p1, u1, htr, ?_, ?_, ?_, hw1, ?_, ?_⟩
  · simpa [List.reverse_cons, List.append_assoc] using h1dst
  · intro j hj1 hj2
    rcases h1oth j hj1 hj2 with ⟨htj, hpj, huj⟩
    simp only [t_pre, t_w, p_pre, u_pre, Function.update_of_ne hj2] at htj hpj huj
    exact ⟨htj, hpj, huj⟩
  · simp only [p_pre, Function.update_self] at hp1dst
    simp only [List.length_cons]
    omega
  · intro j
    refine le_trans ?_ (hu1_ge j)
    by_cases hj : j = dst
    · subst hj; simp [u_pre]
    · simp [u_pre, hj]
  · have hspace0 := spanSum_le_add l0 u0 l0 u_pre (fun _ => 0)
      (fun j => if j = dst then 1 else 0)
      (fun _ => by omega)
      (fun j => by
        by_cases hj : j = dst
        · rw [hj]; simp [u_pre]; have := (hw dst).2; omega
        · simp [hj, u_pre])
      (fun j => le_trans (hw j).1 (hw j).2)
    simp at hspace0
    omega

/-- Write `false` at the head of `dst` and move right. -/
def appendFalse {N : ℕ} (dst : Fin N) : Program N where
  stateCount := 3
  start := s3 0
  scan _ := dst
  transition q _ :=
    match q.val with
    | 0 => .inr (s3 1, .write (some false))
    | 1 => .inr (s3 2, .move .right)
    | _ => .inl true

theorem appendFalse_run {N : ℕ} (dst inTape : Fin N) (acc : List Bool)
    (t0 : Fin N → Turing.Tape (Option Bool)) (p0 l0 u0 : Fin N → ℤ)
    (hw : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j)
    (hdst : t0 dst = bTape acc []) :
    ∃ t1 p1 u1,
      Computation.Trace (locatedStep ((appendFalse dst).machine inTape)) 3
        ⟨⟨.inr (appendFalse dst).start, t0⟩, p0, l0, u0⟩
        ⟨⟨.inl true, t1⟩, p1, l0, u1⟩ ∧
      t1 dst = bTape (false :: acc) [] ∧
      (∀ j, j ≠ dst → t1 j = t0 j ∧ p1 j = p0 j ∧ u1 j = u0 j) ∧
      p1 dst = p0 dst + 1 ∧
      (∀ j, l0 j ≤ p1 j ∧ p1 j ≤ u1 j) ∧
      (∀ j, u0 j ≤ u1 j) ∧
      spanSum l0 u1 ≤ spanSum l0 u0 + 1 := by
  let t_s1 := Function.update t0 dst ((t0 dst).write (some false))
  let t_s2 := Function.update t_s1 dst ((t_s1 dst).move .right)
  let p_s2 := Function.update p0 dst (p0 dst + 1)
  let u_s2 := Function.update u0 dst (max (u0 dst) (p0 dst + 1))
  have hs0 := step_write (appendFalse dst) inTape (s3 0) (s3 1) (some false) dst
    t0 p0 l0 u0 (hw dst) rfl rfl
  have hs1 := step_move_right (appendFalse dst) inTape (s3 1) (s3 2) dst
    t_s1 p0 l0 u0 (hw dst) rfl rfl
  have hs2 := step_halt (appendFalse dst) inTape (s3 2) true dst t_s2 p_s2 l0 u_s2 rfl rfl
  have htr := Computation.Trace.cons hs0 (.cons hs1 (.cons hs2 (.refl _)))
  dsimp only [t_s2, t_s1, p_s2, u_s2] at htr
  refine ⟨_, _, _, htr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_self, hdst, bTape_write_nil, bTape_move_right_cons]
  · intro j hj
    simp [hj]
  · simp [Function.update_self]
  · intro j
    by_cases hj : j = dst
    · rw [hj]; simp only [Function.update_self]
      exact ⟨le_trans (hw dst).1 (by omega), le_max_right _ _⟩
    · simp [hj, hw j]
  · intro j
    by_cases hj : j = dst
    · rw [hj]; simp
    · simp [hj]
  · have hspace0 := spanSum_le_add l0 u0 l0 (Function.update u0 dst (max (u0 dst) (p0 dst + 1)))
      (fun _ => 0) (fun j => if j = dst then 1 else 0)
      (fun _ => by omega)
      (fun j => by
        by_cases hj : j = dst
        · rw [hj]; simp; have := (hw dst).2; omega
        · simp [hj])
      (fun j => le_trans (hw j).1 (hw j).2)
    simp at hspace0 ⊢
    omega

end TapeRoutines

section ComplexityBounds

theorem frame_length (w : List Bool) : (Encoding.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons _ bs ih =>
    change (true :: _ :: Encoding.frame bs).length = 2 * (bs.length + 1) + 1
    simp only [List.length_cons, ih]
    omega

theorem encodeList3_eq (x a d : List Bool) :
    Encoding.encodeList id [x, a, d] =
      ((true :: Encoding.frame x) ++ (true :: Encoding.frame a) ++ (true :: Encoding.frame d)) ++
        [false] := by
  simp [Encoding.encodeList, List.append_assoc]

theorem encodeList3_length (x a d : List Bool) :
    (Encoding.encodeList id [x, a, d]).length =
      2 * x.length + 2 * a.length + 2 * d.length + 7 := by
  rw [encodeList3_eq]
  simp only [List.length_append, List.length_cons, List.length_nil, frame_length]
  omega

private theorem nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      have : (1 : ℝ) ≤ 2 := by norm_num
      exact one_le_pow₀ this
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    linarith

private theorem logSafe_nat_le {b : ℕ} (hb : 1 ≤ b) : logSafe (b : ℝ) ≤ (b : ℝ) := by
  unfold logSafe
  refine max_le (by exact_mod_cast hb) ?_
  unfold Real.logb
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2]
  have hpow : max (2 : ℝ) (b : ℝ) ≤ (2 : ℝ) ^ b := by
    refine max_le ?_ (nat_le_two_pow b)
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by ring
      _ ≤ (2 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hb
  have hpos : 0 < max (2 : ℝ) (b : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  calc Real.log (max (2 : ℝ) (b : ℝ))
      ≤ Real.log ((2 : ℝ) ^ b) := Real.log_le_log hpos (hpow)
    _ = (b : ℝ) * Real.log 2 := Real.log_pow 2 b

private theorem one_le_mainSpaceBound_exponent {b : ℕ} (hb : 1 ≤ b) :
    1 ≤ (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := by
  have hlog1 : 1 ≤ logSafe (b : ℝ) := le_max_left _ _
  have hlog_pos : 0 < logSafe (b : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hrpow_pos : 0 < (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hlog_pos _
  have hrpow_le : (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) ≤ logSafe (b : ℝ) := by
    calc (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ (logSafe (b : ℝ)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
      _ = logSafe (b : ℝ) := Real.rpow_one _
  exact (one_le_div hrpow_pos).2 (le_trans hrpow_le (logSafe_nat_le hb))

theorem one_le_mainSpaceBound (c b : ℕ) (hb : 1 ≤ b) : 1 ≤ mainSpaceBound c b := by
  unfold mainSpaceBound
  have hlog_nonneg : 0 ≤ (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  exact Real.one_le_rpow (by norm_num)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hlog_nonneg)

theorem mainSpaceBound_add (c₁ c₂ b : ℕ) :
    mainSpaceBound (c₁ + c₂) b = mainSpaceBound c₁ b * mainSpaceBound c₂ b := by
  unfold mainSpaceBound
  push_cast
  rw [add_mul, add_div, Real.rpow_add (by norm_num)]

theorem mainSpaceBound_three_mul (k b : ℕ) :
    (mainSpaceBound k b) ^ 3 = mainSpaceBound (3 * k) b := by
  rw [show 3 * k = k + (k + k) by omega, mainSpaceBound_add, mainSpaceBound_add]
  ring

theorem two_pow_le_mainSpaceBound (m b : ℕ) (hb : 1 ≤ b) :
    (2 : ℝ) ^ m ≤ mainSpaceBound m b := by
  unfold mainSpaceBound
  rw [← Real.rpow_natCast (2 : ℝ) m]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hexp := one_le_mainSpaceBound_exponent hb
  rw [mul_div_assoc]
  simpa using mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg m)

theorem poly_le_mainSpaceBound (k M b : ℕ) (hb : 1 ≤ b) :
    (M : ℝ) * (mainSpaceBound k b) ^ 3 ≤ mainSpaceBound (3 * k + M) b := by
  have hw0 : 0 ≤ mainSpaceBound k b := le_trans zero_le_one (one_le_mainSpaceBound k b hb)
  calc (M : ℝ) * (mainSpaceBound k b) ^ 3
      ≤ (2 : ℝ) ^ M * (mainSpaceBound k b) ^ 3 :=
        mul_le_mul_of_nonneg_right (nat_le_two_pow M) (pow_nonneg hw0 3)
    _ ≤ mainSpaceBound M b * mainSpaceBound (3 * k) b := by
        rw [mainSpaceBound_three_mul]
        exact mul_le_mul_of_nonneg_right (two_pow_le_mainSpaceBound M b hb)
          (le_trans zero_le_one (one_le_mainSpaceBound (3 * k) b hb))
    _ = mainSpaceBound (3 * k + M) b := by
        rw [← mainSpaceBound_add, add_comm M (3 * k)]

theorem one_le_bitLen {p : ℕ} (hp : 2 ≤ p) : 1 ≤ bitLen p := by
  unfold bitLen
  exact Nat.clog_pos (by decide) (by omega)

end ComplexityBounds

section MainComposition

/-- Total tape count for the composed four-call machine. -/
def compTapes (A B D E : PrimitiveMachine) : ℕ :=
  1 + A.tapeCount + B.tapeCount + D.tapeCount + E.tapeCount

def inIdx (A B D E : PrimitiveMachine) : Fin (compTapes A B D E) :=
  ⟨0, by dsimp [compTapes]; omega⟩

private def fA (A B D E : PrimitiveMachine) (i : Fin A.tapeCount) : Fin (compTapes A B D E) :=
  ⟨1 + i.val, by dsimp [compTapes]; omega⟩

private def fB (A B D E : PrimitiveMachine) (i : Fin B.tapeCount) : Fin (compTapes A B D E) :=
  ⟨1 + A.tapeCount + i.val, by dsimp [compTapes]; omega⟩

private def fD (A B D E : PrimitiveMachine) (i : Fin D.tapeCount) : Fin (compTapes A B D E) :=
  ⟨1 + A.tapeCount + B.tapeCount + i.val, by dsimp [compTapes]; omega⟩

def fE (A B D E : PrimitiveMachine) (i : Fin E.tapeCount) : Fin (compTapes A B D E) :=
  ⟨1 + A.tapeCount + B.tapeCount + D.tapeCount + i.val, by dsimp [compTapes]; omega⟩

private theorem fA_inj (A B D E : PrimitiveMachine) : Function.Injective (fA A B D E) := by
  intro i j hij; ext; have := congrArg Fin.val hij; simp [fA] at this; omega

private theorem fB_inj (A B D E : PrimitiveMachine) : Function.Injective (fB A B D E) := by
  intro i j hij; ext; have := congrArg Fin.val hij; simp [fB] at this; omega

private theorem fD_inj (A B D E : PrimitiveMachine) : Function.Injective (fD A B D E) := by
  intro i j hij; ext; have := congrArg Fin.val hij; simp [fD] at this; omega

private theorem fE_inj (A B D E : PrimitiveMachine) : Function.Injective (fE A B D E) := by
  intro i j hij; ext; have := congrArg Fin.val hij; simp [fE] at this; omega

private theorem in_ne_fA (A B D E : PrimitiveMachine) (i : Fin A.tapeCount) :
    inIdx A B D E ≠ fA A B D E i := by
  intro h; have := congrArg Fin.val h; simp [inIdx, fA] at this; omega

private theorem in_ne_fB (A B D E : PrimitiveMachine) (i : Fin B.tapeCount) :
    inIdx A B D E ≠ fB A B D E i := by
  intro h; have := congrArg Fin.val h; simp [inIdx, fB] at this; omega

private theorem in_ne_fD (A B D E : PrimitiveMachine) (i : Fin D.tapeCount) :
    inIdx A B D E ≠ fD A B D E i := by
  intro h; have := congrArg Fin.val h; simp [inIdx, fD] at this; omega

private theorem in_ne_fE (A B D E : PrimitiveMachine) (i : Fin E.tapeCount) :
    inIdx A B D E ≠ fE A B D E i := by
  intro h; have := congrArg Fin.val h; simp [inIdx, fE] at this; omega

private theorem fA_ne_fB (A B D E : PrimitiveMachine) (i : Fin A.tapeCount) (j : Fin B.tapeCount) :
    fA A B D E i ≠ fB A B D E j := by
  intro h; have := congrArg Fin.val h; simp [fA, fB] at this; omega

private theorem fA_ne_fD (A B D E : PrimitiveMachine) (i : Fin A.tapeCount) (j : Fin D.tapeCount) :
    fA A B D E i ≠ fD A B D E j := by
  intro h; have := congrArg Fin.val h; simp [fA, fD] at this; omega

private theorem fA_ne_fE (A B D E : PrimitiveMachine) (i : Fin A.tapeCount) (j : Fin E.tapeCount) :
    fA A B D E i ≠ fE A B D E j := by
  intro h; have := congrArg Fin.val h; simp [fA, fE] at this; omega

private theorem fB_ne_fD (A B D E : PrimitiveMachine) (i : Fin B.tapeCount) (j : Fin D.tapeCount) :
    fB A B D E i ≠ fD A B D E j := by
  intro h; have := congrArg Fin.val h; simp [fB, fD] at this; omega

private theorem fB_ne_fE (A B D E : PrimitiveMachine) (i : Fin B.tapeCount) (j : Fin E.tapeCount) :
    fB A B D E i ≠ fE A B D E j := by
  intro h; have := congrArg Fin.val h; simp [fB, fE] at this; omega

private theorem fD_ne_fE (A B D E : PrimitiveMachine) (i : Fin D.tapeCount) (j : Fin E.tapeCount) :
    fD A B D E i ≠ fE A B D E j := by
  intro h; have := congrArg Fin.val h; simp [fD, fE] at this; omega

private theorem four_call_time_bound {W xl al bl dl pl nA nB nD nE : ℝ} {N : ℕ}
    (hW : 1 ≤ W) (hx : xl ≤ W + 1) (ha : al ≤ W + 1) (hb : bl ≤ W + 1)
    (hd : dl ≤ (W + 1) * (bl + 1)) (hp : pl = 2 * xl + 2 * al + 2 * dl + 7)
    (hnA : nA ≤ W + 1) (hnB : nB ≤ W + 1)
    (hnD : nD ≤ (W + 1) * (bl + 1)) (hnE : nE ≤ (W + 1) * (pl + 1)) :
    (5 * xl + 1) + (xl + 3) + (xl + 3) + (xl + 3) + nA + nB + (3 * bl + 1) +
      (bl + 3) + nD + (5 * xl + 6) + (5 * al + 6) + (5 * dl + 6) + 3 + (pl + 3) + nE ≤
      ((N + 720 : ℕ) : ℝ) * W ^ 3 := by
  have h1_le_W1 : 1 ≤ W + 1 := by linarith
  have hW1_le2 : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hW2_le3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := by nlinarith
  have hW1_le3 : W + 1 ≤ (W + 1) ^ 3 := le_trans hW1_le2 hW2_le3
  have h1_le_W1_3 : 1 ≤ (W + 1) ^ 3 := le_trans h1_le_W1 hW1_le3
  have hD_rhs : (W + 1) * (bl + 1) ≤ 2 * (W + 1) ^ 2 := by nlinarith
  have hpl_le : pl + 1 ≤ 8 * (W + 1) ^ 2 := by nlinarith
  have hE_rhs : (W + 1) * (pl + 1) ≤ 8 * (W + 1) ^ 3 := by nlinarith
  have hW3_bound : (W + 1) ^ 3 ≤ 8 * W ^ 3 := by
    have h2w : W + 1 ≤ 2 * W := by linarith
    calc (W + 1) ^ 3 ≤ (2 * W) ^ 3 := pow_le_pow_left₀ (by linarith) h2w 3
      _ = 8 * W ^ 3 := by ring
  have h1_le_W3 : 1 ≤ W ^ 3 := one_le_pow₀ hW
  have hN_le : 0 ≤ (N : ℝ) * W ^ 3 := mul_nonneg (Nat.cast_nonneg N) (by linarith)
  push_cast
  linarith

private theorem four_call_space_bound {W xl al bl dl pl sp0 sp1 sp2 sp3 sp4 sp5 sp6 sp7 sp8 sp9
    sp10 sp11 sp12 sp13 sp14 sp15 : ℝ} {N : ℕ}
    (hW : 1 ≤ W) (hx : xl ≤ W + 1) (ha : al ≤ W + 1) (hb : bl ≤ W + 1)
    (hd : dl ≤ (W + 1) * (bl + 1)) (hp : pl = 2 * xl + 2 * al + 2 * dl + 7)
    (h0 : sp0 ≤ (N : ℝ) + xl) (h1 : sp1 ≤ sp0 + 3 * xl) (h2 : sp2 ≤ sp1 + 1)
    (h3 : sp3 ≤ sp2 + 1) (h4 : sp4 ≤ sp3 + 1) (h5 : sp5 ≤ sp4 + (W + 1))
    (h6 : sp6 ≤ sp5 + (W + 1)) (h7 : sp7 ≤ sp6 + 2 * bl) (h8 : sp8 ≤ sp7 + 1)
    (h9 : sp9 ≤ sp8 + (W + 1) * (bl + 1)) (h10 : sp10 ≤ sp9 + (3 * xl + 2))
    (h11 : sp11 ≤ sp10 + (3 * al + 2)) (h12 : sp12 ≤ sp11 + (3 * dl + 2))
    (h13 : sp13 ≤ sp12 + 1) (h14 : sp14 ≤ sp13 + 1)
    (h15 : sp15 ≤ sp14 + (W + 1) * (pl + 1)) :
    sp15 ≤ ((N + 720 : ℕ) : ℝ) * W ^ 3 := by
  have h1_le_W1 : 1 ≤ W + 1 := by linarith
  have hW1_le2 : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hW2_le3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := by nlinarith
  have hW1_le3 : W + 1 ≤ (W + 1) ^ 3 := le_trans hW1_le2 hW2_le3
  have h1_le_W1_3 : 1 ≤ (W + 1) ^ 3 := le_trans h1_le_W1 hW1_le3
  have hD_rhs : (W + 1) * (bl + 1) ≤ 2 * (W + 1) ^ 2 := by nlinarith
  have hpl_le : pl + 1 ≤ 8 * (W + 1) ^ 2 := by nlinarith
  have hE_rhs : (W + 1) * (pl + 1) ≤ 8 * (W + 1) ^ 3 := by nlinarith
  have hW3_bound : (W + 1) ^ 3 ≤ 8 * W ^ 3 := by
    have h2w : W + 1 ≤ 2 * W := by linarith
    calc (W + 1) ^ 3 ≤ (2 * W) ^ 3 := pow_le_pow_left₀ (by linarith) h2w 3
      _ = 8 * W ^ 3 := by ring
  have h1_le_W3 : 1 ≤ W ^ 3 := one_le_pow₀ hW
  have hN_le : (N : ℝ) ≤ (N : ℝ) * W ^ 3 := le_mul_of_one_le_right (Nat.cast_nonneg N) h1_le_W3
  push_cast
  linarith

private def compStage1 (A B D E : PrimitiveMachine) : Program (compTapes A B D E) :=
  copy2Forward (inIdx A B D E) (fA A B D E A.inputTape) (fB A B D E B.inputTape)

private def compStage2 (A B D E : PrimitiveMachine) : Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage1 A B D E) (rewindProgram (inIdx A B D E))

private def compStage3 (A B D E : PrimitiveMachine) : Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage2 A B D E) (rewindProgram (fA A B D E A.inputTape))

private def compStage4 (A B D E : PrimitiveMachine) : Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage3 A B D E) (rewindProgram (fB A B D E B.inputTape))

private def compStage5 (A B D E : PrimitiveMachine) : Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage4 A B D E) (embedProgram A (fA A B D E))

private def compStage6 (A B D E : PrimitiveMachine) : Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage5 A B D E) (embedProgram B (fB A B D E))

private def compStage7 (A B : PrimitiveMachine) (ob : Fin B.tapeCount) (D E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage6 A B D E)
    (copy1Forward (fB A B D E ob) (fD A B D E D.inputTape))

private def compStage8 (A B : PrimitiveMachine) (ob : Fin B.tapeCount) (D E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage7 A B ob D E) (rewindProgram (fD A B D E D.inputTape))

private def compStage9 (A B : PrimitiveMachine) (ob : Fin B.tapeCount) (D E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage8 A B ob D E) (embedProgram D (fD A B D E))

private def compStage10 (A B : PrimitiveMachine) (ob : Fin B.tapeCount) (D E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage9 A B ob D E)
    (appendFrame (inIdx A B D E) (fE A B D E E.inputTape))

private def compStage11 (A : PrimitiveMachine) (oa : Fin A.tapeCount)
    (B : PrimitiveMachine) (ob : Fin B.tapeCount) (D E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage10 A B ob D E)
    (appendFrame (fA A B D E oa) (fE A B D E E.inputTape))

private def compStage12 (A : PrimitiveMachine) (oa : Fin A.tapeCount)
    (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage11 A oa B ob D E)
    (appendFrame (fD A B D E od) (fE A B D E E.inputTape))

private def compStage13 (A : PrimitiveMachine) (oa : Fin A.tapeCount)
    (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage12 A oa B ob D od E) (appendFalse (fE A B D E E.inputTape))

private def compStage14 (A : PrimitiveMachine) (oa : Fin A.tapeCount)
    (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) :
    Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage13 A oa B ob D od E) (rewindProgram (fE A B D E E.inputTape))

/-- Sequential 15-phase `Program` composing four submachines `A`, `B`, `D`, `E`. -/
def compProgram (A : PrimitiveMachine) (oa : Fin A.tapeCount)
    (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount)
    (E : PrimitiveMachine) : Program (compTapes A B D E) :=
  seqProg (inIdx A B D E) (compStage14 A oa B ob D od E) (embedProgram E (fE A B D E))

set_option maxHeartbeats 800000 in
theorem compProgram_runsWithin
    (A : PrimitiveMachine) (oa : Fin A.tapeCount) (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) (oe : Fin E.tapeCount)
    (k : ℕ) :
    let M := (compProgram A oa B ob D od E).machine (inIdx A B D E)
    let o : Fin M.tapeCount := fE A B D E oe
    let c := 3 * k + (compTapes A B D E + 720)
    ∀ (p : ℕ), 2 ≤ p → ∀ (x a b d e : List Bool),
      let W := mainSpaceBound k (bitLen p)
      let pack := Encoding.encodeList id [x, a, d]
      RunsWithin A oa x a (W + 1) (W + 1) →
      RunsWithin B ob x b (W + 1) (W + 1) →
      RunsWithin D od b d ((W + 1) * (b.length + 1)) ((W + 1) * (b.length + 1)) →
      RunsWithin E oe pack e ((W + 1) * (pack.length + 1)) ((W + 1) * (pack.length + 1)) →
      RunsWithin M o x e (mainSpaceBound c (bitLen p)) (mainSpaceBound c (bitLen p)) := by
  intro M o c p hp x a b d e W pack hA hB hD hE
  let N := compTapes A B D E
  let inp := inIdx A B D E
  let gA := fA A B D E
  let gB := fB A B D E
  let gD := fD A B D E
  let gE := fE A B D E
  let inA := gA A.inputTape
  let outA := gA oa
  let inB := gB B.inputTape
  let outB := gB ob
  let inD := gD D.inputTape
  let outD := gD od
  let inE := gE E.inputTape
  let outE := gE oe
  let Q1 := compStage1 A B D E
  let Q2 := compStage2 A B D E
  let Q3 := compStage3 A B D E
  let Q4 := compStage4 A B D E
  let Q5 := compStage5 A B D E
  let Q6 := compStage6 A B D E
  let Q7 := compStage7 A B ob D E
  let Q8 := compStage8 A B ob D E
  let Q9 := compStage9 A B ob D E
  let Q10 := compStage10 A B ob D E
  let Q11 := compStage11 A oa B ob D E
  let Q12 := compStage12 A oa B ob D od E
  let Q13 := compStage13 A oa B ob D od E
  let Q14 := compStage14 A oa B ob D od E
  let t0 : Fin N → Turing.Tape (Option Bool) := fun j =>
    if j = inp then bTape [] x else bTape [] []
  let p0 : Fin N → ℤ := fun _ => 0
  let l0 : Fin N → ℤ := fun _ => 0
  let u0 : Fin N → ℤ := fun j => if j = inp then ((x.length - 1 : ℕ) : ℤ) else 0
  have hw0 : ∀ j, l0 j ≤ p0 j ∧ p0 j ≤ u0 j := by
    intro j; by_cases hj : j = inp <;> simp [l0, p0, u0, hj]
  have hinit_eq : locatedInit M x =
      ⟨⟨.inr M.start, t0⟩, p0, l0, u0⟩ := by
    apply loc_ext
    · apply cfg_ext'
      · rfl
      · funext j; exact locatedInit_tapes (compProgram A oa B ob D od E) inp x j
    · rfl
    · rfl
    · funext j; exact locatedInit_upper (compProgram A oa B ob D od E) inp x j
  have hspan0' : spanSum l0 u0 ≤ N + x.length := by
    unfold spanSum
    calc ∑ j : Fin N, (u0 j - l0 j + 1).toNat
        ≤ ∑ j : Fin N, (1 + if j = inp then x.length else 0) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j = inp <;> simp [l0, u0, hj] <;> omega
      _ = N + x.length := by
          simp [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  -- Phase 1: copy2Forward inp inA inB
  rcases copy2Forward_run inp inA inB inp
      (in_ne_fA A B D E A.inputTape) (in_ne_fB A B D E B.inputTape)
      (fA_ne_fB A B D E A.inputTape B.inputTape)
      [] x [] [] t0 p0 l0 u0 hw0 (by simp [t0])
      (by dsimp only [t0, inp, inA, gA]; rw [if_neg (in_ne_fA A B D E A.inputTape).symm])
      (by dsimp only [t0, inp, inB, gB]; rw [if_neg (in_ne_fB A B D E B.inputTape).symm]) with
    ⟨t1, p1, u1, htr1, h1inp, h1inA, h1inB, h1oth, hp1inp, hp1inA, hp1inB, hw1, hu1_ge, hsp1⟩
  -- Phase 2: rewindProgram inp
  have hl1 : l0 inp ≤ 0 := by simp [l0]
  rcases rewindProgram_run inp inp x t1 p1 l0 u1 hw1 hl1 (by simpa using h1inp)
      (by simpa [p0] using hp1inp) with
    ⟨t2, p2, l2, u2, htr2, h2inp, hp2inp, h2oth, hw2, hsp2, hlu2⟩
  have htr_2 := seqProg_trace inp Q1 (rewindProgram inp) hw0 htr1 htr2
  -- Phase 3: rewindProgram inA
  have h2inA : t2 inA = bTape x.reverse [] := by
    have := (h2oth inA (in_ne_fA A B D E A.inputTape).symm).1
    simpa [this] using h1inA
  have hp2inA : p2 inA = x.length := by
    have := (h2oth inA (in_ne_fA A B D E A.inputTape).symm).2
    simpa [this, p0] using hp1inA
  have hl2inA : l2 inA ≤ 0 := le_trans (hlu2 inA).1 (by simp [l0])
  rcases rewindProgram_run inA inp x t2 p2 l2 u2 hw2 hl2inA h2inA hp2inA with
    ⟨t3, p3, l3, u3, htr3, h3inA, hp3inA, h3oth, hw3, hsp3, hlu3⟩
  have htr_3 := seqProg_trace inp Q2 (rewindProgram inA) hw0 htr_2 htr3
  -- Phase 4: rewindProgram inB
  have h3inB : t3 inB = bTape x.reverse [] := by
    have h2b := (h2oth inB (in_ne_fB A B D E B.inputTape).symm).1
    have h3b := (h3oth inB (fA_ne_fB A B D E A.inputTape B.inputTape).symm).1
    simpa [h3b, h2b] using h1inB
  have hp3inB : p3 inB = x.length := by
    have h2b := (h2oth inB (in_ne_fB A B D E B.inputTape).symm).2
    have h3b := (h3oth inB (fA_ne_fB A B D E A.inputTape B.inputTape).symm).2
    simpa [h3b, h2b, p0] using hp1inB
  have hl3inB : l3 inB ≤ 0 := le_trans (hlu3 inB).1 (le_trans (hlu2 inB).1 (by simp [l0]))
  rcases rewindProgram_run inB inp x t3 p3 l3 u3 hw3 hl3inB h3inB hp3inB with
    ⟨t4, p4, l4, u4, htr4, h4inB, hp4inB, h4oth, hw4, hsp4, hlu4⟩
  have htr_4 := seqProg_trace inp Q3 (rewindProgram inB) hw0 htr_3 htr4
  -- Preconditions for embedProgram A gA
  have h4inA : t4 inA = bTape [] x := by
    rw [(h4oth inA (fA_ne_fB A B D E A.inputTape B.inputTape)).1]; exact h3inA
  have hp4inA : p4 inA = 0 := by
    rw [(h4oth inA (fA_ne_fB A B D E A.inputTape B.inputTape)).2]; exact hp3inA
  have ht4_A_blank : ∀ i, i ≠ A.inputTape → t4 (gA i) = bTape [] [] := by
    intro i hi
    have h4i := (h4oth (gA i) (fA_ne_fB A B D E i B.inputTape)).1
    have h3i := (h3oth (gA i) (fun heq => hi ((fA_inj A B D E) heq))).1
    have h2i := (h2oth (gA i) (in_ne_fA A B D E i).symm).1
    have h1i := (h1oth (gA i) (in_ne_fA A B D E i).symm (fun heq => hi ((fA_inj A B D E) heq))
      (fA_ne_fB A B D E i B.inputTape)).1
    rw [h4i, h3i, h2i, h1i]
    dsimp only [t0, inp, gA]
    rw [if_neg (in_ne_fA A B D E i).symm]
  have hp4_A : ∀ i, p4 (gA i) = 0 := by
    intro i
    by_cases hi : i = A.inputTape
    · subst hi; exact hp4inA
    · have h4i := (h4oth (gA i) (fA_ne_fB A B D E i B.inputTape)).2
      have h3i := (h3oth (gA i) (fun heq => hi ((fA_inj A B D E) heq))).2
      have h2i := (h2oth (gA i) (in_ne_fA A B D E i).symm).2
      have h1i := (h1oth (gA i) (in_ne_fA A B D E i).symm (fun heq => hi ((fA_inj A B D E) heq))
        (fA_ne_fB A B D E i B.inputTape)).2.1
      rw [h4i, h3i, h2i, h1i]
  have hu4_inA : ((x.length - 1 : ℕ) : ℤ) ≤ u4 inA := by
    have h1 : ((x.length : ℕ) : ℤ) ≤ u1 inA := by
      have := (hw1 inA).2; linarith [hp1inA]
    have hu14 : u1 inA ≤ u4 inA :=
      le_trans (hlu2 inA).2 (le_trans (hlu3 inA).2 (hlu4 inA).2)
    omega
  -- Phase 5: embedProgram A gA
  rcases embedProgram_run A gA (fA_inj A B D E) oa inp hA t4 p4 l4 u4 hw4
      h4inA ht4_A_blank hp4_A hu4_inA with
    ⟨nA, ansA, t5, p5, l5, u5, htr5, hnA_le, hw5, hsp5, h5outA, h5oth, hlu5⟩
  have htr_5 := seqProg_trace inp Q4 (embedProgram A gA) hw0 htr_4 htr5
  -- Preconditions for embedProgram B gB
  have h5inB : t5 inB = bTape [] x := by
    rw [(h5oth inB (fun i => fA_ne_fB A B D E i B.inputTape)).1]; exact h4inB
  have hp5inB : p5 inB = 0 := by
    rw [(h5oth inB (fun i => fA_ne_fB A B D E i B.inputTape)).2.1]; exact hp4inB
  have ht5_B_blank : ∀ i, i ≠ B.inputTape → t5 (gB i) = bTape [] [] := by
    intro i hi
    have h5i := (h5oth (gB i) (fun j => fA_ne_fB A B D E j i)).1
    have h4i := (h4oth (gB i) (fun heq => hi ((fB_inj A B D E) heq))).1
    have h3i := (h3oth (gB i) (fA_ne_fB A B D E A.inputTape i).symm).1
    have h2i := (h2oth (gB i) (in_ne_fB A B D E i).symm).1
    have h1i := (h1oth (gB i) (in_ne_fB A B D E i).symm (fA_ne_fB A B D E A.inputTape i).symm
      (fun heq => hi ((fB_inj A B D E) heq))).1
    rw [h5i, h4i, h3i, h2i, h1i]
    dsimp only [t0, inp, gB]
    rw [if_neg (in_ne_fB A B D E i).symm]
  have hp5_B : ∀ i, p5 (gB i) = 0 := by
    intro i
    by_cases hi : i = B.inputTape
    · subst hi; exact hp5inB
    · have h5i := (h5oth (gB i) (fun j => fA_ne_fB A B D E j i)).2.1
      have h4i := (h4oth (gB i) (fun heq => hi ((fB_inj A B D E) heq))).2
      have h3i := (h3oth (gB i) (fA_ne_fB A B D E A.inputTape i).symm).2
      have h2i := (h2oth (gB i) (in_ne_fB A B D E i).symm).2
      have h1i := (h1oth (gB i) (in_ne_fB A B D E i).symm (fA_ne_fB A B D E A.inputTape i).symm
        (fun heq => hi ((fB_inj A B D E) heq))).2.1
      rw [h5i, h4i, h3i, h2i, h1i]
  have hu5_inB : ((x.length - 1 : ℕ) : ℤ) ≤ u5 inB := by
    have h1 : ((x.length : ℕ) : ℤ) ≤ u1 inB := by
      have := (hw1 inB).2; linarith [hp1inB]
    have hu15 : u1 inB ≤ u5 inB :=
      le_trans (hlu2 inB).2 (le_trans (hlu3 inB).2 (le_trans (hlu4 inB).2 (hlu5 inB).2))
    omega
  -- Phase 6: embedProgram B gB
  rcases embedProgram_run B gB (fB_inj A B D E) ob inp hB t5 p5 l5 u5 hw5
      h5inB ht5_B_blank hp5_B hu5_inB with
    ⟨nB, ansB, t6, p6, l6, u6, htr6, hnB_le, hw6, hsp6, h6outB, h6oth, hlu6⟩
  have htr_6 := seqProg_trace inp Q5 (embedProgram B gB) hw0 htr_5 htr6
  -- Preserved facts at Phase 6
  have h6_D_tapes : ∀ i, t6 (gD i) = bTape [] [] ∧ p6 (gD i) = 0 := by
    intro i
    have h6i := h6oth (gD i) (fun j => fB_ne_fD A B D E j i)
    have h5i := h5oth (gD i) (fun j => fA_ne_fD A B D E j i)
    have h4i := h4oth (gD i) (fB_ne_fD A B D E B.inputTape i).symm
    have h3i := h3oth (gD i) (fA_ne_fD A B D E A.inputTape i).symm
    have h2i := h2oth (gD i) (in_ne_fD A B D E i).symm
    have h1i := h1oth (gD i) (in_ne_fD A B D E i).symm
      (fA_ne_fD A B D E A.inputTape i).symm (fB_ne_fD A B D E B.inputTape i).symm
    refine ⟨?_, ?_⟩
    · rw [h6i.1, h5i.1, h4i.1, h3i.1, h2i.1, h1i.1]
      dsimp only [t0, inp, gD]
      rw [if_neg (in_ne_fD A B D E i).symm]
    · rw [h6i.2.1, h5i.2.1, h4i.2, h3i.2, h2i.2, h1i.2.1]
  have h6_E_tapes : ∀ i, t6 (gE i) = bTape [] [] ∧ p6 (gE i) = 0 := by
    intro i
    have h6i := h6oth (gE i) (fun j => fB_ne_fE A B D E j i)
    have h5i := h5oth (gE i) (fun j => fA_ne_fE A B D E j i)
    have h4i := h4oth (gE i) (fB_ne_fE A B D E B.inputTape i).symm
    have h3i := h3oth (gE i) (fA_ne_fE A B D E A.inputTape i).symm
    have h2i := h2oth (gE i) (in_ne_fE A B D E i).symm
    have h1i := h1oth (gE i) (in_ne_fE A B D E i).symm
      (fA_ne_fE A B D E A.inputTape i).symm (fB_ne_fE A B D E B.inputTape i).symm
    refine ⟨?_, ?_⟩
    · rw [h6i.1, h5i.1, h4i.1, h3i.1, h2i.1, h1i.1]
      dsimp only [t0, inp, gE]
      rw [if_neg (in_ne_fE A B D E i).symm]
    · rw [h6i.2.1, h5i.2.1, h4i.2, h3i.2, h2i.2, h1i.2.1]
  have h6inp : t6 inp = bTape [] x := by
    rw [(h6oth inp (fun j => (in_ne_fB A B D E j).symm)).1]
    rw [(h5oth inp (fun j => (in_ne_fA A B D E j).symm)).1]
    rw [(h4oth inp (in_ne_fB A B D E B.inputTape)).1]
    rw [(h3oth inp (in_ne_fA A B D E A.inputTape)).1]
    exact h2inp
  have h6outA : t6 outA = bTape [] a := by
    rw [(h6oth outA (fun j => (fA_ne_fB A B D E oa j).symm)).1]
    exact h5outA
  have hl6_le_zero : ∀ j, l6 j ≤ 0 := fun j =>
    le_trans (hlu6 j).1 (le_trans (hlu5 j).1 (le_trans (hlu4 j).1
      (le_trans (hlu3 j).1 (le_trans (hlu2 j).1 (by simp [l0])))))
  -- Phase 7: copy1Forward outB inD
  rcases copy1Forward_run outB inD inp (fB_ne_fD A B D E ob D.inputTape)
      [] b [] t6 p6 l6 u6 hw6 h6outB (h6_D_tapes D.inputTape).1 with
    ⟨t7, p7, u7, htr7, h7outB, h7inD, h7oth, hp7outB, hp7inD, hw7, hu7_ge, hsp7⟩
  have htr_7 := seqProg_trace inp Q6 (copy1Forward outB inD) hw0 htr_6 htr7
  -- Phase 8: rewindProgram inD
  have hp7inD' : p7 inD = b.length := by
    rw [hp7inD, (h6_D_tapes D.inputTape).2, zero_add]
  rcases rewindProgram_run inD inp b t7 p7 l6 u7 hw7 (hl6_le_zero inD)
      (by simpa using h7inD) hp7inD' with
    ⟨t8, p8, l8, u8, htr8, h8inD, hp8inD, h8oth, hw8, hsp8, hlu8⟩
  have htr_8 := seqProg_trace inp Q7 (rewindProgram inD) hw0 htr_7 htr8
  -- Preconditions for embedProgram D gD
  have ht8_D_blank : ∀ i, i ≠ D.inputTape → t8 (gD i) = bTape [] [] := by
    intro i hi
    have h8i := (h8oth (gD i) (fun heq => hi ((fD_inj A B D E) heq))).1
    have h7i := (h7oth (gD i) (fB_ne_fD A B D E ob i).symm
      (fun heq => hi ((fD_inj A B D E) heq))).1
    rw [h8i, h7i]
    exact (h6_D_tapes i).1
  have hp8_D : ∀ i, p8 (gD i) = 0 := by
    intro i
    by_cases hi : i = D.inputTape
    · subst hi; exact hp8inD
    · have h8i := (h8oth (gD i) (fun heq => hi ((fD_inj A B D E) heq))).2
      have h7i := (h7oth (gD i) (fB_ne_fD A B D E ob i).symm
        (fun heq => hi ((fD_inj A B D E) heq))).2.1
      rw [h8i, h7i]
      exact (h6_D_tapes i).2
  have hu8_inD : ((b.length - 1 : ℕ) : ℤ) ≤ u8 inD := by
    have h7 : ((b.length : ℕ) : ℤ) ≤ u7 inD := by
      have := (hw7 inD).2; linarith [hp7inD']
    have hu78 := (hlu8 inD).2
    omega
  -- Phase 9: embedProgram D gD
  rcases embedProgram_run D gD (fD_inj A B D E) od inp hD t8 p8 l8 u8 hw8
      h8inD ht8_D_blank hp8_D hu8_inD with
    ⟨nD, ansD, t9, p9, l9, u9, htr9, hnD_le, hw9, hsp9, h9outD, h9oth, hlu9⟩
  have htr_9 := seqProg_trace inp Q8 (embedProgram D gD) hw0 htr_8 htr9
  -- Preserved facts at Phase 9
  have h9inp : t9 inp = bTape [] x := by
    rw [(h9oth inp (fun i => (in_ne_fD A B D E i).symm)).1]
    rw [(h8oth inp (in_ne_fD A B D E D.inputTape)).1]
    rw [(h7oth inp (in_ne_fB A B D E ob) (in_ne_fD A B D E D.inputTape)).1]
    exact h6inp
  have h9outA : t9 outA = bTape [] a := by
    rw [(h9oth outA (fun i => (fA_ne_fD A B D E oa i).symm)).1]
    rw [(h8oth outA (fA_ne_fD A B D E oa D.inputTape)).1]
    rw [(h7oth outA (fA_ne_fB A B D E oa ob) (fA_ne_fD A B D E oa D.inputTape)).1]
    exact h6outA
  have h9_E_tapes : ∀ i, t9 (gE i) = bTape [] [] ∧ p9 (gE i) = 0 := by
    intro i
    have h9i := h9oth (gE i) (fun j => fD_ne_fE A B D E j i)
    have h8i := h8oth (gE i) (fD_ne_fE A B D E D.inputTape i).symm
    have h7i := h7oth (gE i) (fB_ne_fE A B D E ob i).symm
      (fD_ne_fE A B D E D.inputTape i).symm
    refine ⟨?_, ?_⟩
    · rw [h9i.1, h8i.1, h7i.1]; exact (h6_E_tapes i).1
    · rw [h9i.2.1, h8i.2, h7i.2.1]; exact (h6_E_tapes i).2
  have hl9_le_zero : ∀ j, l9 j ≤ 0 := fun j =>
    le_trans (hlu9 j).1 (le_trans (hlu8 j).1 (hl6_le_zero j))
  -- Phase 10: appendFrame inp inE
  rcases appendFrame_run inp inE inp (in_ne_fE A B D E E.inputTape)
      x [] t9 p9 l9 u9 hw9 h9inp (h9_E_tapes E.inputTape).1 with
    ⟨t10, p10, u10, htr10, h10inE, h10oth, hp10inE, hw10, hu10_ge, hsp10⟩
  have htr_10 := seqProg_trace inp Q9 (appendFrame inp inE) hw0 htr_9 htr10
  -- Phase 11: appendFrame outA inE
  have h10outA : t10 outA = bTape [] a := by
    rw [(h10oth outA (in_ne_fA A B D E oa).symm (fA_ne_fE A B D E oa E.inputTape)).1]
    exact h9outA
  rcases appendFrame_run outA inE inp (fA_ne_fE A B D E oa E.inputTape)
      a ((true :: Encoding.frame x).reverse ++ []) t10 p10 l9 u10 hw10 h10outA h10inE with
    ⟨t11, p11, u11, htr11, h11inE, h11oth, hp11inE, hw11, hu11_ge, hsp11⟩
  have htr_11 := seqProg_trace inp Q10 (appendFrame outA inE) hw0 htr_10 htr11
  -- Phase 12: appendFrame outD inE
  have h11outD : t11 outD = bTape [] d := by
    rw [(h11oth outD (fA_ne_fD A B D E oa od).symm (fD_ne_fE A B D E od E.inputTape)).1]
    rw [(h10oth outD (in_ne_fD A B D E od).symm (fD_ne_fE A B D E od E.inputTape)).1]
    exact h9outD
  rcases appendFrame_run outD inE inp (fD_ne_fE A B D E od E.inputTape)
      d ((true :: Encoding.frame a).reverse ++ ((true :: Encoding.frame x).reverse ++ []))
      t11 p11 l9 u11 hw11 h11outD h11inE with
    ⟨t12, p12, u12, htr12, h12inE, h12oth, hp12inE, hw12, hu12_ge, hsp12⟩
  have htr_12 := seqProg_trace inp Q11 (appendFrame outD inE) hw0 htr_11 htr12
  -- Phase 13: appendFalse inE
  rcases appendFalse_run inE inp
      ((true :: Encoding.frame d).reverse ++
        ((true :: Encoding.frame a).reverse ++ ((true :: Encoding.frame x).reverse ++ [])))
      t12 p12 l9 u12 hw12 h12inE with
    ⟨t13, p13, u13, htr13, h13inE, h13oth, hp13inE, hw13, hu13_ge, hsp13⟩
  have htr_13 := seqProg_trace inp Q12 (appendFalse inE) hw0 htr_12 htr13
  -- Preconditions for rewindProgram inE
  have h13inE_pack : t13 inE = bTape pack.reverse [] := by
    have hrev : pack.reverse = false :: ((true :: Encoding.frame d).reverse ++
        ((true :: Encoding.frame a).reverse ++ ((true :: Encoding.frame x).reverse ++ []))) := by
      dsimp [pack]
      rw [encodeList3_eq]
      simp [List.append_assoc]
    rw [hrev]
    exact h13inE
  have hp13inE_len : p13 inE = pack.length := by
    have hp9 : p9 inE = 0 := (h9_E_tapes E.inputTape).2
    have hlen : pack.length = (true :: Encoding.frame x).length + (true :: Encoding.frame a).length +
        (true :: Encoding.frame d).length + 1 := by
      dsimp [pack]
      rw [encodeList3_eq]
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hp13inE, hp12inE, hp11inE, hp10inE, hp9, hlen]
    push_cast
    ring
  -- Phase 14: rewindProgram inE
  rcases rewindProgram_run inE inp pack t13 p13 l9 u13 hw13 (hl9_le_zero inE)
      h13inE_pack hp13inE_len with
    ⟨t14, p14, l14, u14, htr14, h14inE, hp14inE, h14oth, hw14, hsp14, hlu14⟩
  have htr_14 := seqProg_trace inp Q13 (rewindProgram inE) hw0 htr_13 htr14
  -- Preconditions for embedProgram E gE
  have ht14_E_blank : ∀ i, i ≠ E.inputTape → t14 (gE i) = bTape [] [] := by
    intro i hi
    have hne : gE i ≠ inE := fun heq => hi (fE_inj A B D E heq)
    have h14i := (h14oth (gE i) hne).1
    have h13i := (h13oth (gE i) hne).1
    have h12i := (h12oth (gE i) (fD_ne_fE A B D E od i).symm hne).1
    have h11i := (h11oth (gE i) (fA_ne_fE A B D E oa i).symm hne).1
    have h10i := (h10oth (gE i) (in_ne_fE A B D E i).symm hne).1
    rw [h14i, h13i, h12i, h11i, h10i]
    exact (h9_E_tapes i).1
  have hp14_E : ∀ i, p14 (gE i) = 0 := by
    intro i
    by_cases hi : i = E.inputTape
    · subst hi; exact hp14inE
    · have hne : gE i ≠ inE := fun heq => hi (fE_inj A B D E heq)
      have h14i := (h14oth (gE i) hne).2
      have h13i := (h13oth (gE i) hne).2.1
      have h12i := (h12oth (gE i) (fD_ne_fE A B D E od i).symm hne).2.1
      have h11i := (h11oth (gE i) (fA_ne_fE A B D E oa i).symm hne).2.1
      have h10i := (h10oth (gE i) (in_ne_fE A B D E i).symm hne).2.1
      rw [h14i, h13i, h12i, h11i, h10i]
      exact (h9_E_tapes i).2
  have hu14_inE : ((pack.length - 1 : ℕ) : ℤ) ≤ u14 inE := by
    have h13 : ((pack.length : ℕ) : ℤ) ≤ u13 inE := by
      have := (hw13 inE).2; linarith [hp13inE_len]
    have hu1314 := (hlu14 inE).2
    omega
  -- Phase 15: embedProgram E gE
  rcases embedProgram_run E gE (fE_inj A B D E) oe inp hE t14 p14 l14 u14 hw14
      h14inE ht14_E_blank hp14_E hu14_inE with
    ⟨nE, ansE, t15, p15, l15, u15, htr15, hnE_le, hw15, hsp15, h15outE, _, _⟩
  have htr_15 := seqProg_trace inp Q14 (embedProgram E gE) hw0 htr_14 htr15
  -- Complexity bounds
  have hb_bit : 1 ≤ bitLen p := one_le_bitLen hp
  have hW_ge : 1 ≤ W := one_le_mainSpaceBound k (bitLen p) hb_bit
  have hx_le : (x.length : ℝ) ≤ W + 1 := runsWithin_input_length_le hA
  have ha_le : (a.length : ℝ) ≤ W + 1 := runsWithin_output_length_le hA
  have hb_le : (b.length : ℝ) ≤ W + 1 := runsWithin_output_length_le hB
  have hd_le : (d.length : ℝ) ≤ (W + 1) * ((b.length : ℝ) + 1) := runsWithin_output_length_le hD
  have hpack_len : (pack.length : ℝ) =
      2 * (x.length : ℝ) + 2 * (a.length : ℝ) + 2 * (d.length : ℝ) + 7 := by
    exact_mod_cast encodeList3_length x a d
  have hpoly : ((N + 720 : ℕ) : ℝ) * W ^ 3 ≤ mainSpaceBound c (bitLen p) := by
    exact poly_le_mainSpaceBound k (N + 720) (bitLen p) hb_bit
  let totalSteps : ℕ :=
    5 * x.length + 1 + (x.length + 3) + (x.length + 3) + (x.length + 3) + nA + nB +
      (3 * b.length + 1) + (b.length + 3) + nD + (5 * x.length + 6) + (5 * a.length + 6) +
      (5 * d.length + 6) + 3 + (pack.length + 3) + nE
  apply (runsWithin_iff_final_space M o x e _ _).2
  refine ⟨totalSteps, ⟨⟨.inl ansE, t15⟩, p15, l15, u15⟩, ?_, ⟨ansE, rfl⟩, ?_, ?_, ?_⟩
  · rw [hinit_eq]; exact htr_15
  · dsimp only [o]; exact h15outE
  · dsimp only [totalSteps]
    push_cast
    exact le_trans (four_call_time_bound hW_ge hx_le ha_le hb_le hd_le hpack_len
      hnA_le hnB_le hnD_le hnE_le) hpoly
  · change (spanSum l15 u15 : ℝ) ≤ mainSpaceBound c (bitLen p)
    have h0r : (spanSum l0 u0 : ℝ) ≤ (N : ℝ) + (x.length : ℝ) := by exact_mod_cast hspan0'
    have h1r : (spanSum l0 u1 : ℝ) ≤ (spanSum l0 u0 : ℝ) + 3 * (x.length : ℝ) := by exact_mod_cast hsp1
    have h2r : (spanSum l2 u2 : ℝ) ≤ (spanSum l0 u1 : ℝ) + 1 := by exact_mod_cast hsp2
    have h3r : (spanSum l3 u3 : ℝ) ≤ (spanSum l2 u2 : ℝ) + 1 := by exact_mod_cast hsp3
    have h4r : (spanSum l4 u4 : ℝ) ≤ (spanSum l3 u3 : ℝ) + 1 := by exact_mod_cast hsp4
    have h7r : (spanSum l6 u7 : ℝ) ≤ (spanSum l6 u6 : ℝ) + 2 * (b.length : ℝ) := by exact_mod_cast hsp7
    have h8r : (spanSum l8 u8 : ℝ) ≤ (spanSum l6 u7 : ℝ) + 1 := by exact_mod_cast hsp8
    have h10r : (spanSum l9 u10 : ℝ) ≤ (spanSum l9 u9 : ℝ) + (3 * (x.length : ℝ) + 2) := by
      exact_mod_cast hsp10
    have h11r : (spanSum l9 u11 : ℝ) ≤ (spanSum l9 u10 : ℝ) + (3 * (a.length : ℝ) + 2) := by
      exact_mod_cast hsp11
    have h12r : (spanSum l9 u12 : ℝ) ≤ (spanSum l9 u11 : ℝ) + (3 * (d.length : ℝ) + 2) := by
      exact_mod_cast hsp12
    have h13r : (spanSum l9 u13 : ℝ) ≤ (spanSum l9 u12 : ℝ) + 1 := by exact_mod_cast hsp13
    have h14r : (spanSum l14 u14 : ℝ) ≤ (spanSum l9 u13 : ℝ) + 1 := by exact_mod_cast hsp14
    exact le_trans (four_call_space_bound hW_ge hx_le ha_le hb_le hd_le hpack_len
      h0r h1r h2r h3r h4r hsp5 hsp6 h7r h8r hsp9 h10r h11r h12r h13r h14r hsp15) hpoly

end MainComposition

end DetDLP.M89FourCall

open DetDLP DetDLP.M89FourCall OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem solution
    (A : PrimitiveMachine) (oa : Fin A.tapeCount) (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) (oe : Fin E.tapeCount)
    (k : ℕ) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (c : ℕ),
      ∀ (p : ℕ), 2 ≤ p → ∀ (x a b d e : List Bool),
        let W := mainSpaceBound k (bitLen p)
        let pack := Encoding.encodeList id [x,a,d]
        RunsWithin A oa x a (W+1) (W+1) → RunsWithin B ob x b (W+1) (W+1) →
        RunsWithin D od b d ((W+1)*(b.length+1)) ((W+1)*(b.length+1)) →
        RunsWithin E oe pack e ((W+1)*(pack.length+1)) ((W+1)*(pack.length+1)) →
        RunsWithin M o x e (mainSpaceBound c (bitLen p)) (mainSpaceBound c (bitLen p)) :=
  ⟨(compProgram A oa B ob D od E).machine (inIdx A B D E),
    fE A B D E oe,
    3 * k + (compTapes A B D E + 720),
    compProgram_runsWithin A oa B ob D od E oe k⟩
