-- Prove2me | solution 1 for Freiman.other22_geometry_goodness
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T20:29:50.331733+00:00
-- url     : https://prove2.me/submissions/416eee50-3939-4a3f-a685-9f0e007a96a3

import Definitions.Def_Freiman_other22Verification
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Theorems.Thm_Freiman_lowerHistory_inv_value
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics
import Theorems.Thm_Freiman_lowerHistory_pull_value
import Mathlib.Tactic

open Freiman
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

-- Positivity and context lemmas adapted from accepted submission
-- d769562b-25b8-4db6-b0a7-965e4e05818d (lowerHistory_reached_goodness).
namespace M7Goodness14

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih =>
    simp only [prefixEval]
    positivity

private theorem tau_nonneg : 0 ≤ certFieldVal lowerHistoryTau := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [certFieldVal, lowerHistoryTau]

private theorem endval_nonneg (C : LowerHistoryContext) (w : LowerPair)
    (upper side short : Bool) :
    0 ≤ certFieldVal (lowerHistoryEndVal C w upper side short) := by
  unfold lowerHistoryEndVal
  rw [lowerHistory_cf_value _ _ tau_nonneg]
  exact prefix_nonneg _ _ tau_nonneg

private theorem equal_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEqualCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  by_cases hn : (lowerHistoryNatural C w upper false ||
      lowerHistoryNatural C w upper true) = true
  · simp only [lowerHistoryEqualCases, hn, ↓reduceIte,
      List.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, rfl⟩
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
  · dsimp only [lowerHistoryEqualCases] at hz
    rw [if_neg hn] at hz
    simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, shortened, _, heq⟩ := hz
    cases heq
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem endpoint_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  unfold lowerHistoryEndpointCases at hz
  split_ifs at hz with hp
  · exact equal_nonneg C w upper z cs hz
  · simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, ⟨v,bs⟩, hv, heq⟩ := hz
    cases heq
    split_ifs at hv
    · exact equal_nonneg _ _ _ _ _ hv
    · simp only [List.mem_singleton, Prod.mk.injEq] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩


end M7Goodness14

namespace Stage13GreaterSigns
private theorem field_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h3 : Real.sqrt (3:ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt (7:ℝ)^2 = 7 := Real.sq_sqrt (by norm_num)
  have h37 : Real.sqrt (21:ℝ) = Real.sqrt 3 * Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  simp only [certFieldVal, certFieldMul]
  push_cast
  rw [h37]
  ring_nf
  simp only [h3,h7]
  ring

private theorem field_abs
    (hsg : ∀ z : CertField,
      (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z)) (z : CertField) :
    certFieldVal (lowerHistoryAbs z) = |certFieldVal z| := by
  unfold lowerHistoryAbs
  split_ifs with h
  · have hn : certFieldVal z < 0 := by
      rcases lt_trichotomy (certFieldVal z) 0 with hz | hz | hz
      · exact hz
      · have := (hsg z).1.mpr hz; omega
      · have := (hsg z).2.mpr hz; omega
    rw [abs_of_neg hn]
    simp only [lowerHistoryNeg, certFieldScale, certFieldVal]
    push_cast
    ring
  · rw [abs_of_nonneg]
    by_contra hn
    have hz : certFieldVal z < 0 := lt_of_not_ge hn
    have hsn : 0 ≤ lowerHistorySign z := le_of_not_gt h
    rcases eq_or_lt_of_le hsn with he | hp
    · have := (hsg z).1.mp he.symm; linarith
    · have := (hsg z).2.mp hp; linarith




end Stage13GreaterSigns

namespace GoodFields15

private def Valid (b : CertBound) : Prop :=
  0 < certFieldVal b.threshold.c ∧
  0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
  0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1

private theorem extreme_nonneg (maximum : Bool) (zs : List CertField)
    (hz : ∀ z ∈ zs, 0 ≤ certFieldVal z) :
    0 ≤ certFieldVal (lowerHistoryExtreme maximum zs) := by
  have hf (xs : List CertField) (a : CertField) (ha : 0 ≤ certFieldVal a)
      (hxs : ∀ z ∈ xs, 0 ≤ certFieldVal z) :
      0 ≤ certFieldVal (xs.foldl (fun a b =>
        if decide (0 < lowerHistorySign (certFieldSub b a)) = maximum then b else a) a) := by
    induction xs generalizing a with
    | nil => exact ha
    | cons b xs ih =>
      simp only [List.foldl_cons]
      split_ifs
      · exact ih b (hxs b (by simp)) (fun z hz => hxs z (by simp [hz]))
      · exact ih a ha (fun z hz => hxs z (by simp [hz]))
  cases zs with
  | nil => norm_num [lowerHistoryExtreme,lowerHistoryRat,certFieldVal]
  | cons a xs =>
    exact hf (a::xs) a (hz a (by simp)) hz

private def hull (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : CertField × CertField :=
  let es := lowerHistoryEndpointCases C w upper
  (lowerHistoryExtreme (upper.xor C.parity.1) (es.map (fun z => z.1.1)),
   lowerHistoryExtreme (upper.xor C.parity.2) (es.map (fun z => z.1.2)))

private theorem hull_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) :
    0 ≤ certFieldVal (hull C w upper).1 ∧ 0 ≤ certFieldVal (hull C w upper).2 := by
  constructor
  · apply extreme_nonneg
    intro a ha
    obtain ⟨⟨z,cs⟩,hz,rfl⟩ := List.mem_map.mp ha
    exact (M7Goodness14.endpoint_nonneg C w upper z cs hz).1
  · apply extreme_nonneg
    intro a ha
    obtain ⟨⟨z,cs⟩,hz,rfl⟩ := List.mem_map.mp ha
    exact (M7Goodness14.endpoint_nonneg C w upper z cs hz).2

private theorem bound_fields (C : LowerHistoryContext) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2)
    (b : CertBound) (hg : lowerHistoryGreater C x y = .bound b) : Valid b := by
  let dx := certFieldSub x.1 y.1
  let dy := certFieldSub x.2 y.2
  let sx := (if C.parity.1 then -1 else 1 : ℤ) * lowerHistorySign dx
  let sy := (if C.parity.2 then -1 else 1 : ℤ) * lowerHistorySign dy
  change (if 0 ≤ sx ∧ 0 ≤ sy then LowerHistoryComparison.automatic else
    if sx ≤ 0 ∧ sy ≤ 0 then LowerHistoryComparison.impossible else LowerHistoryComparison.bound
      ⟨decide (sx < 0),false,lowerHistoryThreshold
        (lowerHistoryAbs (lowerHistoryDiv dx dy)) (x.1,y.1) (x.2,y.2)⟩) = LowerHistoryComparison.bound b at hg
  split_ifs at hg with hp hn <;> try contradiction
  have hsx : sx ≠ 0 := by intro h; omega
  have hsy : sy ≠ 0 := by intro h; omega
  have hdx : certFieldVal dx ≠ 0 := by
    intro h
    apply hsx
    simp [sx,(lowerHistory_sign_value dx).1.mpr h]
  have hdy : certFieldVal dy ≠ 0 := by
    intro h
    apply hsy
    simp [sy,(lowerHistory_sign_value dy).1.mpr h]
  have hc : 0 < certFieldVal (lowerHistoryAbs (lowerHistoryDiv dx dy)) := by
    rw [Stage13GreaterSigns.field_abs lowerHistory_sign_value]
    unfold lowerHistoryDiv
    rw [Stage13GreaterSigns.field_mul,lowerHistory_inv_value dy hdy]
    exact abs_pos.mpr (mul_ne_zero hdx (inv_ne_zero hdy))
  injection hg with hb
  subst b
  unfold Valid lowerHistoryThreshold lowerHistorySort
  split <;> split <;> simp_all

private def envelopeComparison (C : LowerHistoryContext) (u v : LowerPair) : LowerHistoryComparison :=
  lowerHistoryGreater C (hull C u true) (hull C v false)

private def comparisonBounds : LowerHistoryComparison → Option (List CertBound)
  | .automatic => some []
  | .impossible => none
  | .bound b => some [b]

private theorem relaxed_unroll (C : LowerHistoryContext) :
    lowerHistoryRelaxedGoodness C =
      (comparisonBounds (envelopeComparison C ([1],[]) ([2],[]))).bind (fun bs =>
        (comparisonBounds (envelopeComparison C ([2],[]) ([1],[]))).map (fun cs => bs ++ cs)) := by
  unfold lowerHistoryRelaxedGoodness envelopeComparison hull comparisonBounds
  simp only [Bool.true_xor, Bool.false_xor]
  split <;> split <;> simp_all [List.forIn_cons, List.forIn_nil]

private theorem envelope_fields (C : LowerHistoryContext) (u v : LowerPair)
    (bs : List CertBound) (he : comparisonBounds (envelopeComparison C u v) = some bs) :
    ∀ b ∈ bs, Valid b := by
  cases hg : envelopeComparison C u v with
  | automatic =>
    have heq : bs = [] := by simpa [hg,comparisonBounds] using he
    simp [heq]
  | impossible => simp [hg,comparisonBounds] at he
  | bound b =>
    have hb : [b] = bs := by simpa [hg,comparisonBounds] using he
    subst bs
    intro a ha
    have heq : a = b := by simpa using ha
    subst a
    exact bound_fields C _ _ (hull_nonneg C u true) (hull_nonneg C v false) b hg

private theorem relaxed_fields (C : LowerHistoryContext) (bs : List CertBound)
    (h : lowerHistoryRelaxedGoodness C = some bs) : ∀ b ∈ bs, Valid b := by
  rw [relaxed_unroll] at h
  obtain ⟨xs,hxs,hmap⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys,hys,hbs⟩ := Option.map_eq_some_iff.mp hmap
  subst bs
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact envelope_fields C _ _ xs hxs b hb
  · exact envelope_fields C _ _ ys hys b hb

end GoodFields15

namespace ReachedGood15

private theorem rawStep_append (base words : LowerPair) (wide : Bool) (l : LowerLabel) :
    lowerHistoryRawStep (lowerHistoryAppend base words) wide l =
      lowerHistoryAppend base (lowerHistoryRawStep words wide l) := by
  cases wide <;> simp [lowerHistoryRawStep, lowerHistoryAppend, List.append_assoc]

private theorem fold_append (base : LowerPair) :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool),
      List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2))
          (lowerHistoryAppend base r.1, r.2) xs =
      let z := List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2)) r xs
      (lowerHistoryAppend base z.1, z.2) := by
  intro xs
  induction xs with
  | nil => intro r; rfl
  | cons step tail ih =>
      intro r
      simp only [List.foldl_cons]
      rw [rawStep_append]
      simpa using ih (lowerHistoryRawStep r.1 r.2 step.1,
        if step.2 then !r.2 else r.2)

private theorem replay_append (base : LowerPair) (p : LowerHistoryPath) (j : ℕ) :
    (lowerHistoryReplay base p j).1 =
      lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1 ∧
    (lowerHistoryReplay base p j).2 = (lowerHistoryReplay ([],[]) p j).2 := by
  unfold lowerHistoryReplay
  have hi : lowerHistoryRawStep base false p.entry =
      lowerHistoryAppend base (lowerHistoryRawStep ([],[]) false p.entry) := by
    simpa [lowerHistoryAppend] using rawStep_append base ([],[]) false p.entry
  rw [hi]
  have hf := fold_append base (p.steps.take j)
    (lowerHistoryRawStep ([],[]) false p.entry, p.initialWider)
  exact ⟨by simpa using congrArg Prod.fst hf, by simpa using congrArg Prod.snd hf⟩

private theorem decide_add_odd (m n : ℕ) :
    decide ((m+n) % 2 = 1) =
      (decide (m % 2 = 1)).xor (decide (n % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [Nat.add_mod, hm, hn]

private theorem even_of_decide_not_odd (n : ℕ) (h : decide (n % 2 = 1) = false) :
    n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · exact hn
  · simp [hn] at h

private theorem advance_shape (r : LowerPair × Bool) (s : LowerHistoryState)
    (l : LowerLabel) (reflect : Bool)
    (hshape : s.context.parity =
        (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
      s.wider = r.2) :
    let r' := (lowerHistoryRawStep r.1 r.2 l, if reflect then !r.2 else r.2)
    let s' := lowerHistoryAdvance s l reflect
    s'.context.parity =
        (decide (r'.1.1.length % 2 = 1), decide (r'.1.2.length % 2 = 1)) ∧
      s'.wider = r'.2 := by
  rcases r with ⟨words,wide⟩
  rcases s with ⟨C,swide,marked,previous⟩
  simp only at hshape ⊢
  unfold lowerHistoryAdvance
  dsimp only
  rw [hshape.1, hshape.2]
  cases wide <;> cases reflect <;>
    simp [lowerHistoryAdvance, lowerHistoryRawStep, List.length_append,
      decide_add_odd, Bool.xor_comm]

private theorem fold_shape :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool) (s : LowerHistoryState),
      (s.context.parity =
          (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
        s.wider = r.2) →
      let rr := List.foldl (fun z step => (lowerHistoryRawStep z.1 z.2 step.1,
        if step.2 then !z.2 else z.2)) r xs
      let ss := xs.foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s
      ss.context.parity =
          (decide (rr.1.1.length % 2 = 1), decide (rr.1.2.length % 2 = 1)) ∧
        ss.wider = rr.2 := by
  intro xs
  induction xs with
  | nil => intro r s hs; exact hs
  | cons step tail ih =>
      intro r s hs
      simp only [List.foldl_cons]
      rcases step with ⟨l,reflect⟩
      apply ih
      exact advance_shape r s l reflect hs

private theorem state_replay_shape (p : LowerHistoryPath) (j : ℕ) :
    let r := lowerHistoryReplay ([],[]) p j
    let s := lowerHistoryStateAt p j
    s.context.parity =
      (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
    s.wider = r.2 := by
  classical
  unfold lowerHistoryReplay lowerHistoryStateAt
  apply fold_shape
  simp [lowerHistoryInitialState, lowerHistoryRawStep]


private theorem suffixContext_snoc (u v : List ℕ+) (a : ℕ+)
    (h : lowerHistorySuffixContext u v) :
    lowerHistorySuffixContext (u++[a]) (v++[a]) := by
  rcases h with ⟨⟨pre,hpre⟩,h3,h31⟩
  refine ⟨⟨pre,by simpa [List.append_assoc] using congrArg (fun z => z ++ [a]) hpre⟩,?_,?_⟩
  · simp [lowerEnds, ← List.reverse_prefix]
  · have h3r : [3] <+: u.reverse ↔ [3] <+: v.reverse := by
      simpa [lowerEnds, ← List.reverse_prefix] using h3
    simp [lowerEnds, ← List.reverse_prefix, h3r]

private theorem suffixContext_append (u v w : List ℕ+)
    (h : lowerHistorySuffixContext u v) :
    lowerHistorySuffixContext (u++w) (v++w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w a ih =>
      simpa [List.append_assoc] using suffixContext_snoc (u++w) (v++w) a ih

private theorem state_words (p : LowerHistoryPath) (j : ℕ) :
    let source : LowerPair :=
      (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
    (lowerHistoryStateAt p j).context.words =
      lowerHistoryAppend source (lowerHistoryWordsAt p j) := by
  let source : LowerPair :=
    (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  have aux : ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool)
      (s : LowerHistoryState),
      s.context.words = lowerHistoryAppend source r.1 ∧ s.wider = r.2 →
      let rr := xs.foldl (fun z step =>
        (lowerHistoryRawStep z.1 z.2 step.1, if step.2 then !z.2 else z.2)) r
      let ss := xs.foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s
      ss.context.words = lowerHistoryAppend source rr.1 ∧ ss.wider = rr.2 := by
    intro xs
    induction xs with
    | nil => intro r s hs; exact hs
    | cons step tail ih =>
        intro r s hs
        simp only [List.foldl_cons]
        apply ih
        constructor
        · simp only [lowerHistoryAdvance]
          rw [hs.1, hs.2, rawStep_append]
        · simp only [lowerHistoryAdvance]
          rw [hs.2]
          cases r.2 <;> cases step.2 <;> rfl
  unfold lowerHistoryStateAt lowerHistoryWordsAt lowerHistoryReplay
  have ha := aux (p.steps.take j)
    (lowerHistoryRawStep ([],[]) false p.entry,p.initialWider)
    (lowerHistoryInitialState p) (by
      constructor
      · simp only [lowerHistoryInitialState]
        dsimp [source]
        simpa [lowerHistoryAppend] using rawStep_append source ([],[]) false p.entry
      · rfl)
  exact ha.1

private theorem reached_state_context (base : LowerPair) (p : LowerHistoryPath) (j : ℕ)
    (hbase1 : lowerHistorySuffixContext base.1 p.context)
    (hbase2 : lowerHistorySuffixContext base.2
      (if p.catalog = .initial then [3,1,3] else [3,1]))
    (hpar : base.1.length % 2 = base.2.length % 2) :
    let words := lowerHistoryWordsAt p j
    let s := lowerHistoryStateAt p j
    lowerHistoryContextFits
      (lowerHistoryOrient (lowerHistoryAppend base words) s.wider)
      ⟨lowerHistoryOrient s.context.words s.wider,
        if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩ := by
  let words := lowerHistoryWordsAt p j
  let s := lowerHistoryStateAt p j
  let source : LowerPair :=
    (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  have hsw := state_words p j
  have hshape := state_replay_shape p j
  have hpard : decide (base.1.length % 2 = 1) =
      decide (base.2.length % 2 = 1) := by rw [hpar]
  have hctx1 := suffixContext_append base.1 source.1 words.1 hbase1
  have hctx2 := suffixContext_append base.2 source.2 words.2 hbase2
  change lowerHistoryContextFits
    (lowerHistoryOrient (lowerHistoryAppend base words) s.wider)
    ⟨lowerHistoryOrient s.context.words s.wider,
      if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩
  have hsw' : s.context.words = lowerHistoryAppend source words := by
    simpa [s, source, words] using hsw
  have hshape' : s.context.parity =
      (decide (words.1.length % 2 = 1), decide (words.2.length % 2 = 1)) := by
    simpa [s, words, lowerHistoryWordsAt] using hshape.1
  cases hw : s.wider <;>
    simp only [lowerHistoryOrient, hw, Bool.false_eq_true, Bool.true_eq_false,
      if_false, if_true, Prod.fst, Prod.snd, ↓reduceIte]
  · refine ⟨?_,?_,?_⟩
    · simpa [hsw', source, lowerHistoryAppend] using hctx1
    · simpa [hsw', source, lowerHistoryAppend] using hctx2
    · rw [hshape']
      simp only [lowerHistoryAppend, List.length_append, decide_add_odd]
      rw [hpard]
      cases decide (base.2.length % 2 = 1) <;>
        cases decide (words.1.length % 2 = 1) <;>
        cases decide (words.2.length % 2 = 1) <;> decide
  · refine ⟨?_,?_,?_⟩
    · simpa [hsw', source, lowerHistoryAppend] using hctx2
    · simpa [hsw', source, lowerHistoryAppend] using hctx1
    · rw [hshape']
      simp only [lowerHistoryAppend, List.length_append, decide_add_odd]
      rw [hpard]
      cases decide (base.2.length % 2 = 1) <;>
        cases decide (words.1.length % 2 = 1) <;>
        cases decide (words.2.length % 2 = 1) <;> decide

private theorem normalize_wide (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with h
  · exact h
  · exact (lt_of_not_ge h).le

private theorem normalize_idem (p : LowerPair) :
    lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  conv_lhs => rw [lowerNormalize]
  exact if_pos (normalize_wide p)

private theorem normalize_good (p : LowerPair) (h : lowerGood p) :
    lowerGood (lowerNormalize p) := by
  simpa only [lowerGood, lowerChild, normalize_idem] using h

end ReachedGood15

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryGoodEvents Z (other22Paths k) := by
  have hB : B = (Z.1 ++ [2], Z.2 ++ [3]) := by
    rw [h.birth]
    simp [lowerChild, h.normalizedZ]
  have hR : lowerNormalize R = (Z.2 ++ [3], Z.1 ++ [2,2]) := by
    rw [h.normalizedR, hB]
    simp [List.append_assoc]
  have hS : S = (Z.2 ++ [3,1], Z.1 ++ [2,2]) := by
    rw [h.stepS]
    simp [lowerChild, h.normalizedR, hB, List.append_assoc]
  have hbase1 : lowerHistorySuffixContext Z.1 (other22Paths k).context := hc.1
  have hcat : (other22Paths k).catalog ≠ .initial := by fin_cases k <;> decide
  have hbase2 : lowerHistorySuffixContext Z.2
      (if (other22Paths k).catalog = .initial then [3,1,3] else [3,1]) := by
    simpa only [if_neg hcat, other22Context] using hc.2.1
  intro j hj
  let words := lowerHistoryWordsAt (other22Paths k) j
  let s := lowerHistoryStateAt (other22Paths k) j
  let q := lowerHistoryOrient (lowerHistoryAppend Z words) s.wider
  let C : LowerHistoryContext :=
    ⟨lowerHistoryOrient s.context.words s.wider,
      if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩
  have hfit : lowerHistoryContextFits q C :=
    ReachedGood15.reached_state_context Z (other22Paths k) j hbase1 hbase2 h.equalZ
  have hj2 : j ≤ 2 := by
    have he : (other22Paths k).steps.length = 2 := by fin_cases k <;> rfl
    simpa [he] using hj
  have hq : q = B ∨ q = lowerNormalize R ∨ q = S := by
    dsimp only [q, words, s]
    interval_cases j
    · left
      rw [hB]
      fin_cases k <;> rfl
    · right; left
      rw [hR]
      fin_cases k <;> rfl
    · right; right
      rw [hS]
      fin_cases k <;> rfl
  have hnorm : lowerNormalize q = q := by
    rcases hq with he | he | he
    · rw [he]; exact h.normalizedB
    · rw [he]; exact ReachedGood15.normalize_idem R
    · rw [he]; exact h.normalizedS
  have hgood : lowerGood q := by
    rcases hq with he | he | he
    · rw [he]; exact h.goodB
    · rw [he]; exact ReachedGood15.normalize_good R h.goodR
    · rw [he]; exact h.goodS
  obtain ⟨bs,hbs,hholds⟩ := lowerHistory_goodness_semantics q C hfit hnorm hgood
  refine ⟨bs.map (fun b => lowerHistoryPull b words s.wider),?_,?_⟩
  · simp [lowerHistoryNecessary, C, words, s, hbs]
  · intro d hd
    obtain ⟨b,hbm,rfl⟩ := List.mem_map.mp hd
    have hv := GoodFields15.relaxed_fields C bs hbs b hbm
    have hbq : lowerHistoryAtBase q [b] := by
      intro a ha
      have hab : a = b := by simpa using ha
      subst a
      exact hholds b hbm
    have hpulled := (lowerHistory_pull_value Z words b s.wider hv.1 hv.2.1 hv.2.2.1
      hv.2.2.2.1 hv.2.2.2.2).mp (by simpa [q] using hbq)
    exact hpulled _ (by simp)
