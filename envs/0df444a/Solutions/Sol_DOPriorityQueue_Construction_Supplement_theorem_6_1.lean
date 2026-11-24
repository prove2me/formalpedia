-- Prove2me | solution 1 for DOPriorityQueue.Construction.Supplement.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T16:44:39.034178+00:00
-- url     : https://prove2.me/submissions/76d1d6cd-64cc-445f-bf12-2922da192f77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DOPriorityQueue_Construction_Supplement_LowerBound
import Theorems.Thm_DOPriorityQueue_Construction_Supplement_lemma_6_2
import Theorems.Thm_DOPriorityQueue_Construction_Supplement_lemma_6_3
set_option autoImplicit false
namespace DOPriorityQueue.Construction.Supplement

def clientTok {w M : ℕ} (s : OpaqueState w M) : Set ℕ :=
  {b | ∃ i, s.client i = some (RAM.Cell.ball b)}
def servTok {w M : ℕ} (s : OpaqueState w M) : Set ℕ :=
  {b | ∃ a, s.server a = some (RAM.Cell.ball b)}
def allTok {w M : ℕ} (s : OpaqueState w M) : Set ℕ := clientTok s ∪ servTok s

lemma evalSlot_none_tok {w M : ℕ} (c : Fin M → Option (RAM.Cell w ℕ)) (e : SlotExpression w M)
    (b : ℕ) (h : evalSlot c none e = some (RAM.Cell.ball b)) : ∃ i, c i = some (RAM.Cell.ball b) := by
  cases e <;> simp [evalSlot] at h
  case resident i => exact ⟨i, h⟩

lemma evalSlot_some_tok {w M : ℕ} (c : Fin M → Option (RAM.Cell w ℕ)) (e : SlotExpression w M)
    (x b : ℕ) (h : evalSlot c (some x) e = some (RAM.Cell.ball b)) :
    (∃ i, c i = some (RAM.Cell.ball b)) ∨ b = x := by
  cases e <;> simp [evalSlot] at h
  case resident i => exact Or.inl ⟨i, h⟩
  case arriving => exact Or.inr h.symm

lemma enter_extract_tok {w M : ℕ} (Q : OpaqueProgram w M) (s : OpaqueState w M) :
    clientTok (opaqueEnter Q s Operation.extractMin) ⊆ clientTok s ∧
    servTok (opaqueEnter Q s Operation.extractMin) = servTok s := by
  refine ⟨fun b ⟨i, hi⟩ => ?_, rfl⟩
  exact evalSlot_none_tok _ _ _ hi

lemma enter_insert_tok {w M : ℕ} (Q : OpaqueProgram w M) (s : OpaqueState w M) (p x : ℕ) :
    servTok (opaqueEnter Q s (Operation.insert p x)) = servTok s := rfl

def CallSpec {w M : ℕ} (s : OpaqueState w M) (c : OpaqueCall w M) : Prop :=
    allTok c.state ⊆ allTok s ∧
    (∃ F : Finset ℕ, F.card ≤ c.probes.length ∧ servTok c.state ⊆ servTok s ∪ ↑F) ∧
    (∀ p b, c.answer = Answer.extracted (some (p, b)) → b ∈ allTok s)

lemma CallSpec.comb {w M : ℕ} {s s' : OpaqueState w M} {F0 : Finset ℕ} {k : ℕ}
    (hA : allTok s' ⊆ allTok s) (hS : servTok s' ⊆ servTok s ∪ ↑F0) (hF0 : F0.card ≤ k)
    {c' c : OpaqueCall w M} (hst : c.state = c'.state) (hans : c.answer = c'.answer)
    (hpr : c.probes.length = c'.probes.length + k) (sp : CallSpec s' c') : CallSpec s c := by
  obtain ⟨h1, ⟨F, hF, h2⟩, h3⟩ := sp
  refine ⟨?_, ⟨F ∪ F0, ?_, ?_⟩, ?_⟩
  · rw [hst]; exact h1.trans hA
  · calc (F ∪ F0).card ≤ F.card + F0.card := Finset.card_union_le _ _
      _ ≤ c.probes.length := by omega
  · intro b hb
    rw [hst] at hb
    rcases h2 hb with hb | hb
    · rcases hS hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr (by simp [hb])
    · exact Or.inr (by simp [hb])
  · intro p b hb
    rw [hans] at hb
    exact hA (h3 p b hb)

lemma tok_loaded {w M : ℕ} (s : OpaqueState w M) (dest : Fin M) (a : BitVec w) :
    clientTok ({ s with client := Function.update s.client dest (s.server a) } : OpaqueState w M)
      ⊆ allTok s := by
  rintro b ⟨i, hi⟩
  by_cases h : i = dest
  · subst h
    simp only [Function.update_self] at hi
    exact Or.inr ⟨a, hi⟩
  · simp only [Function.update_of_ne h] at hi
    exact Or.inl ⟨i, hi⟩

lemma call_spec {w M : ℕ} (Q : OpaqueProgram w M) : ∀ (fuel : ℕ) (s : OpaqueState w M)
    (coins : List (BitVec w)) (c : OpaqueCall w M), opaqueCall Q fuel s coins = some c →
    CallSpec s c := by
  intro fuel
  induction fuel with
  | zero => intro s coins c h; simp [opaqueCall] at h
  | succ fuel ih =>
    intro s coins c h
    cases coins with
    | nil => simp [opaqueCall] at h
    | cons coin coins =>
      simp only [opaqueCall] at h
      generalize Q.action (fun i => viewCell (s.client i)) coin = a at h
      cases a with
      | «local» u =>
        have sp := ih _ _ _ h
        refine CallSpec.comb (s' := { s with client := fun i => evalSlot s.client none (u i) })
          (F0 := ∅) (k := 0) ?_ ?_ (by simp) rfl rfl (by simp) sp
        · intro b hb
          rcases hb with ⟨i, hi⟩ | hb
          · exact Or.inl ⟨_, (evalSlot_none_tok _ _ _ hi).choose_spec⟩
          · exact Or.inr hb
        · intro b hb; exact Or.inl hb
      | read address destination u =>
        obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.pure_def, Option.some.injEq] at hc
        subst hc
        have sp := ih _ _ _ hr
        refine CallSpec.comb (s' := { s with client := fun i => evalSlot (Function.update s.client destination (s.server address)) none (u i) })
          (F0 := ∅) (k := 1) (c' := r) ?_ ?_ (by simp) rfl rfl (by simp) sp
        · intro b hb
          rcases hb with ⟨i, hi⟩ | hb
          · exact tok_loaded s destination address
              (evalSlot_none_tok _ _ _ hi |>.choose_spec |> fun h => ⟨_, h⟩)
          · exact Or.inr hb
        · intro b hb; exact Or.inl hb
      | write address value u =>
        obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.pure_def, Option.some.injEq] at hc
        subst hc
        have sp := ih _ _ _ hr
        classical
        let F0 : Finset ℕ := match evalSlot s.client none value with
          | some (RAM.Cell.ball b) => {b}
          | _ => ∅
        refine CallSpec.comb (s' := { client := fun i => evalSlot s.client none (u i), server := Function.update s.server address (evalSlot s.client none value) })
          (F0 := F0) (k := 1) (c' := r) ?_ ?_ ?_ rfl rfl (by simp) sp
        · intro b hb
          rcases hb with ⟨i, hi⟩ | ⟨a, ha⟩
          · exact Or.inl ⟨_, (evalSlot_none_tok _ _ _ hi).choose_spec⟩
          · by_cases h : a = address
            · subst h
              simp only [Function.update_self] at ha
              obtain ⟨i, hi⟩ := evalSlot_none_tok _ _ _ ha
              exact Or.inl ⟨i, hi⟩
            · simp only [Function.update_of_ne h] at ha
              exact Or.inr ⟨a, ha⟩
        · rintro b ⟨a, ha⟩
          by_cases h : a = address
          · subst h
            simp only [Function.update_self] at ha
            right
            simp [F0, ha]
          · simp only [Function.update_of_ne h] at ha
            exact Or.inl ⟨a, ha⟩
        · show F0.card ≤ 1
          simp only [F0]; split <;> simp
      | inserted =>
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        refine ⟨fun b hb => hb, ⟨∅, by simp, fun b hb => Or.inl hb⟩, ?_⟩
        intro p b hb; simp at hb
      | empty =>
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        refine ⟨fun b hb => hb, ⟨∅, by simp, fun b hb => Or.inl hb⟩, ?_⟩
        intro p b hb; simp at hb
      | output priority source =>
        simp only at h
        split at h
        · rename_i b hb
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          refine ⟨fun b hb => hb, ⟨∅, by simp, fun b hb => Or.inl hb⟩, ?_⟩
          intro p b' hb'
          simp only [Answer.extracted.injEq, Option.some.injEq, Prod.mk.injEq] at hb'
          obtain ⟨-, rfl⟩ := hb'
          exact Or.inl ⟨source, hb⟩
        · simp at h

lemma run_cons {w M : ℕ} (Q : OpaqueProgram w M) (fuel : ℕ) (s : OpaqueState w M)
    (coins : List (BitVec w)) (op : Operation ℕ) (h : List (Operation ℕ)) (r : OpaqueRun w M)
    (hr : opaqueRun Q fuel s coins (op :: h) = some r) :
    ∃ c rest, opaqueCall Q fuel (opaqueEnter Q s op) coins = some c ∧
      opaqueRun Q fuel c.state c.remainingCoins h = some rest ∧
      r.state = rest.state ∧ r.remainingCoins = rest.remainingCoins ∧
      r.traces = c.probes :: rest.traces ∧ r.answers = c.answer :: rest.answers := by
  simp only [opaqueRun] at hr
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨rest, hrest, hr⟩ := Option.bind_eq_some_iff.mp hr
  simp only [Option.pure_def, Option.some.injEq] at hr
  subst hr
  exact ⟨c, rest, hc, hrest, rfl, rfl, rfl, rfl⟩

lemma run_len {w M : ℕ} (Q : OpaqueProgram w M) (fuel : ℕ) :
    ∀ (ops : List (Operation ℕ)) (s : OpaqueState w M) (coins : List (BitVec w)) (r : OpaqueRun w M),
    opaqueRun Q fuel s coins ops = some r → r.answers.length = ops.length ∧ r.traces.length = ops.length := by
  intro ops
  induction ops with
  | nil => intro s coins r h; simp [opaqueRun] at h; subst h; simp
  | cons op ops ih =>
    intro s coins r h
    obtain ⟨c, rest, hc, hrest, -, -, ht, ha⟩ := run_cons Q fuel s coins op ops r h
    have := ih _ _ _ hrest
    rw [ht, ha]; simp [this]

lemma run_serv {w M : ℕ} (Q : OpaqueProgram w M) (fuel : ℕ) :
    ∀ (ops : List (Operation ℕ)) (s : OpaqueState w M) (coins : List (BitVec w)) (r : OpaqueRun w M),
    opaqueRun Q fuel s coins ops = some r →
    ∃ F : Finset ℕ, F.card ≤ probeCount r.traces ∧ servTok r.state ⊆ servTok s ∪ ↑F := by
  intro ops
  induction ops with
  | nil => intro s coins r h; simp [opaqueRun] at h; subst h; exact ⟨∅, by simp, fun b hb => Or.inl hb⟩
  | cons op ops ih =>
    intro s coins r h
    obtain ⟨c, rest, hc, hrest, hst, -, ht, -⟩ := run_cons Q fuel s coins op ops r h
    obtain ⟨-, ⟨F1, hF1, hs1⟩, -⟩ := call_spec Q _ _ _ _ hc
    obtain ⟨F2, hF2, hs2⟩ := ih _ _ _ hrest
    refine ⟨F1 ∪ F2, ?_, ?_⟩
    · have : probeCount r.traces = c.probes.length + probeCount rest.traces := by
        simp [probeCount, ht]
      have := Finset.card_union_le F1 F2
      omega
    · intro b hb
      rw [hst] at hb
      rcases hs2 hb with hb | hb
      · rcases hs1 hb with hb | hb
        · have : servTok (opaqueEnter Q s op) = servTok s := by
            cases op <;> rfl
          rw [this] at hb
          exact Or.inl hb
        · exact Or.inr (by simp [hb])
      · exact Or.inr (by simp [hb])

lemma run_extract {w M : ℕ} (Q : OpaqueProgram w M) (fuel : ℕ) :
    ∀ (ops : List (Operation ℕ)) (s : OpaqueState w M) (coins : List (BitVec w)) (r : OpaqueRun w M),
    (∀ op ∈ ops, op = Operation.extractMin) →
    opaqueRun Q fuel s coins ops = some r →
    allTok r.state ⊆ allTok s ∧
      ∀ p b, Answer.extracted (some (p, b)) ∈ r.answers → b ∈ allTok s := by
  intro ops
  induction ops with
  | nil => intro s coins r _ h; simp [opaqueRun] at h; subst h; exact ⟨fun b hb => hb, by simp⟩
  | cons op ops ih =>
    intro s coins r hops h
    have hop : op = Operation.extractMin := hops op (by simp)
    subst hop
    obtain ⟨c, rest, hc, hrest, hst, -, -, ha⟩ := run_cons Q fuel s coins _ ops r h
    obtain ⟨h1, -, h3⟩ := call_spec Q _ _ _ _ hc
    obtain ⟨hA, hB⟩ := ih _ _ _ (fun o ho => hops o (by simp [ho])) hrest
    obtain ⟨e1, e2⟩ := enter_extract_tok Q s
    have hen : allTok (opaqueEnter Q s Operation.extractMin) ⊆ allTok s := by
      rintro b (hb | hb)
      · exact Or.inl (e1 hb)
      · exact Or.inr (by rw [e2] at hb; exact hb)
    refine ⟨?_, ?_⟩
    · rw [hst]; exact hA.trans (h1.trans hen)
    · intro p b hb
      rw [ha] at hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hen (h3 p b hb.symm)
      · exact h1.trans hen (hB p b hb)

lemma run_append {w M : ℕ} (Q : OpaqueProgram w M) (fuel : ℕ) :
    ∀ (h1 h2 : List (Operation ℕ)) (s : OpaqueState w M) (coins : List (BitVec w)) (r : OpaqueRun w M),
    opaqueRun Q fuel s coins (h1 ++ h2) = some r →
    ∃ r1 r2, opaqueRun Q fuel s coins h1 = some r1 ∧
      opaqueRun Q fuel r1.state r1.remainingCoins h2 = some r2 ∧
      r.traces = r1.traces ++ r2.traces ∧ r.answers = r1.answers ++ r2.answers := by
  intro h1
  induction h1 with
  | nil =>
    intro h2 s coins r h
    exact ⟨⟨s, coins, [], []⟩, r, by simp [opaqueRun], by simpa using h, by simp, by simp⟩
  | cons op h1 ih =>
    intro h2 s coins r h
    obtain ⟨c, rest, hc, hrest, hst, -, ht, ha⟩ := run_cons Q fuel s coins op (h1 ++ h2) r h
    obtain ⟨r1, r2, e1, e2, e3, e4⟩ := ih h2 _ _ _ hrest
    refine ⟨⟨r1.state, r1.remainingCoins, c.probes :: r1.traces, c.answer :: r1.answers⟩, r2, ?_, e2, ?_, ?_⟩
    · simp only [opaqueRun]
      rw [hc]; simp only [bind, Option.bind_some]
      rw [e1]; simp
    · rw [ht, e3]; simp
    · rw [ha, e4]; simp

def qEnd {Ball : Type} : ℕ → List (Record Ball) → List (Operation Ball) → List (Record Ball)
  | _, q, [] => q
  | i, q, op :: r => qEnd (i + 1) (queueStep i q op).1 r

lemma queueRun_append {Ball : Type} (h1 h2 : List (Operation Ball)) :
    ∀ (i : ℕ) (q : List (Record Ball)),
    queueRun i q (h1 ++ h2) = queueRun i q h1 ++ queueRun (i + h1.length) (qEnd i q h1) h2 := by
  induction h1 with
  | nil => intro i q; simp [queueRun, qEnd]
  | cons op h1 ih =>
    intro i q
    simp only [List.cons_append, queueRun, qEnd, ih, List.length_cons, List.cons_append]
    rw [show i + 1 + h1.length = i + (h1.length + 1) by omega]

lemma queueRun_length {Ball : Type} (h : List (Operation Ball)) :
    ∀ (i : ℕ) (q : List (Record Ball)), (queueRun i q h).length = h.length := by
  induction h with
  | nil => intro i q; simp [queueRun]
  | cons op h ih => intro i q; simp [queueRun, ih]

lemma qEnd_inserts (l : List (ℕ × ℕ)) :
    ∀ (i : ℕ) (q : List (Record ℕ)),
    ((qEnd i q (l.map fun pb => Operation.insert pb.1 pb.2)).map Record.payload).Perm
      (q.map Record.payload ++ l.map Prod.snd) ∧
    (qEnd i q (l.map fun pb => Operation.insert pb.1 pb.2)).length = q.length + l.length := by
  induction l with
  | nil => intro i q; simp [qEnd]
  | cons pb l ih =>
    intro i q
    simp only [List.map_cons, qEnd, queueStep]
    obtain ⟨h1, h2⟩ := ih (i + 1) (List.orderedInsert keyLE ⟨pb.1, i, pb.2⟩ q)
    refine ⟨?_, ?_⟩
    · refine h1.trans ?_
      have hp := (List.perm_orderedInsert keyLE (⟨pb.1, i, pb.2⟩ : Record ℕ) q).map Record.payload
      simp only [List.map_cons] at hp
      have := (hp.append_right (l.map Prod.snd))
      refine this.trans ?_
      simp only [List.cons_append, List.map_cons]
      exact List.perm_middle.symm
    · rw [h2, (List.perm_orderedInsert keyLE (⟨pb.1, i, pb.2⟩ : Record ℕ) q).length_eq]; simp; omega

lemma queueRun_extracts {Ball : Type} (q : List (Record Ball)) :
    ∀ i, queueRun i q (List.replicate q.length Operation.extractMin) =
      q.map fun r => Answer.extracted (some (r.priority, r.payload)) := by
  induction q with
  | nil => intro i; simp [queueRun]
  | cons r q ih => intro i; simp [List.replicate_succ, queueRun, queueStep, ih]

lemma probeCount_append {w : ℕ} (a b : RAM.Trace w) : probeCount (a ++ b) = probeCount a + probeCount b := by
  simp [probeCount]

lemma pathwise_bound {w M : ℕ} (Q : OpaqueProgram w M) (n : ℕ) (X : Fin n → Fin n)
    (fuel : ℕ) (coins : List (BitVec w)) (r : OpaqueRun w M)
    (hrun : opaqueRun Q fuel (opaqueInitial Q) coins (experimentHistory (fun i : Fin n => i.val) X) = some r)
    (hans : r.answers = exactAnswers (experimentHistory (fun i : Fin n => i.val) X)) :
    n - M ≤ probeCount r.traces := by
  classical
  set l : List (ℕ × ℕ) := List.ofFn (fun i : Fin n => ((X i).val + 1, i.val)) with hl
  have hins : (List.ofFn fun i : Fin n => Operation.insert ((X i).val + 1) i.val) =
      l.map fun pb => Operation.insert pb.1 pb.2 := by
    simp [hl, List.map_ofFn, Function.comp_def]
  have hllen : l.length = n := by simp [hl]
  unfold experimentHistory at hrun hans
  rw [hins] at hrun hans
  obtain ⟨r1, r2, e1, e2, e3, e4⟩ := run_append Q fuel _ _ _ _ _ hrun
  set insOps := l.map fun pb => Operation.insert pb.1 pb.2 with hio
  have hlen_ins : insOps.length = n := by simp [hio, hllen]
  unfold exactAnswers at hans
  rw [queueRun_append, hlen_ins] at hans
  obtain ⟨hq1, hq2⟩ := qEnd_inserts l 1 []
  rw [← hio] at hq1 hq2
  have hlq : (qEnd 1 [] insOps).length = n := by simp [hq2, hllen]
  rw [← hlq, queueRun_extracts, e4] at hans
  have hr1len := (run_len Q fuel _ _ _ _ e1).1
  obtain ⟨-, h2⟩ := List.append_inj hans (by rw [hr1len, queueRun_length])
  obtain ⟨-, hB⟩ := run_extract Q fuel _ _ _ _ (fun op hop => (List.mem_replicate.mp hop).2) e2
  have htok : ∀ i < n, i ∈ allTok r1.state := by
    intro i hi
    have hi' : i ∈ List.map Prod.snd l := by
      refine List.mem_map.mpr ⟨((X ⟨i, hi⟩).val + 1, i), ?_, rfl⟩
      rw [hl]; exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩
    have hi'' := hq1.mem_iff.mpr (by simpa using hi')
    obtain ⟨rec, hrec, hpay⟩ := List.mem_map.mp hi''
    exact hB rec.priority i (by rw [h2]; exact List.mem_map.mpr ⟨rec, hrec, by simp [hpay]⟩)
  obtain ⟨F, hF, hs⟩ := run_serv Q fuel _ _ _ _ e1
  have hinit : servTok (opaqueInitial Q) = ∅ := by
    ext b
    simp only [servTok, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, ha⟩
    cases h : Q.initialServer a <;> simp [opaqueInitial, h] at ha
  rw [hinit] at hs
  let f : Fin M → ℕ := fun i => match r1.state.client i with
    | some (RAM.Cell.ball b) => b
    | _ => 0
  have hsub : Finset.range n ⊆ Finset.univ.image f ∪ F := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases htok i hi with ⟨j, hj⟩ | hb
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by simp [f, hj]⟩
    · apply Finset.mem_union_right
      simpa using hs hb
  have hc := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le (Finset.univ.image f) F
  have hc3 : (Finset.univ.image f).card ≤ M := by
    calc _ ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_image_le
      _ = M := by simp
  have hp : probeCount r.traces = probeCount r1.traces + probeCount r2.traces := by
    rw [e3, probeCount_append]
  simp only [Finset.card_range] at hc
  omega

lemma mixed_eq_avg {n w : ℕ} (hn : 0 < n) (K : TraceKernel w) (b : Fin n → ℕ) :
    mixedProbes K b = ∑ X : Fin n → Fin n,
      (Fintype.card (Fin n → Fin n) : ENNReal)⁻¹ * expectedProbes K (experimentHistory b X) := by
  classical
  have : Nonempty (Fin n → Fin n) := ⟨id⟩
  unfold mixedProbes expectedProbes experimentLaw
  have key : ∀ v : RAM.Trace w, ((PMF.uniformOfFintype (Fin n → Fin n)).bind fun X =>
      (K (experimentHistory b X)).map fun v => (X, v)).map Prod.snd v
      = ∑ X : Fin n → Fin n, (Fintype.card (Fin n → Fin n) : ENNReal)⁻¹ * K (experimentHistory b X) v := by
    intro v
    rw [PMF.map_bind, PMF.bind_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [PMF.uniformOfFintype_apply, PMF.map_comp]
    simp only [Function.comp_def, PMF.map_apply]
    congr 1
    rw [tsum_eq_single v (fun a ha => by simp [Ne.symm ha])]
    simp
  simp_rw [key, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  ring


lemma valid_hist (n T U : ℕ) (hT : 2 * n ≤ T) (hU : n ≤ U) (X : Fin n → Fin n) :
    validHistory T U (experimentHistory (fun i : Fin n => i.val) X) := by
  refine ⟨?_, ?_⟩
  · simp [experimentHistory]; omega
  · intro op hop
    simp only [experimentHistory, List.mem_append, List.mem_ofFn, Set.mem_range,
      List.mem_replicate] at hop
    rcases hop with ⟨i, rfl⟩ | ⟨-, rfl⟩
    · have := (X i).isLt; have := i.isLt
      simp only; omega
    · trivial

lemma pw_arith (A c : ℝ) (hc : 0 < c) (m : ENNReal) (N : ℕ)
    (h : ENNReal.ofReal A ≤ (m + (N : ENNReal)) * ENNReal.ofReal c) :
    ENNReal.ofReal (A / c - N) ≤ m := by
  by_cases hm : m = ⊤
  · simp [hm]
  have hm' : m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal hm).symm
  rw [hm'] at h ⊢
  have e : (ENNReal.ofReal m.toReal + (N : ENNReal)) * ENNReal.ofReal c
      = ENNReal.ofReal ((m.toReal + N) * c) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  apply ENNReal.ofReal_le_ofReal
  have : A / c ≤ m.toReal + N := by rw [div_le_iff₀ hc]; exact h
  linarith

theorem pointwise : PointwiseLowerBound := by
  intro n T U M w Q ε δ hn hT hM hMn hU hcorr hdo
  refine ⟨?_, ?_⟩
  · have h62 := lemma_6_2 n T U w (opaqueKernel Q) (fun i : Fin n => i.val) ε δ hn hT hU
      (fun a b h => Fin.ext h) hdo
    have h63 := (lemma_6_3 n T U M w Q (fun i : Fin n => i.val) hn hT hU hM
      (fun a b h => Fin.ext h) hcorr).2
    have hc : 0 < Real.logb 2 (2 * (M + 2 : ℕ)) := by
      apply Real.logb_pos (by norm_num)
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      push_cast; linarith
    have := pw_arith _ _ hc _ _ (h62.trans h63)
    simpa using this
  · intro X fuel coins r hrun
    exact pathwise_bound Q n X fuel coins r hrun
      ((hcorr _ (valid_hist n T U hT hU X)).2.1 fuel coins r hrun)

lemma completed_run {w M : ℕ} (Q : OpaqueProgram w M) (h : List (Operation ℕ)) (coins : List (BitVec w))
    (r : OpaqueRun w M) (hr : opaqueCompleted Q h coins = some r) :
    ∃ fuel, opaqueRun Q fuel (opaqueInitial Q) coins h = some r := by
  classical
  unfold opaqueCompleted at hr
  simp only at hr
  split_ifs at hr with ht
  exact ⟨_, hr⟩

lemma expected_ge {w M n T U : ℕ} (Q : OpaqueProgram w M) (hT : 2 * n ≤ T) (hU : n ≤ U)
    (hcorr : opaqueCorrect Q T U) (X : Fin n → Fin n) :
    ((n - M : ℕ) : ENNReal) ≤ expectedProbes (opaqueKernel Q) (experimentHistory (fun i : Fin n => i.val) X) := by
  classical
  set h := experimentHistory (fun i : Fin n => i.val) X with hh
  have hv := hcorr h (valid_hist n T U hT hU X)
  have hH := hv.2.2
  have hK : ∀ v, opaqueKernel Q h v = opaqueMass Q h v := by
    intro v; simp [opaqueKernel, hH]; rfl
  unfold expectedProbes
  calc ((n - M : ℕ) : ENNReal) = (∑' v, opaqueMass Q h v) * ((n - M : ℕ) : ENNReal) := by
        rw [hH.tsum_eq, one_mul]
    _ = ∑' v, opaqueMass Q h v * ((n - M : ℕ) : ENNReal) := ENNReal.tsum_mul_right.symm
    _ ≤ _ := by
      refine ENNReal.tsum_le_tsum fun v => ?_
      rw [hK]
      by_cases h0 : opaqueMass Q h v = 0
      · simp [h0]
      · gcongr
        have : ∃ coins, (match opaqueCompleted Q h coins with
            | none => 0
            | some r => if r.traces = v then RAM.coinPrefixMass w coins else 0) ≠ 0 := by
          by_contra hne
          push Not at hne
          apply h0
          unfold opaqueMass
          exact ENNReal.tsum_eq_zero.mpr hne
        obtain ⟨coins, hc⟩ := this
        cases hcomp : opaqueCompleted Q h coins with
        | none => simp [hcomp] at hc
        | some r =>
          simp only [hcomp] at hc
          have htr : r.traces = v := by
            by_contra hne; simp [hne] at hc
          obtain ⟨fuel, hfuel⟩ := completed_run Q h coins r hcomp
          rw [← htr]
          exact pathwise_bound Q n X fuel coins r hfuel ((hv.2.1) fuel coins r hfuel)

lemma exists_X {n w : ℕ} (hn : 0 < n) (K : TraceKernel w) (b : Fin n → ℕ) :
    ∃ X : Fin n → Fin n, mixedProbes K b ≤ expectedProbes K (experimentHistory b X) := by
  classical
  by_contra hcon
  push Not at hcon
  have hcard : (Fintype.card (Fin n → Fin n) : ENNReal) ≠ 0 := by
    have : 0 < Fintype.card (Fin n → Fin n) := Fintype.card_pos_iff.mpr ⟨id⟩
    exact_mod_cast this.ne'
  have hcardt : (Fintype.card (Fin n → Fin n) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  haveI : Nonempty (Fin n → Fin n) := ⟨id⟩
  have : mixedProbes K b < mixedProbes K b := by
    calc mixedProbes K b = ∑ X : Fin n → Fin n,
        (Fintype.card (Fin n → Fin n) : ENNReal)⁻¹ * expectedProbes K (experimentHistory b X) :=
          mixed_eq_avg hn K b
      _ < ∑ X : Fin n → Fin n, (Fintype.card (Fin n → Fin n) : ENNReal)⁻¹ * mixedProbes K b := by
          apply ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro X _
          exact (ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.mpr hcardt)
            (ENNReal.inv_ne_top.mpr hcard)).mpr (hcon X)
      _ = mixedProbes K b := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
            ENNReal.mul_inv_cancel hcard hcardt, one_mul]
  exact lt_irrefl _ this

lemma gamma_le (n : ℕ) (ε δ E' : ℝ) (hε : 0 ≤ ε) (hεE : ε ≤ E') (hE : 0 ≤ E') (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 16) (hL : 16 * (E' + 1) ≤ Real.logb 2 n) :
    gamma n ε δ ≤ Real.logb 2 n / 4 := by
  unfold gamma
  set L := Real.logb 2 n with hLdef
  have l2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have e1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have e2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    calc (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) e1
      _ = 1 / 2 := by norm_num
  have hL16 : 16 ≤ L := by linarith
  have t1 : (ε + 1) / Real.log 2 ≤ 2 * (E' + 1) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have t2 : δ * L / (1 - Real.exp (-1)) ≤ L / 8 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

lemma case2_ineq (n L ℓ γ : ℝ) (hn : 0 ≤ n) (hℓ : 1 ≤ ℓ) (hL : 16 ≤ L) (hγ : γ ≤ L / 4)
    (hℓL : ℓ < L / 16) :
    n * L / (32 * ℓ) ≤ n * (L - 2 - γ) / (1 + ℓ) - 2 * n := by
  have h1 : L / (32 * ℓ) ≤ L / 32 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have h2 : L / (32 * ℓ) + 2 ≤ (L - 2 - γ) / (1 + ℓ) := by
    rw [le_div_iff₀ (by linarith)]
    have hq : L / (32 * ℓ) * ℓ = L / 32 := by field_simp
    nlinarith
  have : n * L / (32 * ℓ) = n * (L / (32 * ℓ)) := by ring
  have h3 : n * (L - 2 - γ) / (1 + ℓ) = n * ((L - 2 - γ) / (1 + ℓ)) := by ring
  rw [this, h3]
  nlinarith

theorem lowerBound : LowerBoundTarget := by
  intro ε δ ⟨E, hE⟩ hδ
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ E ∧ δ n < 1 / 16 ∧
      2 ^ ⌈16 * (max E 0 + 1)⌉₊ ≤ n ∧ 2 ≤ n :=
    hE.and ((hδ.eventually (gt_mem_nhds (by norm_num))).and
      ((Filter.eventually_ge_atTop _).and (Filter.eventually_ge_atTop 2)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn T U M w Q hT hM hMn hU hcorr hdo
  obtain ⟨h1, h2, h3, hn2⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hε0 := hdo.1
  have hδ0 := hdo.2.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set E' := max E 0 with hE'
  have hE0 : 0 ≤ E' := le_max_right _ _
  have hLk : 16 * (E' + 1) ≤ Real.logb 2 n := by
    have h4 : ((⌈16 * (E' + 1)⌉₊ : ℕ) : ℝ) ≤ Real.logb 2 n := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_natCast]
      exact_mod_cast h3
    exact (Nat.le_ceil _).trans h4
  have hγ := gamma_le n (ε n) (δ n) E' hε0 (h1.trans (le_max_left _ _)) hE0 hδ0 h2.le hLk
  have hL16 : 16 ≤ Real.logb 2 n := by linarith
  obtain ⟨X, hX⟩ := exists_X (by omega : 0 < n) (opaqueKernel Q) (fun i : Fin n => i.val)
  refine ⟨X, ?_⟩
  have hpw := (pointwise n T U M w Q (ε n) (δ n) hn2 hT hM hMn hU hcorr hdo).1
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hℓ1 : 1 ≤ Real.logb 2 (M + 2 : ℕ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by push_cast; linarith)]
    push_cast; simp
  by_cases hcase : Real.logb 2 n / 16 ≤ Real.logb 2 (M + 2 : ℕ)
  · refine le_trans ?_ (expected_ge Q hT hU hcorr X)
    have : (n : ℝ) * Real.logb 2 n / (32 * Real.logb 2 (M + 2 : ℕ)) ≤ ((n - M : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), div_le_iff₀ (by linarith)]
      have : (2 * M : ℝ) ≤ n := by exact_mod_cast hMn
      nlinarith [mul_le_mul_of_nonneg_left hcase hnpos.le]
    calc _ ≤ ENNReal.ofReal ((n - M : ℕ) : ℝ) := ENNReal.ofReal_le_ofReal this
      _ = _ := ENNReal.ofReal_natCast _
  · push Not at hcase
    have hc : Real.logb 2 (2 * ((M + 2 : ℕ) : ℝ)) = 1 + Real.logb 2 (M + 2 : ℕ) := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
    rw [hc] at hpw
    refine le_trans ?_ (hpw.trans hX)
    apply ENNReal.ofReal_le_ofReal
    exact case2_ineq n _ _ _ hnpos.le hℓ1 hL16 hγ hcase

end DOPriorityQueue.Construction.Supplement

theorem solution : DOPriorityQueue.Construction.Supplement.LowerBoundTarget ∧
    DOPriorityQueue.Construction.Supplement.PointwiseLowerBound :=
  ⟨DOPriorityQueue.Construction.Supplement.lowerBound,
    DOPriorityQueue.Construction.Supplement.pointwise⟩
