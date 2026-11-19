-- Prove2me | solution 1 for FCP.BusyBeaver.busy_beaver_exceeds_computable
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-18T10:37:32.235285+00:00
-- url     : https://prove2.me/submissions/1c323d44-1fe8-4ce3-8b7c-1e4870919d44

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace FCP.BusyBeaver.Rado

open FCP.BusyBeaver

/-! ### Machines over an arbitrary state type -/

structure GTM (Q : Type) where
  trans : Q → Bool → Bool × Bool × Option Q

structure GCfg (Q : Type) where
  state : Q
  head : ℤ
  tape : ℤ → Bool

variable {Q : Type}

def gstep (M : GTM Q) (c : GCfg Q) : Option (GCfg Q) :=
  match M.trans c.state (c.tape c.head) with
  | (_, _, none) => none
  | (w, d, some s) =>
      some ⟨s, if d then c.head + 1 else c.head - 1, Function.update c.tape c.head w⟩

def grun (M : GTM Q) (c : GCfg Q) : ℕ → Option (GCfg Q)
  | 0 => some c
  | t + 1 => (grun M c t).bind (gstep M)

theorem grun_add (M : GTM Q) (c : GCfg Q) (a b : ℕ) :
    grun M c (a + b) = (grun M c a).bind (fun c' => grun M c' b) := by
  induction b with
  | zero => simp [grun]
  | succ b ih => rw [← Nat.add_assoc, grun, ih, Option.bind_assoc]; rfl

theorem grun_one (M : GTM Q) (c : GCfg Q) : grun M c 1 = gstep M c := by
  simp [grun]

/-- Each step changes at most one cell, so a run from the blank tape has at most `t` true cells
after `t` steps. -/
theorem card_true_le (M : GTM Q) (q0 : Q) :
    ∀ (t : ℕ) (c : GCfg Q), grun M ⟨q0, 0, fun _ => false⟩ t = some c →
      ∀ P : Finset ℤ, (P.filter (fun i => c.tape i = true)).card ≤ t := by
  intro t
  induction t with
  | zero =>
    intro c hc P
    simp only [grun, Option.some.injEq] at hc
    subst hc
    simp
  | succ t ih =>
    intro c hc P
    simp only [grun] at hc
    obtain ⟨c', hc', hs⟩ := Option.bind_eq_some_iff.1 hc
    have h1 := ih c' hc' P
    unfold gstep at hs
    split at hs
    · cases hs
    · rename_i w d s _
      simp only [Option.some.injEq] at hs
      subst hs
      have hsub : P.filter (fun i => Function.update c'.tape c'.head w i = true) ⊆
          insert c'.head (P.filter (fun i => c'.tape i = true)) := by
        intro i hi
        simp only [Finset.mem_filter] at hi
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : i = c'.head
        · exact Or.inl h
        · rw [Function.update_of_ne h] at hi
          exact Or.inr hi
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_insert_le _ _
        _ ≤ t + 1 := by omega

/-! ### From arbitrary state types to `TM n` -/

section Reindex

variable [Nonempty Q] {n : ℕ}

open Classical in
noncomputable def reindex (ι : Q → Fin n) (M : GTM Q) : TM n :=
  ⟨fun i b => if i ∈ Set.range ι then
      let r := M.trans (Function.invFun ι i) b
      (r.1, r.2.1, r.2.2.map ι)
    else (b, true, none)⟩

def cmap (ι : Q → Fin n) (c : GCfg Q) : Config n := ⟨ι c.state, c.head, c.tape⟩

theorem step_reindex {ι : Q → Fin n} (hι : Function.Injective ι) (M : GTM Q) (c : GCfg Q) :
    step (reindex ι M) (cmap ι c) = (gstep M c).map (cmap ι) := by
  have hinv : Function.invFun ι (ι c.state) = c.state := Function.leftInverse_invFun hι _
  unfold step gstep
  simp only [reindex, cmap, Set.mem_range_self, if_true, hinv]
  rcases M.trans c.state (c.tape c.head) with ⟨w, d, _ | s⟩ <;> rfl

theorem run_reindex {ι : Q → Fin n} (hι : Function.Injective ι) (M : GTM Q) (c : GCfg Q) :
    ∀ t, run (reindex ι M) (cmap ι c) t = (grun M c t).map (cmap ι)
  | 0 => rfl
  | t + 1 => by
    simp only [run, grun, run_reindex hι M c t]
    cases grun M c t with
    | none => rfl
    | some c' => simp [step_reindex hι]

end Reindex

/-! ### Bounding `BB` from below -/

instance (n : ℕ) : Finite (TM n) :=
  Finite.of_injective (fun M : TM n => M.trans) (by
    intro a b h; cases a; cases b; simp_all)

theorem haltsIn_unique {n : ℕ} {M : TM n} {c : Config n} {t₁ t₂ : ℕ}
    (h₁ : HaltsIn M c t₁) (h₂ : HaltsIn M c t₂) : t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact absurd h₁.1 (h₂.2 _ h)
  · exact h
  · exact absurd h₂.1 (h₁.2 _ h)

theorem bddAbove_halts (n : ℕ) :
    BddAbove {t : ℕ | ∃ (M : TM n) (h : 0 < n), HaltsIn M (init h) t} := by
  apply Set.Finite.bddAbove
  refine Set.Finite.subset (Set.finite_iUnion (fun M : TM n =>
    (show Set.Subsingleton {t : ℕ | ∃ h : 0 < n, HaltsIn M (init h) t} from ?_).finite)) ?_
  · rintro t₁ ⟨h, ht₁⟩ t₂ ⟨_, ht₂⟩
    exact haltsIn_unique ht₁ ht₂
  · rintro t ⟨M, h, ht⟩
    exact Set.mem_iUnion.2 ⟨M, h, ht⟩

theorem le_BB {n t : ℕ} (M : TM n) (h : 0 < n) (ht : HaltsIn M (init h) t) : t ≤ BB n :=
  le_csSup (bddAbove_halts n) ⟨M, h, ht⟩

theorem gen_le_BB [Fintype Q] (M : GTM Q) (q0 : Q) (t : ℕ) (c : GCfg Q)
    (h₁ : grun M ⟨q0, 0, fun _ => false⟩ t = some c) (h₂ : gstep M c = none)
    (N : ℕ) (hN : Fintype.card Q ≤ N) : t + 1 ≤ BB N := by
  have : Nonempty Q := ⟨q0⟩
  have hpos : 0 < N := lt_of_lt_of_le Fintype.card_pos hN
  let e := Fintype.equivFin Q
  let ι : Q → Fin N := fun q => Equiv.swap (Fin.castLE hN (e q0)) ⟨0, hpos⟩ (Fin.castLE hN (e q))
  have hι : Function.Injective ι := fun a b hab =>
    e.injective (Fin.castLE_injective hN ((Equiv.swap _ _).injective hab))
  have hι0 : ι q0 = ⟨0, hpos⟩ := Equiv.swap_apply_left _ _
  have hinit : cmap ι ⟨q0, 0, fun _ => false⟩ = init hpos := by
    simp only [cmap, hι0, init]
  refine le_BB (reindex ι M) hpos ⟨?_, ?_⟩
  · rw [← hinit, run_reindex hι, grun, h₁]
    simp [h₂]
  · intro s hs hnone
    rw [← hinit, run_reindex hι, Option.map_eq_none_iff] at hnone
    have := grun_add M ⟨q0, 0, fun _ => false⟩ s (t - s)
    rw [Nat.add_sub_cancel' (by omega), h₁, hnone] at this
    cases this


/-! ### Simulating a `TM0` machine over `Bool`, after writing its input -/

section TM0Sim

open Turing

variable {Λ : Type} [Inhabited Λ] (M : TM0.Machine Bool Λ) (S : Finset Λ) (h0 : default ∈ S)
  (w : List Bool)

open Classical in
noncomputable def lab (q : Λ) : {q // q ∈ S} := if h : q ∈ S then ⟨q, h⟩ else ⟨default, h0⟩

theorem lab_of_mem {q : Λ} (h : q ∈ S) : lab S h0 q = ⟨q, h⟩ := by
  simp [lab, h]

def dirB : Dir → Bool
  | .left => false
  | .right => true

abbrev SQ := Fin (w.length + 1) ⊕ ({q // q ∈ S} × Bool)

noncomputable def simTM : GTM (SQ S w) :=
  ⟨fun q b => match q with
    | .inl j =>
      if h : j.val < w.length then
        (w.getD (w.length - 1 - j.val) false, false, some (.inl ⟨j.val + 1, by omega⟩))
      else (b, true, some (.inr (lab S h0 default, false)))
    | .inr (q, false) =>
      match M q.1 b with
      | none => (b, true, none)
      | some (q', .move d) => (b, dirB d, some (.inr (lab S h0 q', false)))
      | some (q', .write a) => (a, true, some (.inr (lab S h0 q', true)))
    | .inr (q, true) => (b, false, some (.inr (q, false)))⟩

def SimRel (c : TM0.Cfg Bool Λ) (g : GCfg (SQ S w)) : Prop :=
  ∃ h : c.q ∈ S, g.state = .inr (⟨c.q, h⟩, false) ∧ ∀ i : ℤ, g.tape (g.head + i) = c.Tape.nth i

variable {M S h0 w}

theorem sim_halt {c : TM0.Cfg Bool Λ} {g : GCfg (SQ S w)} (hr : SimRel S w c g)
    (hc : TM0.step M c = none) : gstep (simTM M S h0 w) g = none := by
  obtain ⟨q, T⟩ := c
  obtain ⟨hq, hst, htape⟩ := hr
  have hhead : g.tape g.head = T.1 := by simpa using htape 0
  have hM : M q T.1 = none := by simpa [TM0.step] using hc
  unfold gstep
  rw [hst, hhead]
  simp [simTM, hM]

theorem sim_step (hS : TM0.Supports M ↑S) {c c' : TM0.Cfg Bool Λ} {g : GCfg (SQ S w)}
    (hr : SimRel S w c g) (hc : c' ∈ TM0.step M c) :
    ∃ k g', grun (simTM M S h0 w) g k = some g' ∧ SimRel S w c' g' := by
  obtain ⟨q, T⟩ := c
  obtain ⟨hq, hst, htape⟩ := hr
  have hhead : g.tape g.head = T.1 := by simpa using htape 0
  obtain ⟨⟨q', a⟩, hM, rfl⟩ := Option.map_eq_some_iff.1 hc
  have hq' : q' ∈ S := hS.2 hM hq
  obtain ⟨st, hd, tp⟩ := g
  simp only at hst htape hhead
  subst hst
  cases a with
  | move d =>
    refine ⟨1, ⟨.inr (⟨q', hq'⟩, false), if dirB d then hd + 1 else hd - 1,
      Function.update tp hd T.1⟩, ?_, hq', rfl, ?_⟩
    · rw [grun_one]
      unfold gstep
      simp only [hhead, simTM, hM, lab_of_mem S h0 hq']
    · intro i
      simp only
      rw [Function.update_eq_self_iff.2 hhead.symm]
      cases d
      · simp only [dirB, Bool.false_eq_true, if_false, Tape.move_left_nth]
        rw [← htape]; congr 1; ring
      · simp only [dirB, if_true, Tape.move_right_nth]
        rw [← htape]; congr 1; ring
  | write b =>
    refine ⟨2, ⟨.inr (⟨q', hq'⟩, false), hd + 1 - 1, Function.update (Function.update tp hd b)
      (hd + 1) (Function.update tp hd b (hd + 1))⟩, ?_, hq', rfl, ?_⟩
    · show (grun _ _ 1).bind _ = _
      rw [grun_one]
      unfold gstep
      simp only [hhead, simTM, hM, lab_of_mem S h0 hq']
      simp only [if_true, Option.bind_some]
      rfl
    · intro i
      simp only [add_sub_cancel_right]
      rw [Function.update_eq_self_iff.2 rfl, Tape.write_nth]
      by_cases hi : i = 0
      · subst hi; simp
      · rw [if_neg hi, Function.update_of_ne (by omega), htape]

theorem sim_reaches (hS : TM0.Supports M ↑S) {c c' : TM0.Cfg Bool Λ} {g : GCfg (SQ S w)}
    (hr : SimRel S w c g) (hc : TM0.Reaches M c c') :
    ∃ k g', grun (simTM M S h0 w) g k = some g' ∧ SimRel S w c' g' := by
  induction hc with
  | refl => exact ⟨0, g, rfl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨k, g₁, hk, hr₁⟩ := ih
    obtain ⟨k', g₂, hk', hr₂⟩ := sim_step (h0 := h0) hS hr₁ hbc
    exact ⟨k + k', g₂, by rw [grun_add, hk]; exact hk', hr₂⟩

theorem mk₁_nth (i : ℤ) : (Tape.mk₁ w).nth i = if 0 ≤ i then w.getD i.toNat false else false := by
  rcases i with n | n
  · simp only [Int.ofNat_eq_natCast, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    rw [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk, List.getI_eq_getElem?_getD]
    simp [List.getD_eq_getElem?_getD]
  · simp only [Int.negSucc_not_nonneg, if_false]
    rfl

/-- The tape written by the prefix after `j` steps. -/
def preTape (j : ℕ) (x : ℤ) : Bool :=
  if -(j : ℤ) < x ∧ x ≤ 0 then w.getD ((w.length : ℤ) - 1 + x).toNat false else false

theorem sim_prefix_aux (j : ℕ) (hj : j ≤ w.length) :
    grun (simTM M S h0 w) ⟨.inl 0, 0, fun _ => false⟩ j =
      some ⟨.inl ⟨j, by omega⟩, -(j : ℤ), preTape (w := w) j⟩ := by
  induction j with
  | zero =>
    simp only [grun, Option.some.injEq]
    congr
    funext x
    simp only [preTape, Nat.cast_zero, neg_zero]
    split_ifs with h <;> [omega; rfl]
  | succ j ih =>
    rw [grun, ih (by omega), Option.bind_some]
    unfold gstep
    simp only [simTM, show j < w.length by omega, dif_pos, Bool.false_eq_true, if_false]
    congr 2
    · push_cast; ring
    · funext x
      simp only [preTape]
      by_cases hx : x = -(j : ℤ)
      · subst hx
        rw [Function.update_self]
        rw [if_pos (by push_cast; omega)]
        congr 1
        omega
      · rw [Function.update_of_ne hx]
        unfold preTape
        have : (-(j : ℤ) < x ∧ x ≤ 0) ↔ (-((j + 1 : ℕ) : ℤ) < x ∧ x ≤ 0) := by push_cast; omega
        simp only [this]

theorem sim_prefix :
    ∃ g, grun (simTM M S h0 w) ⟨.inl 0, 0, fun _ => false⟩ (w.length + 1) = some g ∧
      SimRel S w (TM0.init w) g := by
  refine ⟨⟨.inr (⟨default, h0⟩, false), -(w.length : ℤ) + 1, Function.update (preTape (w := w)
    w.length) (-(w.length : ℤ)) (preTape (w := w) w.length (-(w.length : ℤ)))⟩, ?_, h0, rfl, ?_⟩
  · rw [grun, sim_prefix_aux w.length le_rfl, Option.bind_some]
    unfold gstep
    simp only [simTM, lt_irrefl, dif_neg, not_false_eq_true, if_true, lab_of_mem S h0 h0]
  · intro i
    simp only [TM0.init]
    rw [Function.update_eq_self_iff.2 rfl, mk₁_nth, preTape]
    by_cases hi : 0 ≤ i
    · rw [if_pos hi]
      by_cases hiL : i < w.length
      · rw [if_pos (by omega)]
        congr 1
        omega
      · rw [if_neg (by omega), List.getD_eq_default]
        omega
    · rw [if_neg hi, if_neg (by omega)]

/-- If a `TM0` machine over `Bool` halts on input `w`, then the number of `true` cells in its
final tape is less than `BB N` for every `N` at least the size of the simulating machine. -/
theorem tm0_lt_BB (hS : TM0.Supports M ↑S) {b : TM0.Cfg Bool Λ}
    (hb : b ∈ StateTransition.eval (TM0.step M) (TM0.init w)) (R N : ℕ)
    (hN : w.length + 1 + S.card * 2 ≤ N) :
    ((Finset.range R).filter (fun i : ℕ => b.Tape.nth i = true)).card < BB N := by
  obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.1 hb
  obtain ⟨g₀, hg₀, hr₀⟩ := sim_prefix (M := M) (h0 := hS.1)
  obtain ⟨k, g, hk, hr⟩ := sim_reaches (h0 := hS.1) hS hr₀ hreach
  have hrun : grun (simTM M S hS.1 w) ⟨.inl 0, 0, fun _ => false⟩ (w.length + 1 + k) = some g := by
    rw [grun_add, hg₀]; exact hk
  have hlt := gen_le_BB _ _ _ _ hrun (sim_halt hr hhalt) N (by
    simp only [SQ, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_bool]
    exact hN)
  have hcount := card_true_le _ _ _ _ hrun ((Finset.range R).image fun i : ℕ => g.head + i)
  refine lt_of_le_of_lt (le_trans ?_ hcount) (by omega)
  apply Finset.card_le_card_of_injOn (fun i : ℕ => g.head + i)
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
    simp only [Finset.coe_filter, Finset.mem_image, Finset.mem_range, Set.mem_ofPred_eq]
    obtain ⟨_, _, htape⟩ := hr
    exact ⟨⟨i, hi.1, rfl⟩, by rw [htape]; exact hi.2⟩
  · intro i _ j _ hij
    simpa using hij

end TM0Sim


/-! ### Counting `true` cells of a block-encoded tape -/

section Count

open Turing

theorem nth_append' {Γ : Type} [Inhabited Γ] (l : List Γ) (L : ListBlank Γ) (i : ℕ) :
    (ListBlank.append l L).nth i = if i < l.length then l.getI i else L.nth (i - l.length) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp [ListBlank.append, ListBlank.nth_zero, ListBlank.head_cons]
    | succ i =>
      rw [ListBlank.append, ListBlank.nth_succ, ListBlank.tail_cons, ih]
      simp [List.length_cons]

theorem flatMap_nth {Γ : Type} [Inhabited Γ] {m : ℕ} (enc : Γ → List.Vector Bool m) (hf)
    (R : ListBlank Γ) (j r : ℕ) (hr : r < m) :
    (R.flatMap (fun a => (enc a).toList) hf).nth (j * m + r) = (enc (R.nth j)).get ⟨r, hr⟩ := by
  induction j generalizing R with
  | zero =>
    conv_lhs => rw [← ListBlank.cons_head_tail R]
    rw [ListBlank.cons_flatMap, nth_append']
    simp [hr, List.getI_eq_getElem, List.Vector.get_eq_get_toList, ListBlank.nth_zero]
  | succ j ih =>
    conv_lhs => rw [← ListBlank.cons_head_tail R]
    rw [ListBlank.cons_flatMap, nth_append', if_neg (by simp; nlinarith)]
    have : (j + 1) * m + r - (enc R.head).toList.length = j * m + r := by
      simp; rw [Nat.add_mul, one_mul]; omega
    rw [this, ih, ListBlank.nth_succ]

theorem count_ge {Γ : Type} [Inhabited Γ] {m : ℕ} (enc : Γ → List.Vector Bool m)
    (dec : List.Vector Bool m → Γ) (enc0 : enc default = List.Vector.replicate m false)
    (encdec : ∀ a, dec (enc a) = a) (hf) (R : ListBlank Γ) (K : ℕ)
    (hK : ∀ j < K, R.nth j ≠ default) :
    K ≤ ((Finset.range (K * m)).filter
      (fun i : ℕ => (R.flatMap (fun a => (enc a).toList) hf).nth i = true)).card := by
  have hex : ∀ j < K, ∃ r, ∃ hr : r < m, (enc (R.nth j)).get ⟨r, hr⟩ = true := by
    intro j hj
    by_contra hcon
    push Not at hcon
    apply hK j hj
    have : enc (R.nth j) = enc default := by
      rw [enc0]
      apply List.Vector.ext
      intro r
      simpa using hcon r.1 r.2
    rw [← encdec (R.nth j), this, encdec]
  choose! r hr hrt using hex
  have hdiv : ∀ j, j < K → (j * m + r j) / m = j := fun j hj => by
    have := hr j hj
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt this, zero_add]
  calc K = (Finset.range K).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn (fun j => j * m + r j)
      · intro j hj
        simp only [Finset.coe_range, Set.mem_Iio] at hj
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
        refine ⟨?_, ?_⟩
        · have := hr j hj
          have : (j + 1) * m ≤ K * m := Nat.mul_le_mul_right _ hj
          nlinarith
        · rw [flatMap_nth enc hf R j (r j) (hr j hj)]
          exact hrt j hj
      · intro a ha b hb hab
        simp only [Finset.coe_range, Set.mem_Iio] at ha hb
        have := congrArg (· / m) hab
        simp only at this
        rwa [hdiv a ha, hdiv b hb] at this

end Count

/-! ### Mathlib's compiler from partial recursive codes to `TM0` over `Bool` -/

section Chain

open Turing PartrecToTM2 ToPartrec

instance instFintypeK' : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, by intro x; cases x <;> simp⟩

theorem trPosNum_length : ∀ p : PosNum, (trPosNum p).length = p.natSize
  | .one => rfl
  | .bit0 p => by simp [trPosNum, PosNum.natSize, trPosNum_length p]
  | .bit1 p => by simp [trPosNum, PosNum.natSize, trPosNum_length p]

theorem trNum_length : ∀ a : Num, (trNum a).length = a.natSize
  | .zero => rfl
  | .pos p => trPosNum_length p

theorem trNat_length (n : ℕ) : (trNat n).length = Nat.size n := by
  rw [trNat, trNum_length, Num.natSize_to_nat, Num.to_of_nat]

theorem size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.2 (Nat.lt_two_pow_self)

theorem trInit_length {K : Type} [DecidableEq K] {Γ : K → Type} (k : K) (L : List (Γ k)) :
    (TM2to1.trInit k L).length ≤ L.length + 1 := by
  rw [← List.length_reverse (as := L)]
  unfold TM2to1.trInit
  generalize L.reverse = R
  cases R with
  | nil => exact le_refl _
  | cons a R =>
    show (List.map _ R).length + 1 ≤ _
    exact le_of_eq_of_le (congrArg (· + 1) (List.length_map _)) (by simp)

theorem length_flatMap_vec {α : Type} {m : ℕ} (enc : α → List.Vector Bool m) (l : List α) :
    (l.flatMap fun a => (enc a).toList).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih, Nat.add_mul, Nat.add_comm]

theorem chain (G : Code) : ∃ A B : ℕ, ∀ n x, G.eval [n] = pure [x] →
    ∀ N, A * n + B ≤ N → Nat.size x < BB N := by
  classical
  let _ : Inhabited Λ' := ⟨trNormal G Cont'.halt⟩
  obtain ⟨m, enc, dec, enc0, encdec⟩ :=
    TM1to1.exists_enc_dec (Γ := TM2to1.Γ' K' (fun _ : K' => Γ'))
  let M1 := TM2to1.tr (K := K') (Γ := fun _ : K' => Γ') (Λ := Λ') (σ := Option Γ') tr
  let M1b := TM1to1.tr enc dec M1
  have hS2 : TM2.Supports tr (codeSupp G Cont'.halt) := tr_supports G Cont'.halt
  have hS1 := TM2to1.tr_supports tr hS2
  have hS1b := TM1to1.tr_supports enc dec M1 hS1
  have hS0 := TM1to0.tr_supports M1b hS1b
  refine ⟨m, 2 * m + 1 + (TM1to0.trStmts M1b
    (TM1to1.trSupp M1 (TM2to1.trSupp tr (codeSupp G Cont'.halt)))).card * 2, ?_⟩
  intro n x hx N hN
  have hb2 : PartrecToTM2.halt [x] ∈ StateTransition.eval (TM2.step tr) (TM2.init K'.main (trList [n])) := by
    have : (TM2.init K'.main (trList [n]) : Cfg') = PartrecToTM2.init G [n] := by
      simp only [TM2.init, PartrecToTM2.init]
      congr
      funext k
      cases k <;> rfl
    have e := PartrecToTM2.tr_eval G [n]
    rw [hx, map_pure] at e
    rw [this, e]
    exact Part.mem_some _
  obtain ⟨b1, hT, hb1⟩ := StateTransition.tr_eval (TM2to1.tr_respects tr)
    (TM2to1.trCfg_init (Γ := fun _ : K' => Γ') K'.main (trList [n])) hb2
  obtain ⟨L', hL'⟩ := hT
  obtain ⟨b2, rfl, hb2'⟩ :=
    StateTransition.tr_eval (TM1to1.tr_respects dec M1 (enc0 := enc0) encdec) rfl hb1
  set l1 := TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])
  set w := l1.flatMap fun a => (enc a).toList
  have hinit : TM1to1.trCfg enc enc0 (TM1.init l1 : TM1.Cfg _ (TM2to1.Λ' K' (fun _ : K' => Γ')
      Λ' (Option Γ')) (Option Γ')) = TM1.init w := by
    simp only [TM1.init, TM1to1.trCfg, Tape.mk₁, Tape.mk₂, TM1to1.trTape_mk', TM1to1.trTape',
      ListBlank.flatMap_mk, Option.map_some]
    rfl
  rw [hinit] at hb2'
  obtain ⟨b0, rfl, hb0⟩ := StateTransition.tr_eval (TM1to0.tr_respects M1b) rfl hb2'
  have hw : w.length + 1 + (TM1to0.trStmts M1b
      (TM1to1.trSupp M1 (TM2to1.trSupp tr (codeSupp G Cont'.halt)))).card * 2 ≤ N := by
    have h1 : w.length ≤ (n + 2) * m := by
      rw [length_flatMap_vec]
      apply Nat.mul_le_mul_right
      have : l1.length ≤ (trList [n]).length + 1 := trInit_length _ _
      have h2 : (trList [n]).length = Nat.size n + 1 := by simp [trNat_length]
      have := size_le_self n
      omega
    nlinarith
  have hlt := tm0_lt_BB (M := TM1to0.tr M1b) hS0 hb0
    ((trList [x]).length * m) N hw
  refine lt_of_lt_of_le (b := (trList [x]).length) (by simp [trNat_length]) (le_trans ?_ hlt.le)
  have hK := count_ge enc dec enc0 encdec (by
      simp only [enc0, List.Vector.replicate, List.Vector.toList_mk]
      exact ⟨m, rfl⟩) (TM2to1.addBottom L') (trList [x]).length (by
    intro j hj hdef
    have h1 := TM2to1.addBottom_nth_snd L' j
    rw [hdef] at h1
    have h2 := TM2to1.stk_nth_val (k := K'.main) j (hL' K'.main)
    rw [← h1] at h2
    simp only [K'.elim] at h2
    rw [List.getElem?_reverse (by simpa using hj)] at h2
    simp at h2)
  refine le_trans hK (le_of_eq (congrArg Finset.card (Finset.filter_congr ?_)))
  intro i _
  show _ ↔ (TM1to1.trTape enc0 (Tape.mk' ∅ (TM2to1.addBottom L'))).nth (i : ℤ) = true
  rw [TM1to1.trTape_mk']
  unfold TM1to1.trTape'
  rw [Tape.mk'_nth_nat]

end Chain

/-! ### Radó's theorem -/

theorem rado (f : ℕ → ℕ) (hf : Computable f) : ∃ n : ℕ, f n < BB n := by
  let g : ℕ → ℕ := fun n => 2 ^ f (n * n)
  have hg : Computable g :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp.comp (Computable.const 2)
      (hf.comp (Primrec.nat_mul.to_comp.comp Computable.id Computable.id))
  obtain ⟨G, hG⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 hg)
  have hGn : ∀ n, G.eval [n] = pure [g n] := by
    intro n
    have h := hG (n ::ᵥ List.Vector.nil)
    rw [List.Vector.head_cons] at h
    exact h.trans (by simp)
  obtain ⟨A, B, hAB⟩ := chain G
  refine ⟨(A + B + 1) * (A + B + 1), ?_⟩
  have := hAB (A + B + 1) _ (hGn _) ((A + B + 1) * (A + B + 1)) (by nlinarith)
  simp only [g, Nat.size_pow] at this
  omega

end FCP.BusyBeaver.Rado

theorem solution (f : ℕ → ℕ) (hf : Computable f) : ∃ n : ℕ, f n < FCP.BusyBeaver.BB n :=
  FCP.BusyBeaver.Rado.rado f hf
