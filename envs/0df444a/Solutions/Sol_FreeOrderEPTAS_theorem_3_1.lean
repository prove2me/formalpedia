-- Prove2me | solution 1 for FreeOrderEPTAS.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T14:21:48.34587+00:00
-- url     : https://prove2.me/submissions/19b87550-3f03-47d8-8d1e-c3721dc3af0f

import Mathlib
import Definitions.Def_FreeOrderEPTAS_OPT
import Definitions.Def_FreeOrderEPTAS_freeOrder
import Definitions.Def_FreeOrderEPTAS_orc
import Theorems.Thm_FreeOrderEPTAS_corollary_3_3
import Theorems.Thm_FreeOrderEPTAS_lemma_3_2
import Theorems.Thm_FreeOrderEPTAS_value_guarantee
import Theorems.Thm_FreeOrderEPTAS_bucket_facts
import Theorems.Thm_FreeOrderEPTAS_estimate
import Theorems.Thm_FreeOrderEPTAS_value_eq_recursion

namespace FOS31
open FreeOrderEPTAS MeasureTheory

/-! ## Generic facts about `Prog` -/

def CostOK {α : Type} (p : Prog α) (S k : ℕ) : Prop :=
  ∀ s : Cost, s.maxSize ≤ S → ∀ r ∈ (p.run s).support, r.2.total ≤ s.total + k ∧ r.2.maxSize ≤ S

def Pres {α : Type} (p : Prog α) (P : α → Prop) : Prop :=
  ∀ s : Cost, ∀ r ∈ (p.run s).support, P r.1

def PrGE {α : Type} (p : Prog α) (G : α → Prop) (c : ENNReal) : Prop :=
  ∀ s : Cost, c ≤ (p.run s).toOuterMeasure {r | G r.1}

lemma supp_bind {α β : Type} (p : Prog α) (f : α → Prog β) (s : Cost) (r : β × Cost) :
    r ∈ ((p >>= f).run s).support ↔ ∃ x ∈ (p.run s).support, r ∈ ((f x.1).run x.2).support := by
  rw [StateT.run_bind]; exact PMF.mem_support_bind_iff _ _ _

lemma run_pure' {α : Type} (a : α) (s : Cost) : ((pure a : Prog α).run s) = PMF.pure (a, s) := rfl

lemma run_tick (k : ℕ) (s : Cost) : (tick k).run s = PMF.pure ((), { s with ops := s.ops + k }) := by
  simp [tick, StateT.run_modify]; rfl

lemma run_tick_bind {β : Type} (k : ℕ) (g : Unit → Prog β) (s : Cost) :
    (tick k >>= g).run s = (g ()).run { s with ops := s.ops + k } := by
  rw [StateT.run_bind, run_tick]; exact PMF.pure_bind _ _

lemma run_callLP (lp : LPSolver) (P : LPData) (s : Cost) :
    (callLP lp P).run s = PMF.pure (lp P, { s with
      ops := s.ops + P.size, lpCalls := s.lpCalls + 1, maxSize := max s.maxSize P.size }) := by
  simp [callLP, StateT.run_bind, StateT.run_modify]; rfl

lemma run_callRnd (rnd : Rounding) (P : LPData) (y : P.Vars) (s : Cost) :
    (callRnd rnd P y).run s = (rnd P y).bind (fun X => PMF.pure (X, { s with
      ops := s.ops + P.size, rndCalls := s.rndCalls + 1, maxSize := max s.maxSize P.size })) := by
  simp [callRnd, StateT.run_bind, StateT.run_modify]; rfl

/-! ### Cost -/

lemma costOK_pure {α : Type} (a : α) (S : ℕ) : CostOK (pure a : Prog α) S 0 := by
  intro s hs r hr
  rw [run_pure', PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact ⟨le_refl _, hs⟩

lemma costOK_mono {α : Type} {p : Prog α} {S k k' : ℕ} (h : CostOK p S k) (hk : k ≤ k') :
    CostOK p S k' := by
  intro s hs r hr
  obtain ⟨h1, h2⟩ := h s hs r hr
  exact ⟨by omega, h2⟩

lemma costOK_tick (k S : ℕ) : CostOK (tick k) S k := by
  intro s hs r hr
  rw [run_tick, PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact ⟨by simp [Cost.total]; omega, hs⟩

lemma costOK_bind {α β : Type} {p : Prog α} {f : α → Prog β} {S k1 k2 : ℕ}
    (hp : CostOK p S k1) (hf : ∀ a, CostOK (f a) S k2) : CostOK (p >>= f) S (k1 + k2) := by
  intro s hs r hr
  rw [supp_bind] at hr
  obtain ⟨x, hx, hr⟩ := hr
  obtain ⟨h1, h2⟩ := hp s hs x hx
  obtain ⟨h3, h4⟩ := hf x.1 x.2 h2 r hr
  exact ⟨by omega, h4⟩

lemma costOK_callLP (lp : LPSolver) (P : LPData) {S : ℕ} (hP : P.size ≤ S) :
    CostOK (callLP lp P) S (S + 1) := by
  intro s hs r hr
  rw [run_callLP, PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; refine ⟨?_, ?_⟩
  · simp [Cost.total]; omega
  · simp; omega

lemma costOK_callRnd (rnd : Rounding) (P : LPData) (y : P.Vars) {S : ℕ} (hP : P.size ≤ S) :
    CostOK (callRnd rnd P y) S (S + 1) := by
  intro s hs r hr
  rw [run_callRnd, PMF.mem_support_bind_iff] at hr
  obtain ⟨X, -, hr⟩ := hr
  rw [PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; refine ⟨?_, ?_⟩
  · simp [Cost.total]; omega
  · simp; omega

lemma costOK_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (S c : ℕ)
    (hf : ∀ b a, CostOK (f b a) S c) : ∀ b, CostOK (foldP l f b) S (l.length * (c + 1)) := by
  induction l with
  | nil => intro b; simpa [foldP] using costOK_pure b S
  | cons a l ih =>
    intro b
    simp only [foldP]
    refine costOK_mono (costOK_bind (costOK_tick 1 S) fun _ =>
      costOK_bind (hf b a) fun b' => ih b') ?_
    simp [List.length_cons]; ring_nf; omega

lemma costOK_foldProd {α β : Type} (cs : List (List α)) :
    ∀ (f : β → List α → Prog β) (S c : ℕ), (∀ b r, CostOK (f b r) S c) →
      ∀ b, CostOK (foldProd cs f b) S ((cs.map fun l => 2 * (l.length + 1)).prod * (c + 1)) := by
  induction cs with
  | nil => intro f S c hf b; simpa [foldProd] using costOK_mono (hf b []) (by omega)
  | cons l cs ih =>
    intro f S c hf b
    simp only [foldProd]
    refine costOK_mono (costOK_foldP l _ S _ (fun b a => ih (fun b' r => f b' (a :: r)) S c
      (fun b r => hf b _) b) b) ?_
    simp only [List.map_cons, List.prod_cons]
    have hpos : 0 < (cs.map fun l => 2 * (l.length + 1)).prod := by
      apply List.prod_pos; intro x hx; simp at hx; obtain ⟨a, -, rfl⟩ := hx; omega
    have h1 : 1 ≤ (cs.map fun l => 2 * (l.length + 1)).prod * (c + 1) := by
      have := Nat.mul_le_mul hpos (Nat.succ_le_succ (Nat.zero_le c)); simpa using this
    generalize (cs.map fun l => 2 * (l.length + 1)).prod = Q at h1 ⊢
    rw [mul_assoc]
    generalize Q * (c + 1) = P at h1 ⊢
    nlinarith

/-! ### Invariants -/

lemma pres_pure {α : Type} {P : α → Prop} (a : α) (h : P a) : Pres (pure a : Prog α) P := by
  intro s r hr
  rw [run_pure', PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact h

lemma pres_bind {α β : Type} {p : Prog α} {f : α → Prog β} {Q : α → Prop} {P : β → Prop}
    (hp : Pres p Q) (hf : ∀ a, Q a → Pres (f a) P) : Pres (p >>= f) P := by
  intro s r hr
  rw [supp_bind] at hr
  obtain ⟨x, hx, hr⟩ := hr
  exact hf x.1 (hp s x hx) x.2 r hr

lemma pres_tick_bind {β : Type} {g : Unit → Prog β} {P : β → Prop} (k : ℕ)
    (h : Pres (g ()) P) : Pres (tick k >>= g) P := by
  intro s r hr
  rw [run_tick_bind] at hr
  exact h _ r hr

lemma pres_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (P : β → Prop)
    (hf : ∀ b a, P b → Pres (f b a) P) : ∀ b, P b → Pres (foldP l f b) P := by
  induction l with
  | nil => intro b hb; exact pres_pure b hb
  | cons a l ih =>
    intro b hb
    simp only [foldP]
    exact pres_tick_bind 1 (pres_bind (hf b a hb) fun b' hb' => ih b' hb')

lemma pres_foldProd {α β : Type} (cs : List (List α)) (P : β → Prop) :
    ∀ (f : β → List α → Prog β), (∀ b r, P b → Pres (f b r) P) →
      ∀ b, P b → Pres (foldProd cs f b) P := by
  induction cs with
  | nil => intro f hf b hb; exact hf b [] hb
  | cons l cs ih =>
    intro f hf b hb
    simp only [foldProd]
    exact pres_foldP l _ P (fun b a hb => ih _ (fun b' r hb' => hf b' _ hb') b hb) b hb

/-! ### Probability -/

lemma pmf_bind_ge {α β : Type} (p : PMF α) (k : α → PMF β) (S : Set β) (c : ENNReal)
    (h : ∀ x ∈ p.support, c ≤ (k x).toOuterMeasure S) : c ≤ (p.bind k).toOuterMeasure S := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc c = ∑' x, p x * c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ ∑' x, p x * (k x).toOuterMeasure S := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ p.support
      · exact mul_le_mul_right (h x hx) _
      · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]

lemma pmf_bind_ge2 {α β : Type} (p : PMF α) (k : α → PMF β) (A : Set α) (S : Set β)
    (h : ∀ x ∈ p.support, x ∈ A → (k x).support ⊆ S) :
    p.toOuterMeasure A ≤ (p.bind k).toOuterMeasure S := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA]
    by_cases hx : x ∈ p.support
    · rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (h x hx hxA), mul_one]
    · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]
  · rw [Set.indicator_of_notMem hxA]; exact zero_le

lemma prGE_tick_bind {β : Type} {g : Unit → Prog β} {G : β → Prop} {c : ENNReal} (k : ℕ)
    (h : PrGE (g ()) G c) : PrGE (tick k >>= g) G c := by
  intro s; rw [run_tick_bind]; exact h _

lemma prGE_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (Inv G : β → Prop) (c : ENNReal)
    (hInv : ∀ b a, Inv b → Pres (f b a) Inv)
    (hG : ∀ b a, Inv b ∧ G b → Pres (f b a) (fun b => Inv b ∧ G b))
    (a0 : α) (ha0 : a0 ∈ l) (h0 : ∀ b, Inv b → PrGE (f b a0) G c) :
    ∀ b, Inv b → PrGE (foldP l f b) G c := by
  induction l with
  | nil => simp at ha0
  | cons a l ih =>
    intro b hb
    simp only [foldP]
    refine prGE_tick_bind 1 fun s => ?_
    rw [StateT.run_bind]
    rcases List.mem_cons.1 ha0 with rfl | hmem
    · refine le_trans (h0 b hb s) (pmf_bind_ge2 _ _ _ _ fun x hx hxG => ?_)
      have hI : Inv x.1 := hInv b a0 hb s x hx
      intro r hr
      exact (pres_foldP l f _ hG x.1 ⟨hI, hxG⟩ x.2 r hr).2
    · exact pmf_bind_ge _ _ _ _ fun x hx => ih hmem x.1 (hInv b a hb s x hx) x.2

lemma prGE_foldProd {α β : Type} (cs : List (List α)) (Inv G : β → Prop) (c : ENNReal) :
    ∀ (f : β → List α → Prog β) (g0 : List α), List.Forall₂ (fun a l => a ∈ l) g0 cs →
    (∀ b r, Inv b → Pres (f b r) Inv) →
    (∀ b r, Inv b ∧ G b → Pres (f b r) (fun b => Inv b ∧ G b)) →
    (∀ b, Inv b → PrGE (f b g0) G c) →
    ∀ b, Inv b → PrGE (foldProd cs f b) G c := by
  induction cs with
  | nil => intro f g0 hg hInv hG h0 b hb; cases hg; exact h0 b hb
  | cons l cs ih =>
    intro f g0 hg hInv hG h0 b hb
    cases hg with
    | cons ha hg' =>
      rename_i a0 g1
      simp only [foldProd]
      refine prGE_foldP l _ Inv G c
        (fun b a hb => pres_foldProd cs Inv _ (fun b' r hb' => hInv b' _ hb') b hb)
        (fun b a hb => pres_foldProd cs _ _ (fun b' r hb' => hG b' _ hb') b hb)
        a0 ha (fun b hb => ih _ g1 hg' (fun b' r hb' => hInv b' _ hb')
          (fun b' r hb' => hG b' _ hb') (fun b' hb' => h0 b' hb') b hb) b hb

/-! ## The verification `check` -/
lemma forall₂_replicate {α : Type} (c : List α) :
    ∀ g : List α, (∀ x ∈ g, x ∈ c) → List.Forall₂ (fun a l => a ∈ l) g (List.replicate g.length c) := by
  intro g
  induction g with
  | nil => intro _; simp
  | cons a g ih =>
    intro h
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (h a (by simp)) (ih fun x hx => h x (by simp [hx]))


/-! ## Shifts -/

def sh (s c : Cost) : Cost :=
  ⟨s.ops + c.ops, s.oracle + c.oracle, s.lpCalls + c.lpCalls, s.rndCalls + c.rndCalls,
    max s.maxSize c.maxSize⟩

@[simp] lemma zero_ops : (0 : Cost).ops = 0 := rfl
@[simp] lemma zero_oracle : (0 : Cost).oracle = 0 := rfl
@[simp] lemma zero_lpCalls : (0 : Cost).lpCalls = 0 := rfl
@[simp] lemma zero_rndCalls : (0 : Cost).rndCalls = 0 := rfl
@[simp] lemma zero_maxSize : (0 : Cost).maxSize = 0 := rfl

lemma sh_zero (s : Cost) : sh s 0 = s := by
  cases s; simp [sh]

lemma sh_assoc (s c c' : Cost) : sh (sh s c) c' = sh s (sh c c') := by
  simp only [sh, Cost.mk.injEq]; refine ⟨by omega, by omega, by omega, by omega, max_assoc _ _ _⟩

def Shift {α : Type} (p : Prog α) : Prop :=
  ∀ s, p.run s = (p.run 0).map (fun r => (r.1, sh s r.2))

lemma shift_pure {α : Type} (a : α) : Shift (pure a : Prog α) := by
  intro s; rw [run_pure', run_pure', PMF.pure_map, sh_zero]

lemma shift_bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : Shift p)
    (hf : ∀ a, Shift (f a)) : Shift (p >>= f) := by
  intro s
  rw [StateT.run_bind, hp s]
  show PMF.bind _ _ = _
  rw [PMF.bind_map, StateT.run_bind]
  show _ = PMF.map _ (PMF.bind _ _)
  rw [PMF.map_bind]
  congr 1; funext x
  simp only [Function.comp]
  rw [hf x.1 (sh s x.2), hf x.1 x.2, PMF.map_comp]
  congr 1; funext r; simp [sh_assoc]

lemma shift_modify (F : Cost → Cost) (hF : ∀ s, F s = sh s (F 0)) :
    Shift (modify F : Prog Unit) := by
  intro s
  simp only [StateT.run_modify]
  show PMF.pure ((), F s) = (PMF.pure ((), F 0)).map _
  rw [PMF.pure_map, ← hF]

lemma shift_tick (k : ℕ) : Shift (tick k) := by
  unfold tick; apply shift_modify; intro s; cases s; simp [sh]

lemma shift_opn {α : Type} (k : ℕ) (a : α) : Shift (opn k a) := by
  unfold opn; exact shift_bind (shift_tick k) fun _ => shift_pure a

lemma shift_callOrc {n : ℕ} (o : Fin n → ℝ → ℝ) (j : Fin n) (v : ℝ) : Shift (callOrc o j v) := by
  unfold callOrc
  refine shift_bind (shift_modify _ ?_) fun _ => shift_pure _
  intro s; cases s; simp [sh]

lemma shift_callLP (lp : LPSolver) (P : LPData) : Shift (callLP lp P) := by
  unfold callLP
  refine shift_bind (shift_modify _ ?_) fun _ => shift_pure _
  intro s; cases s; simp [sh]

lemma shift_lift {α : Type} (q : PMF α) : Shift (StateT.lift q : Prog α) := by
  intro s
  simp only [StateT.run_lift]
  show q.bind (fun a => PMF.pure (a, s)) = (q.bind fun a => PMF.pure (a, 0)).map _
  rw [PMF.map_bind]; congr 1; funext a; rw [PMF.pure_map, sh_zero]

lemma shift_callRnd (rnd : Rounding) (P : LPData) (y : P.Vars) : Shift (callRnd rnd P y) := by
  unfold callRnd
  refine shift_bind (shift_modify _ ?_) fun _ => shift_lift _
  intro s; cases s; simp [sh]

lemma shift_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (hf : ∀ b a, Shift (f b a)) :
    ∀ b, Shift (foldP l f b) := by
  induction l with
  | nil => intro b; exact shift_pure b
  | cons a l ih =>
    intro b; simp only [foldP]
    exact shift_bind (shift_tick 1) fun _ => shift_bind (hf b a) fun b' => ih b'

lemma shift_foldProd {α β : Type} (cs : List (List α)) :
    ∀ (f : β → List α → Prog β), (∀ b r, Shift (f b r)) → ∀ b, Shift (foldProd cs f b) := by
  induction cs with
  | nil => intro f hf b; exact hf b []
  | cons l cs ih =>
    intro f hf b; simp only [foldProd]
    exact shift_foldP l _ (fun b a => ih _ (fun b' r => hf b' _) b) b

lemma shift_santa {m D n : ℕ} (ε : ℝ) (I : SCInstance m D n) (lp : LPSolver) (rnd : Rounding) :
    Shift (santaClaus ε I lp rnd) := by
  unfold santaClaus
  refine shift_bind (shift_opn _ _) fun _ => ?_
  refine shift_bind (shift_opn _ _) fun _ => ?_
  refine shift_bind (shift_opn _ _) fun _ => ?_
  refine shift_bind (shift_opn _ _) fun _ => ?_
  refine shift_bind (shift_tick _) fun _ => ?_
  refine shift_bind (shift_tick _) fun _ => ?_
  refine shift_bind (shift_tick _) fun _ => ?_
  refine shift_bind (shift_tick _) fun _ => ?_
  refine shift_foldProd _ _ (fun b gN => shift_foldProd _ _ (fun b gS => ?_) b) _
  rcases b with _ | X
  · refine shift_bind (shift_callLP _ _) fun y => ?_
    rcases y with _ | y
    · exact shift_pure _
    · refine shift_bind (shift_callRnd _ _ _) fun X => ?_
      exact shift_bind (shift_tick _) fun _ => shift_pure _
  · exact shift_pure _

/-! ## Consequences of shifts -/

lemma supp_shift {α : Type} {p : Prog α} (hp : Shift p) (s : Cost) (r : α × Cost)
    (hr : r ∈ (p.run s).support) : ∃ c ∈ (p.run 0).support, r = (c.1, sh s c.2) := by
  rw [hp s, PMF.support_map] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  exact ⟨c, hc, rfl⟩

lemma prob_shift {α : Type} {p : Prog α} (hp : Shift p) (G : α → Prop) (s : Cost) :
    (p.run s).toOuterMeasure {r | G r.1} = (p.run 0).toOuterMeasure {r | G r.1} := by
  rw [hp s, PMF.toOuterMeasure_map_apply]; rfl

lemma sh_total (s c : Cost) : (sh s c).total = s.total + c.total := by
  simp [sh, Cost.total]; omega

lemma costOK_of_shift {α : Type} {p : Prog α} (hp : Shift p) {S k : ℕ}
    (h : ∀ c ∈ (p.run 0).support, c.2.total ≤ k ∧ c.2.maxSize ≤ S) : CostOK p S k := by
  intro s hs r hr
  obtain ⟨c, hc, rfl⟩ := supp_shift hp s r hr
  refine ⟨?_, max_le hs (h c hc).2⟩
  rw [sh_total]; have := (h c hc).1; omega

lemma costOK_bind' {α β : Type} {p : Prog α} {f : α → Prog β} {S k1 k2 : ℕ} {Q : α → Prop}
    (hp : CostOK p S k1) (hq : Pres p Q) (hf : ∀ a, Q a → CostOK (f a) S k2) :
    CostOK (p >>= f) S (k1 + k2) := by
  intro s hs r hr
  rw [supp_bind] at hr
  obtain ⟨x, hx, hr⟩ := hr
  obtain ⟨h1, h2⟩ := hp s hs x hx
  obtain ⟨h3, h4⟩ := hf x.1 (hq s x hx) x.2 h2 r hr
  exact ⟨by omega, h4⟩

lemma costOK_opn {α : Type} (k S : ℕ) (a : α) : CostOK (opn k a) S k := by
  unfold opn; simpa using costOK_bind (costOK_tick k S) fun _ => costOK_pure a S

lemma run_callOrc {n : ℕ} (o : Fin n → ℝ → ℝ) (j : Fin n) (v : ℝ) (s : Cost) :
    (callOrc o j v).run s = PMF.pure (o j v, { s with oracle := s.oracle + 1 }) := by
  simp [callOrc, StateT.run_modify]; rfl

lemma costOK_callOrc {n : ℕ} (o : Fin n → ℝ → ℝ) (j : Fin n) (v : ℝ) (S : ℕ) :
    CostOK (callOrc o j v) S 1 := by
  intro s hs r hr
  rw [run_callOrc, PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact ⟨by simp [Cost.total]; omega, hs⟩

lemma pres_callOrc {n : ℕ} {P : ℝ → Prop} (o : Fin n → ℝ → ℝ) (j : Fin n) (v : ℝ)
    (h : P (o j v)) : Pres (callOrc o j v) P := by
  intro s r hr
  rw [run_callOrc, PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact h

lemma pres_true {α : Type} (p : Prog α) : Pres p (fun _ => True) := fun _ _ _ => trivial

lemma pres_mono {α : Type} {p : Prog α} {P Q : α → Prop} (h : Pres p P) (hPQ : ∀ a, P a → Q a) :
    Pres p Q := fun s r hr => hPQ _ (h s r hr)

lemma pres_opn_bind {α β : Type} {k : ℕ} {a : α} {f : α → Prog β} {P : β → Prop}
    (h : Pres (f a) P) : Pres (opn k a >>= f) P := by
  unfold opn; rw [bind_assoc]; simp only [pure_bind]; exact pres_tick_bind k h

lemma pres_opn {α : Type} {k : ℕ} {a : α} {P : α → Prop} (h : P a) : Pres (opn k a) P := by
  unfold opn; exact pres_tick_bind k (pres_pure a h)

lemma prGE_bind {α β : Type} {p : Prog α} {f : α → Prog β} {Q : α → Prop} {G : β → Prop}
    {c : ENNReal} (hp : Pres p Q) (hf : ∀ a, Q a → PrGE (f a) G c) : PrGE (p >>= f) G c := by
  intro s; rw [StateT.run_bind]
  exact pmf_bind_ge _ _ _ _ fun x hx => hf x.1 (hp s x hx) x.2

lemma prGE_bind2 {α β : Type} {p : Prog α} {f : α → Prog β} {A : α → Prop} {G : β → Prop}
    {c : ENNReal} (hA : PrGE p A c) (h : ∀ a, A a → Pres (f a) G) : PrGE (p >>= f) G c := by
  intro s; rw [StateT.run_bind]
  refine le_trans (hA s) (pmf_bind_ge2 _ _ _ _ fun x hx hxA => ?_)
  intro r hr; exact h x.1 hxA x.2 r hr

lemma prGE_opn_bind {α β : Type} {k : ℕ} {a : α} {f : α → Prog β} {G : β → Prop} {c : ENNReal}
    (h : PrGE (f a) G c) : PrGE (opn k a >>= f) G c := by
  unfold opn; rw [bind_assoc]; simp only [pure_bind]; exact prGE_tick_bind k h

/-! ## The recursion -/

lemma shift_recursion {n : ℕ} (o : Fin n → ℝ → ℝ) (σ : Equiv.Perm (Fin n)) :
    Shift (recursionP o σ) := by
  unfold recursionP
  exact shift_foldP _ _ (fun v t => shift_bind (shift_opn _ _) fun j => shift_callOrc _ _ _) 0

lemma recursion_val {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) :
    Pres (recursionP (orc I) σ) (· = R I σ 0) := by
  intro s r hr
  obtain ⟨c, hc, rfl⟩ := supp_shift (shift_recursion _ _) s r hr
  exact ((value_eq_recursion I σ).2.2 c hc).1

lemma recursion_cost {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (S : ℕ) :
    CostOK (recursionP (orc I) σ) S (3 * n) := by
  refine costOK_of_shift (shift_recursion _ _) fun c hc => ⟨((value_eq_recursion I σ).2.2 c hc).2, ?_⟩
  -- maxSize stays 0
  have : ∀ s, s.maxSize = 0 → ∀ r ∈ ((recursionP (orc I) σ).run s).support, r.2.maxSize = 0 := by
    intro s hs r hr
    have := (costOK_foldP (List.finRange n).reverse _ 0 2 (fun v t =>
      costOK_bind (costOK_opn 1 0 _) fun j => costOK_callOrc _ _ _ 0) 0) s (by omega) r hr
    omega
  rw [this 0 rfl c hc]; exact Nat.zero_le _

/-! ## Tables -/

lemma tab_fold {β : Type} {k : ℕ} (f : Fin k → Prog β) (v : Fin k → β)
    (hf : ∀ a, Pres (f a) (· = v a)) :
    ∀ (l : List (Fin k)) (acc : List β),
      Pres (foldP l (fun acc a => do
        let x ← f a
        opn 1 (acc ++ [x])) acc) (· = acc ++ l.map v) := by
  intro l
  induction l with
  | nil => intro acc; exact pres_pure _ (by simp)
  | cons a l ih =>
    intro acc
    simp only [foldP]
    refine pres_tick_bind 1 (pres_bind (Q := fun b' => b' = acc ++ [v a])
      (pres_bind (hf a) fun x hx => pres_opn (by rw [hx])) fun b' hb' => ?_)
    subst hb'
    exact pres_mono (ih _) fun r hr => by rw [hr]; simp

lemma tab_val {β : Type} [Inhabited β] {k : ℕ} (f : Fin k → Prog β) (v : Fin k → β)
    (hf : ∀ a, Pres (f a) (· = v a)) : Pres (tabP f) (· = v) := by
  unfold tabP
  refine pres_bind (tab_fold f v hf _ []) fun l hl => pres_pure _ ?_
  subst hl; funext a; simp [List.getD_eq_getElem?_getD]

lemma tab_cost {β : Type} [Inhabited β] {k : ℕ} (f : Fin k → Prog β) (S c : ℕ)
    (hf : ∀ a, CostOK (f a) S c) : CostOK (tabP f) S (k * (c + 1 + 1)) := by
  unfold tabP
  have := costOK_bind (costOK_foldP (List.finRange k) (fun acc a => do
        let x ← f a
        opn 1 (acc ++ [x])) S (c + 1) (fun b a => costOK_bind (hf a) fun x => costOK_opn 1 S _) [])
    (fun l => costOK_pure (fun a : Fin k => l.getD a.val default) S)
  simpa using this

lemma tom_ne_top {α : Type} (p : PMF α) (T : Set α) : p.toOuterMeasure T ≠ ⊤ := by
  have hT : p.toOuterMeasure T ≤ 1 := by
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).2 (Set.subset_univ _)]
    exact p.toOuterMeasure.mono (Set.subset_univ _)
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hT

/-! ## Santa Claus via Corollary 3.3 -/

def CorStmt (tc : ℕ → ℕ) (dc : ℕ) : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ (m n : ℕ), m ≤ 2 * q + 1 →
      ∀ (I : Instance n) (b Δ : Fin m → ℝ), (∀ i, 0 ≤ b i) →
      ∀ (lp : LPSolver) (rnd : Rounding), IsLPSolver lp → IsDependentRounding rnd →
        (IPProphetsFeasible I b Δ → (1 / 2 : ℝ) ≤
          pr ((santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ)
            lp rnd).run 0)
            {r | ∃ x, r.1 = some x ∧ ProphetCard x ∧
              ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)}) ∧
        ∀ r ∈ ((santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ)
            lp rnd).run 0).support,
          (∀ x, r.1 = some x → ProphetCard x ∧
            ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)) ∧
          r.2.total ≤ tc q * (n + 1) ^ dc ∧ r.2.maxSize ≤ tc q * (n + 1)

lemma cor_exists : ∃ tc dc, CorStmt tc dc := corollary_3_3

section cand
variable {tc : ℕ → ℕ} {dc : ℕ} (hcor : CorStmt tc dc)
include hcor

lemma santa_good {q : ℕ} (hq : 2 ≤ q) {m n : ℕ} (hm : m ≤ 2 * q + 1) (I : Instance n)
    (b Δ : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp)
    (hrnd : IsDependentRounding rnd) (hfeas : IPProphetsFeasible I b Δ) :
    PrGE (santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ) lp rnd)
      (fun r => ∃ x, r = some x ∧ ProphetCard x ∧
        ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j))
      (ENNReal.ofReal (1 / 2)) := by
  intro s
  have e := prob_shift (shift_santa (1 / (q : ℝ))
    (prophetInstance (fun i j => orc I j (b i) - b i) Δ) lp rnd)
    (fun r => ∃ x, r = some x ∧ ProphetCard x ∧
        ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)) s
  rw [e]
  have h := (hcor q hq m n hm I b Δ hb lp rnd hlp hrnd).1 hfeas
  unfold pr at h
  rw [ENNReal.ofReal_le_iff_le_toReal
    (tom_ne_top _ _)]
  exact h

lemma santa_cost {q : ℕ} (hq : 2 ≤ q) {m n : ℕ} (hm : m ≤ 2 * q + 1) (I : Instance n)
    (b Δ : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp)
    (hrnd : IsDependentRounding rnd) :
    CostOK (santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ) lp rnd)
      (tc q * (n + 1)) (tc q * (n + 1) ^ dc) := by
  refine costOK_of_shift (shift_santa _ _ _ _) fun c hc => ?_
  have h := (hcor q hq m n hm I b Δ hb lp rnd hlp hrnd).2 c hc
  exact ⟨h.2.1, h.2.2⟩

end cand

/-! ## The candidate step -/

lemma w_val {n : ℕ} (I : Instance n) (m : ℕ) (g : List ℝ) :
    Pres (tabP fun i : Fin m => tabP fun j : Fin n => do
        let bi ← opn 1 (g.getD i.val 0)
        let v ← callOrc (orc I) j bi
        opn 1 (v - bi))
      (· = fun i j => orc I j (g.getD i.val 0) - g.getD i.val 0) := by
  refine tab_val _ _ fun i => tab_val _ _ fun j => ?_
  refine pres_opn_bind ?_
  exact pres_bind (pres_callOrc (P := (· = orc I j (g.getD i.val 0))) _ _ _ rfl)
    fun v hv => pres_opn (by rw [hv])

lemma w_cost {n : ℕ} (I : Instance n) (m : ℕ) (g : List ℝ) (S : ℕ) :
    CostOK (tabP fun i : Fin m => tabP fun j : Fin n => do
        let bi ← opn 1 (g.getD i.val 0)
        let v ← callOrc (orc I) j bi
        opn 1 (v - bi)) S (m * (n * 5 + 2)) := by
  have := tab_cost _ S _ fun i : Fin m => tab_cost _ S _ fun j : Fin n =>
    costOK_bind (costOK_opn 1 S (g.getD i.val 0)) fun bi =>
      costOK_bind (costOK_callOrc (orc I) j bi S) fun v => costOK_opn 1 S (v - bi)
  simpa using this

/-- The value invariant. -/
def Inv {n : ℕ} (I : Instance n) (best : Equiv.Perm (Fin n) × ℝ) : Prop := best.2 = V I best.1

lemma cand_pres {n : ℕ} (I : Instance n) (ϵ : ℝ) (lp : LPSolver) (rnd : Rounding) (m : ℕ)
    (best : Equiv.Perm (Fin n) × ℝ) (g : List ℝ) (P : Equiv.Perm (Fin n) × ℝ → Prop)
    (h1 : P best) (h2 : ∀ x : Assignment m n, ¬ R I (FreeOrderEPTAS.orderOf x) 0 ≤ best.2 →
      P (FreeOrderEPTAS.orderOf x, R I (FreeOrderEPTAS.orderOf x) 0)) :
    Pres (candidate ϵ (orc I) lp rnd m best g) P := by
  unfold candidate
  refine pres_bind (pres_true _) fun w _ => ?_
  refine pres_tick_bind _ ?_
  refine pres_bind (pres_true _) fun r _ => ?_
  rcases r with _ | x
  · exact pres_pure _ h1
  · refine pres_tick_bind _ ?_
    refine pres_bind (recursion_val I _) fun v hv => ?_
    subst hv
    refine pres_opn_bind (pres_pure _ ?_)
    by_cases hc : R I (FreeOrderEPTAS.orderOf x) 0 ≤ best.2
    · simp [hc, h1]
    · simp [hc, h2 x hc]

section cand2
variable {tc : ℕ → ℕ} {dc : ℕ} (hcor : CorStmt tc dc)
include hcor

lemma cand_good {q : ℕ} (hq : 2 ≤ q) {m n : ℕ} (hm : m ≤ 2 * q + 1) (I : Instance n)
    (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd)
    (b Δ : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) (hfeas : IPProphetsFeasible I b Δ) (g : List ℝ)
    (hgb : ∀ i : Fin m, g.getD i.val 0 = b i) (hgΔ : ∀ i : Fin m, g.getD (m + i.val) 0 = Δ i)
    (c0 : ℝ) (hgood : ∀ x : Assignment m n, ProphetCard x →
      (∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)) →
      c0 ≤ V I (FreeOrderEPTAS.orderOf x))
    (best : Equiv.Perm (Fin n) × ℝ) :
    PrGE (candidate (1 / (q : ℝ)) (orc I) lp rnd m best g) (fun best => c0 ≤ best.2)
      (ENNReal.ofReal (1 / 2)) := by
  unfold candidate
  refine prGE_bind (w_val I m g) fun w hw => ?_
  subst hw
  refine prGE_tick_bind _ ?_
  have e1 : (fun (i : Fin m) (j : Fin n) => orc I j (g.getD i.val 0) - g.getD i.val 0) =
      fun i j => orc I j (b i) - b i := by funext i j; rw [hgb]
  have e2 : (fun i : Fin m => g.getD (m + i.val) 0) = Δ := funext hgΔ
  simp only [e1, e2]
  refine prGE_bind2 (santa_good hcor hq hm I b Δ hb lp rnd hlp hrnd hfeas) fun r hr => ?_
  obtain ⟨x, rfl, hx1, hx2⟩ := hr
  refine pres_tick_bind _ (pres_bind (recursion_val I _) fun v hv => ?_)
  subst hv
  refine pres_opn_bind (pres_pure _ ?_)
  have := hgood x hx1 hx2
  rw [(value_eq_recursion I _).1] at this
  by_cases hc : R I (FreeOrderEPTAS.orderOf x) 0 ≤ best.2
  · simp [hc]; linarith
  · simp [hc]; exact this

lemma cand_cost {q : ℕ} (hq : 2 ≤ q) {m n : ℕ} (hm : m ≤ 2 * q + 1) (I : Instance n)
    (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd)
    (best : Equiv.Perm (Fin n) × ℝ) (g : List ℝ) (hg : ∀ i : Fin m, 0 ≤ g.getD i.val 0) :
    CostOK (candidate (1 / (q : ℝ)) (orc I) lp rnd m best g) (tc q * (n + 1))
      (m * (n * 5 + 2) + (4 * (m + 1) * (n + 1) + (tc q * (n + 1) ^ dc +
        ((n + 1) * (m + 1) + (n + 1) * (n + 1) + (3 * n + 1))))) := by
  unfold candidate
  refine costOK_bind' (w_cost I m g _) (w_val I m g) fun w hw => ?_
  subst hw
  refine costOK_bind (costOK_tick _ _) fun _ => ?_
  refine costOK_bind (santa_cost hcor hq hm I (fun i => g.getD i.val 0) _ hg lp rnd hlp hrnd)
    fun r => ?_
  rcases r with _ | x
  · exact costOK_mono (costOK_pure _ _) (Nat.zero_le _)
  · refine costOK_bind (costOK_tick _ _) fun _ => costOK_bind (recursion_cost I _ _) fun v => ?_
    exact costOK_mono (costOK_bind (costOK_opn 1 _ _) fun _ => costOK_pure _ _) (by simp)

end cand2

/-! ## Facts about values -/

lemma orc_ge {n : ℕ} (I : Instance n) (j : Fin n) (v : ℝ) : v ≤ orc I j v := by
  unfold orc
  have hi : Integrable (fun x => max x v) (I.μ j) := (I.integrable j).sup (integrable_const v)
  calc v = ∫ _x, v ∂(I.μ j) := by simp
    _ ≤ _ := integral_mono (integrable_const v) hi (fun x => le_max_right _ _)

lemma R_nonneg {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (t : ℕ) : 0 ≤ R I σ t := by
  unfold R
  generalize (List.finRange n).drop t = l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons]; exact ih.trans (orc_ge _ _ _)

lemma V_nonneg {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : 0 ≤ V I σ := by
  rw [(value_eq_recursion I σ).1]; exact R_nonneg _ _ _

lemma OPT_ge {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : V I σ ≤ OPT I :=
  Finset.le_sup' (V I) (Finset.mem_univ σ)

lemma OPT_nonneg {n : ℕ} (I : Instance n) : 0 ≤ OPT I := (V_nonneg I 1).trans (OPT_ge I 1)

lemma opn_bind {α β : Type} (k : ℕ) (a : α) (f : α → Prog β) :
    opn k a >>= f = tick k >>= fun _ => f a := by
  unfold opn; rw [bind_assoc]; simp only [pure_bind]

lemma prGE_pure {α : Type} {G : α → Prop} {c : ENNReal} (a : α) (h : G a) (hc : c ≤ 1) :
    PrGE (pure a : Prog α) G c := by
  intro s; rw [run_pure', PMF.toOuterMeasure_pure_apply, if_pos (show (a, s) ∈ {r : α × Cost | G r.1} from h)]
  exact hc

lemma prGE_and {α : Type} {p : Prog α} {G Q : α → Prop} {c : ENNReal} (h : PrGE p G c)
    (hq : Pres p Q) : PrGE p (fun a => Q a ∧ G a) c := by
  intro s
  refine (h s).trans ?_
  rw [← PMF.toOuterMeasure_apply_inter_support]
  refine (PMF.toOuterMeasure _).mono ?_
  rintro r ⟨h1, h2⟩
  exact ⟨hq s r h2, h1⟩

lemma cand_fold_pres {n : ℕ} (I : Instance n) (ϵ : ℝ) (lp : LPSolver) (rnd : Rounding) (m : ℕ)
    (P : Equiv.Perm (Fin n) × ℝ → Prop)
    (hP : ∀ best (x : Assignment m n), P best → ¬ R I (FreeOrderEPTAS.orderOf x) 0 ≤ best.2 →
      P (FreeOrderEPTAS.orderOf x, R I (FreeOrderEPTAS.orderOf x) 0)) :
    ∀ (cs : List (List ℝ)) b, P b → Pres (foldProd cs (candidate ϵ (orc I) lp rnd m) b) P :=
  fun cs => pres_foldProd cs P _ (fun b r hb => cand_pres I ϵ lp rnd m b r P hb (fun x hx => hP b x hb hx))

lemma g0_b {m : ℕ} (b Δ : Fin m → ℝ) (i : Fin m) : (List.ofFn b ++ List.ofFn Δ).getD i.val 0 = b i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]; simp

lemma g0_Δ {m : ℕ} (b Δ : Fin m → ℝ) (i : Fin m) :
    (List.ofFn b ++ List.ofFn Δ).getD (m + i.val) 0 = Δ i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

lemma g0_forall {m : ℕ} (b Δ : Fin m → ℝ) (c : List ℝ) (hb : ∀ i, b i ∈ c) (hΔ : ∀ i, Δ i ∈ c) :
    List.Forall₂ (fun a l => a ∈ l) (List.ofFn b ++ List.ofFn Δ) (List.replicate (2 * m) c) := by
  have h := forall₂_replicate c (List.ofFn b ++ List.ofFn Δ) (by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact hb i
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact hΔ i)
  have hl : (List.ofFn b ++ List.ofFn Δ).length = 2 * m := by simp; ring
  rwa [hl] at h

section main
variable {tc : ℕ → ℕ} {dc : ℕ} (hcor : CorStmt tc dc)
include hcor

lemma main_prob (ε : ℝ) (hε : 0 < ε) {n : ℕ} (I : Instance n) (lp : LPSolver) (rnd : Rounding)
    (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd) :
    PrGE (freeOrder ε (orc I) lp rnd) (fun σ => (1 - ε) * OPT I ≤ V I σ)
      (ENNReal.ofReal (1 / 2)) := by
  unfold freeOrder
  simp only [opn_bind]
  generalize hqd : ⌈14 / min ε 1⌉₊ = q
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have hqr : 14 / min ε 1 ≤ (q : ℝ) := hqd ▸ Nat.le_ceil _
  have hq14r : (14 : ℝ) ≤ q := by
    refine le_trans ?_ hqr
    rw [le_div_iff₀ hmin]; nlinarith [min_le_right ε 1]
  have hq2 : 2 ≤ q := by exact_mod_cast (show (2 : ℝ) ≤ q by linarith)
  have hqpos : (0 : ℝ) < q := by linarith
  have h7 : 7 * (1 / (q : ℝ)) ≤ ε := by
    have : 1 / (q : ℝ) ≤ min ε 1 / 14 := by
      rw [div_le_div_iff₀ hqpos (by norm_num)]; rw [div_le_iff₀ hmin] at hqr; linarith
    linarith [min_le_left ε 1]
  set ϵ : ℝ := 1 / (q : ℝ) with hϵ
  have hϵpos : 0 < ϵ := by positivity
  have hϵ1 : ϵ < 1 := by rw [hϵ, div_lt_one hqpos]; linarith
  refine prGE_tick_bind 3 (prGE_tick_bind 1 (prGE_bind (recursion_val I 1) fun v₀ hv₀ => ?_))
  rw [← (value_eq_recursion I 1).1] at hv₀
  refine prGE_tick_bind 1 ?_
  by_cases hv : v₀ ≤ 0
  · rw [if_pos (by simpa using hv)]
    refine prGE_pure _ ?_ (by rw [ENNReal.ofReal_le_one]; norm_num)
    have h1 := V_nonneg I 1
    have h2 := (estimate I).2.2.1 1
    have h3 := OPT_nonneg I
    have : OPT I = 0 := by linarith
    rw [this]; simpa using h1
  · rw [if_neg (by simpa using hv)]
    push Not at hv
    refine prGE_tick_bind 5 (prGE_tick_bind 6 ?_)
    obtain ⟨k, hk, hkl, hku⟩ := (estimate I).2.2.2 1 ϵ hϵpos hϵ1.le
    obtain ⟨σs, -, hσs⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (V I)
    have hopt : V I σs = OPT I := hσs.symm
    have hE1 : (1 - ϵ) * OPT I ≤ v₀ * (1 + ϵ) ^ k := by rw [hv₀]; exact hkl
    have hE2 : v₀ * (1 + ϵ) ^ k ≤ OPT I := by rw [hv₀]; exact hku
    have hEpos : 0 ≤ v₀ * (1 + ϵ) ^ k := by positivity
    obtain ⟨hfeasAll, hex⟩ := lemma_3_2 I σs hopt ϵ (v₀ * (1 + ϵ) ^ k) q (by omega) rfl
    obtain ⟨b, Δ, hguess, hgrid⟩ := hex hϵ1 hE1 hE2
    have hK : numJumps I σs ϵ ≤ q := by
      have := (bucket_facts I σs ϵ q (by omega) rfl).1
      rw [hϵ, one_div_one_div] at this
      exact_mod_cast this
    have hOPT := OPT_nonneg I
    have hInvP : ∀ (m : ℕ) best (x : Assignment m n), Inv I best → ¬ R I (FreeOrderEPTAS.orderOf x) 0 ≤ best.2 →
        Inv I (FreeOrderEPTAS.orderOf x, R I (FreeOrderEPTAS.orderOf x) 0) :=
      fun m best x _ _ => (value_eq_recursion I _).1.symm
    have hGP : ∀ (m : ℕ) best (x : Assignment m n),
        (Inv I best ∧ (1 - 7 * ϵ) * OPT I ≤ best.2) → ¬ R I (FreeOrderEPTAS.orderOf x) 0 ≤ best.2 →
        (Inv I (FreeOrderEPTAS.orderOf x, R I (FreeOrderEPTAS.orderOf x) 0) ∧
          (1 - 7 * ϵ) * OPT I ≤ (FreeOrderEPTAS.orderOf x, R I (FreeOrderEPTAS.orderOf x) 0).2) :=
      fun m best x hb hx => ⟨(value_eq_recursion I _).1.symm, by
        push Not at hx; exact hb.2.trans hx.le⟩
    refine prGE_bind2 (A := fun best => Inv I best ∧ (1 - 7 * ϵ) * OPT I ≤ best.2)
      (prGE_and ?_ ?_) fun best hb => pres_pure _ ?_
    · refine prGE_foldP _ _ (Inv I) (fun best => (1 - 7 * ϵ) * OPT I ≤ best.2) _
        (fun b a hb => pres_tick_bind _ (pres_foldP _ _ _ (fun b K hb => pres_tick_bind _
          (cand_fold_pres I ϵ lp rnd _ _ (hInvP _) _ b hb)) b hb))
        (fun b a hb => pres_tick_bind _ (pres_foldP _ _ _ (fun b K hb => pres_tick_bind _
          (cand_fold_pres I ϵ lp rnd _ _ (hGP _) _ b hb)) b hb))
        k (List.mem_range.2 (by omega)) ?_ _ hv₀
      intro best hb
      refine prGE_tick_bind _ ?_
      refine prGE_foldP _ _ (Inv I) (fun best => (1 - 7 * ϵ) * OPT I ≤ best.2) _
        (fun b K hb => pres_tick_bind _ (cand_fold_pres I ϵ lp rnd _ _ (hInvP _) _ b hb))
        (fun b K hb => pres_tick_bind _ (cand_fold_pres I ϵ lp rnd _ _ (hGP _) _ b hb))
        (numJumps I σs ϵ) (List.mem_range.2 (by omega)) ?_ _ hb
      intro best hb
      refine prGE_tick_bind _ ?_
      refine prGE_foldProd _ (Inv I) (fun best => (1 - 7 * ϵ) * OPT I ≤ best.2) _ _
        (List.ofFn b ++ List.ofFn Δ)
        (g0_forall b Δ _ (fun i => (hgrid i).1) (fun i => (hgrid i).2))
        (fun b r hb => cand_pres I ϵ lp rnd _ b r _ hb (fun x hx => hInvP _ b x hb hx))
        (fun b r hb => cand_pres I ϵ lp rnd _ b r _ hb (fun x hx => hGP _ b x hb hx))
        ?_ _ hb
      intro best _
      exact cand_good hcor hq2 (by omega) I lp rnd hlp hrnd b Δ hguess.base_nonneg
        (hfeasAll b Δ hguess) _ (g0_b b Δ) (g0_Δ b Δ) _
        (fun x hx1 hx2 => value_guarantee I σs ϵ _ b Δ x
          ⟨hopt, ⟨q, by omega, rfl⟩, hE1, hE2, hguess, hx1, hx2⟩) best
    · exact pres_foldP _ _ _ (fun b a hb => pres_tick_bind _ (pres_foldP _ _ _
        (fun b K hb => pres_tick_bind _ (cand_fold_pres I ϵ lp rnd _ _ (hInvP _) _ b hb)) b hb)) _ hv₀
    · obtain ⟨hb1, hb2⟩ := hb
      show (1 - ε) * OPT I ≤ V I best.1
      rw [← hb1]
      nlinarith

end main

/-! ## Cost -/

lemma costOK_foldP_mem {α β : Type} (l : List α) (f : β → α → Prog β) (S c : ℕ)
    (hf : ∀ b a, a ∈ l → CostOK (f b a) S c) : ∀ b, CostOK (foldP l f b) S (l.length * (c + 1)) := by
  induction l with
  | nil => intro b; simpa [foldP] using costOK_pure b S
  | cons a l ih =>
    intro b
    simp only [foldP]
    refine costOK_mono (costOK_bind (costOK_tick 1 S) fun _ =>
      costOK_bind (hf b a (by simp)) fun b' => ih (fun b a' ha => hf b a' (by simp [ha])) b') ?_
    simp [List.length_cons]; ring_nf; omega

lemma costOK_foldProd_mem {α β : Type} (cs : List (List α)) :
    ∀ (f : β → List α → Prog β) (S c : ℕ),
      (∀ b r, (∀ x ∈ r, ∃ l ∈ cs, x ∈ l) → CostOK (f b r) S c) →
      ∀ b, CostOK (foldProd cs f b) S ((cs.map fun l => 2 * (l.length + 1)).prod * (c + 1)) := by
  induction cs with
  | nil => intro f S c hf b; simpa [foldProd] using costOK_mono (hf b [] (by simp)) (by omega)
  | cons l cs ih =>
    intro f S c hf b
    simp only [foldProd]
    refine costOK_mono (costOK_foldP_mem l _ S _ (fun b a ha => ih (fun b' r => f b' (a :: r)) S c
      (fun b r hr => hf b _ (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨l, by simp, ha⟩
        · obtain ⟨l', hl', hx'⟩ := hr x hx; exact ⟨l', by simp [hl'], hx'⟩)) b) b) ?_
    simp only [List.map_cons, List.prod_cons]
    have hpos : 0 < (cs.map fun l => 2 * (l.length + 1)).prod := by
      apply List.prod_pos; intro x hx; simp at hx; obtain ⟨a, -, rfl⟩ := hx; omega
    have h1 : 1 ≤ (cs.map fun l => 2 * (l.length + 1)).prod * (c + 1) := by
      have := Nat.mul_le_mul hpos (Nat.succ_le_succ (Nat.zero_le c)); simpa using this
    generalize (cs.map fun l => 2 * (l.length + 1)).prod = Q at h1 ⊢
    rw [mul_assoc]
    generalize Q * (c + 1) = P at h1 ⊢
    nlinarith

lemma grid_nonneg {ϵ E : ℝ} (hE : 0 ≤ E) (G : ℕ) : ∀ x ∈ guessGrid ϵ E G, 0 ≤ x := by
  intro x hx
  unfold guessGrid at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  have hk0 : 0 ≤ k := by
    simp at hk
    obtain ⟨a, -, rfl⟩ := hk
    exact Nat.cast_nonneg _
  exact mul_nonneg hk0 (mul_nonneg (sq_nonneg _) hE)

lemma getD_nonneg (g : List ℝ) (h : ∀ x ∈ g, 0 ≤ x) (i : ℕ) : 0 ≤ g.getD i 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hh : g[i]? with
  | none => simp
  | some x => simpa using h x (List.mem_of_getElem? hh)

noncomputable def Gf (q : ℕ) : ℕ := ⌈1 / ((1 / (q : ℝ)) ^ 2 * (1 - 1 / (q : ℝ)))⌉₊
noncomputable def KMf (q : ℕ) : ℕ := ⌈Real.log 2 / Real.log (1 + 1 / (q : ℝ))⌉₊
def Cc (tc : ℕ → ℕ) (q : ℕ) : ℕ := 5 * (2 * q + 1) + 5 * (2 * q + 2) + tc q + 4
noncomputable def Ff (tc : ℕ → ℕ) (q : ℕ) : ℕ := (2 * (Gf q + 2)) ^ (2 * (2 * q + 1)) * (Cc tc q + 1)
noncomputable def Hf (tc : ℕ → ℕ) (q : ℕ) : ℕ := (q + 1) * (3 * (Gf q + 2) + Ff tc q + 1)
noncomputable def Tf (tc : ℕ → ℕ) (q : ℕ) : ℕ := 20 + (KMf q + 1) * (KMf q + 3 + Hf tc q) + tc q

lemma q_two (ε : ℝ) (hε : 0 < ε) : 2 ≤ ⌈14 / min ε 1⌉₊ := by
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have hqr : 14 / min ε 1 ≤ (⌈14 / min ε 1⌉₊ : ℝ) := Nat.le_ceil _
  have hq14r : (14 : ℝ) ≤ 14 / min ε 1 := by
    rw [le_div_iff₀ hmin]; nlinarith [min_le_right ε 1]
  exact_mod_cast (show (2 : ℝ) ≤ ⌈14 / min ε 1⌉₊ by linarith)

lemma q_le (ε : ℝ) (hε : 0 < ε) : ⌈14 / min ε 1⌉₊ < 14 * ⌈1 / ε⌉₊ + 15 := by
  have : ⌈14 / min ε 1⌉₊ ≤ 14 * ⌈1 / ε⌉₊ + 14 := by
    rw [Nat.ceil_le]; push_cast
    have hc := Nat.le_ceil (1 / ε)
    rcases le_total ε 1 with h | h
    · rw [min_eq_left h, div_eq_mul_one_div 14 ε]; nlinarith
    · rw [min_eq_right h]; have : (0 : ℝ) ≤ ⌈1 / ε⌉₊ := Nat.cast_nonneg _
      linarith
  omega

section maincost
variable {tc : ℕ → ℕ} {dc : ℕ} (hcor : CorStmt tc dc)
include hcor

lemma cand_cost' {q : ℕ} (hq : 2 ≤ q) {m n : ℕ} (hm : m ≤ 2 * q + 1) (I : Instance n)
    (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd)
    (best : Equiv.Perm (Fin n) × ℝ) (g : List ℝ) (hg : ∀ x ∈ g, 0 ≤ x) :
    CostOK (candidate (1 / (q : ℝ)) (orc I) lp rnd m best g) (tc q * (n + 1))
      (Cc tc q * (n + 1) ^ (dc + 2)) := by
  refine costOK_mono (cand_cost hcor hq hm I lp rnd hlp hrnd best g
    (fun i => getD_nonneg g hg _)) ?_
  have hN : 1 ≤ n + 1 := by omega
  have hNP : n + 1 ≤ (n + 1) ^ (dc + 2) :=
    le_trans (le_of_eq (pow_one _).symm) (Nat.pow_le_pow_right hN (by omega))
  have hN2 : (n + 1) * (n + 1) ≤ (n + 1) ^ (dc + 2) := by
    rw [← pow_two]; exact Nat.pow_le_pow_right hN (by omega)
  have hNd : (n + 1) ^ dc ≤ (n + 1) ^ (dc + 2) := Nat.pow_le_pow_right hN (by omega)
  have a1 : m * (n + 1) ≤ (2 * q + 1) * (n + 1) ^ (dc + 2) := Nat.mul_le_mul hm hNP
  have a2 : tc q * (n + 1) ^ dc ≤ tc q * (n + 1) ^ (dc + 2) := Nat.mul_le_mul_left _ hNd
  have a3 : q * (n + 1) ≤ q * (n + 1) ^ (dc + 2) := Nat.mul_le_mul_left _ hNP
  unfold Cc
  nlinarith

lemma prod_cost {q : ℕ} (hq : 2 ≤ q) {K n : ℕ} (hK : K ≤ q) (I : Instance n)
    (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd)
    (E : ℝ) (hE : 0 ≤ E) (best : Equiv.Perm (Fin n) × ℝ) :
    CostOK (foldProd (List.replicate (2 * (2 * K + 1)) (guessGrid (1 / (q : ℝ)) E (Gf q)))
      (candidate (1 / (q : ℝ)) (orc I) lp rnd (2 * K + 1)) best) (tc q * (n + 1))
      (Ff tc q * (n + 1) ^ (dc + 2)) := by
  refine costOK_mono (costOK_foldProd_mem _ _ _ _ (fun b r hr => cand_cost' hcor hq
    (by omega) I lp rnd hlp hrnd b r (fun x hx => by
      obtain ⟨l, hl, hxl⟩ := hr x hx
      rw [List.eq_of_mem_replicate hl] at hxl
      exact grid_nonneg hE _ x hxl)) best) ?_
  have hlen : (guessGrid (1 / (q : ℝ)) E (Gf q)).length = Gf q + 1 := by simp [guessGrid]
  simp only [List.map_replicate, List.prod_replicate, hlen]
  have hP : 1 ≤ (n + 1) ^ (dc + 2) := Nat.one_le_pow _ _ (by omega)
  have hpow : (2 * (Gf q + 1 + 1)) ^ (2 * (2 * K + 1)) ≤ (2 * (Gf q + 2)) ^ (2 * (2 * q + 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hc : Cc tc q * (n + 1) ^ (dc + 2) + 1 ≤ (Cc tc q + 1) * (n + 1) ^ (dc + 2) := by nlinarith
  unfold Ff
  calc _ ≤ (2 * (Gf q + 2)) ^ (2 * (2 * q + 1)) * ((Cc tc q + 1) * (n + 1) ^ (dc + 2)) :=
        Nat.mul_le_mul hpow hc
    _ = _ := by ring

lemma main_cost (ε : ℝ) (hε : 0 < ε) {n : ℕ} (I : Instance n) (lp : LPSolver) (rnd : Rounding)
    (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd) :
    CostOK (freeOrder ε (orc I) lp rnd) (tc ⌈14 / min ε 1⌉₊ * (n + 1))
      (Tf tc ⌈14 / min ε 1⌉₊ * (n + 1) ^ (dc + 2)) := by
  have hq2 := q_two ε hε
  unfold freeOrder
  simp only [opn_bind]
  generalize ⌈14 / min ε 1⌉₊ = q at hq2 ⊢
  have hP : 1 ≤ (n + 1) ^ (dc + 2) := Nat.one_le_pow _ _ (by omega)
  have hnP : n ≤ (n + 1) ^ (dc + 2) :=
    le_trans (by omega) (le_trans (le_of_eq (pow_one _).symm) (Nat.pow_le_pow_right (by omega) (by omega)))
  set P := (n + 1) ^ (dc + 2)
  refine costOK_mono (k := 3 + (1 + (3 * n + (1 + (5 + (6 + ((KMf q + 1) *
    ((KMf q + 2 + Hf tc q * P) + 1) + 0))))))) ?_ ?_
  · refine costOK_bind (costOK_tick 3 _) fun _ => costOK_bind (costOK_tick 1 _) fun _ =>
      costOK_bind' (recursion_cost I 1 _) (recursion_val I 1) fun v₀ hv₀ =>
      costOK_bind (costOK_tick 1 _) fun _ => ?_
    by_cases hv : v₀ ≤ 0
    · rw [if_pos (by simpa using hv)]; exact costOK_mono (costOK_pure _ _) (Nat.zero_le _)
    · rw [if_neg (by simpa using hv)]
      push Not at hv
      refine costOK_bind (costOK_tick 5 _) fun _ => costOK_bind (costOK_tick 6 _) fun _ =>
        costOK_bind ?_ fun best => costOK_pure _ _
      refine costOK_mono (costOK_foldP_mem _ _ _ (KMf q + 2 + Hf tc q * P) (fun b k hk => ?_) _)
        (by rw [List.length_range]; rfl)
      have hk' : k ≤ KMf q := by have := List.mem_range.1 hk; unfold KMf; omega
      refine costOK_mono (costOK_bind (k2 := Hf tc q * P) (costOK_tick (k + 2) _) fun _ => ?_)
        (by omega)
      have hE : 0 ≤ v₀ * (1 + 1 / (q : ℝ)) ^ k := by positivity
      refine costOK_mono (costOK_foldP_mem _ _ _ (3 * (Gf q + 2) + Ff tc q * P)
        (fun b K hK => costOK_bind (costOK_tick _ _) fun _ =>
          prod_cost hcor hq2 (by have := List.mem_range.1 hK; omega) I lp rnd hlp hrnd _ hE b) _) ?_
      simp only [List.length_range]
      unfold Hf
      have : 3 * (Gf q + 2) + Ff tc q * P + 1 ≤ (3 * (Gf q + 2) + Ff tc q + 1) * P := by nlinarith
      calc _ ≤ (q + 1) * ((3 * (Gf q + 2) + Ff tc q + 1) * P) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
  · unfold Tf
    have h1 : (KMf q + 1) * (KMf q + 2 + Hf tc q * P + 1) ≤ (KMf q + 1) * (KMf q + 3 + Hf tc q) * P := by
      rw [mul_assoc]; apply Nat.mul_le_mul_left; nlinarith
    nlinarith

end maincost

end FOS31

open FreeOrderEPTAS FOS31 in
theorem solution :
    ∃ (t : ℕ → ℕ) (d : ℕ), ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (I : Instance n) (lp : LPSolver)
      (rnd : Rounding), IsLPSolver lp → IsDependentRounding rnd →
      (1 / 2 : ℝ) ≤ pr ((freeOrder ε (orc I) lp rnd).run 0) {r | (1 - ε) * OPT I ≤ V I r.1} ∧
      ∀ r ∈ ((freeOrder ε (orc I) lp rnd).run 0).support,
        r.2.total ≤ t ⌈1 / ε⌉₊ * (n + 1) ^ d ∧ r.2.maxSize ≤ t ⌈1 / ε⌉₊ * (n + 1) := by
  obtain ⟨tc, dc, hcor⟩ := cor_exists
  refine ⟨fun c => ∑ q ∈ Finset.range (14 * c + 15), Tf tc q, dc + 2, ?_⟩
  intro ε hε n I lp rnd hlp hrnd
  have hT : Tf tc ⌈14 / min ε 1⌉₊ ≤ ∑ q ∈ Finset.range (14 * ⌈1 / ε⌉₊ + 15), Tf tc q :=
    Finset.single_le_sum (f := Tf tc) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (q_le ε hε))
  have htc : tc ⌈14 / min ε 1⌉₊ ≤ Tf tc ⌈14 / min ε 1⌉₊ := by unfold Tf; omega
  refine ⟨?_, fun r hr => ?_⟩
  · have h := main_prob hcor ε hε I lp rnd hlp hrnd 0
    unfold pr
    have := ENNReal.toReal_mono (tom_ne_top _ _) h
    rwa [ENNReal.toReal_ofReal (by norm_num)] at this
  · obtain ⟨h1, h2⟩ := main_cost hcor ε hε I lp rnd hlp hrnd 0 (by simp) r hr
    have h0 : (0 : Cost).total = 0 := rfl
    rw [h0, zero_add] at h1
    exact ⟨h1.trans (Nat.mul_le_mul_right _ hT), h2.trans (Nat.mul_le_mul_right _ (htc.trans hT))⟩
