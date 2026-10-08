-- Prove2me | solution 1 for FibHeap.Amort.rank_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:02:29.464955+00:00
-- url     : https://prove2.me/submissions/e4f97bd8-7df0-4033-9fc4-834ad38b9a8e

import Mathlib
import Definitions.Def_FibHeap_Amort_Model



namespace FibHeap.Amort
open FTree

def hpot (r : Heap) : ℕ := r.length + 2 * markedNonroot r

theorem potential_eq (s : Coll) : potential s = (s.map hpot).sum := rfl

theorem pot_set (s : Coll) (h : ℕ) (r r' : Heap) (hs : s[h]? = some r) :
    potential (s.set h r') + hpot r = potential s + hpot r' := by
  induction s generalizing h with
  | nil => simp at hs
  | cons a s ih =>
    cases h with
    | zero =>
      simp at hs; subst hs
      simp [potential_eq]; ring
    | succ h =>
      simp at hs
      have := ih h hs
      simp only [potential_eq, List.set_cons_succ, List.map_cons, List.sum_cons] at this ⊢
      omega

theorem hpot_append (r r' : Heap) : hpot (r ++ r') = hpot r + hpot r' := by
  simp [hpot, markedNonroot, List.map_append, List.sum_append]; ring

/-- sum of children marked counts -/
def Pc (t : FTree) : ℕ := (t.children.map markedCount).sum
def rho (t : FTree) : ℕ := 1 + 2 * Pc t

theorem mc_eq (t : FTree) : markedCount t = (if t.marked then 1 else 0) + Pc t := by
  cases t; simp only [markedCount, Pc, FTree.marked, FTree.children]
  rfl

theorem mc_setMarked_true (t : FTree) (h : t.marked = false) :
    markedCount (t.setMarked true) = markedCount t + 1 := by
  cases t; simp [markedCount, FTree.setMarked, FTree.marked] at *; subst h; simp; ring

theorem Pc_setKey (t : FTree) (k : ℝ) : Pc (t.setKey k) = Pc t := by
  cases t; simp [Pc, FTree.setKey, FTree.children]

theorem mc_setKey (t : FTree) (k : ℝ) : markedCount (t.setKey k) = markedCount t := by
  cases t; simp [markedCount, FTree.setKey]

theorem cut_marked {i : ℕ} {f : FTree → List FTree} {t t' : FTree} {R : List FTree} {n : ℕ}
    {lost : Bool} (h : CutAt i f t t' R n lost) : t'.marked = t.marked := by
  cases h <;> rfl

theorem cut_bound {i : ℕ} {f : FTree → List FTree} {t t' : FTree} {R : List FTree} {n : ℕ}
    {lost : Bool} (h : CutAt i f t t' R n lost)
    (hf : ∀ c, ((f c).map rho).sum ≤ 2 * markedCount c + 1) :
    (lost = true → 2 * markedCount t' + (R.map rho).sum + n ≤ 2 * markedCount t + 1) ∧
    (lost = false → 2 * markedCount t' + (R.map rho).sum + n ≤ 2 * markedCount t + 3) := by
  induction h with
  | direct hc =>
    rename_i it k m pre post c
    have := hf c
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    refine ⟨fun _ => by omega, by simp⟩
  | markParent hc hm ih =>
    rename_i it k m pre post c c' R n
    have ih1 := ih.1 rfl
    have hm' := cut_marked hc
    have := mc_setMarked_true c' (by rw [hm', hm])
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    refine ⟨by simp, fun _ => by omega⟩
  | cascade hc hm ih =>
    rename_i it k m pre post c c' R n
    have ih1 := ih.1 rfl
    have hm' := cut_marked hc
    have e1 := mc_eq c'
    have e2 := mc_eq c
    have e3 : rho c' + 1 = 2 * markedCount c' := by
      rw [e1, hm', hm]; simp [rho]; ring
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    refine ⟨fun _ => by omega, by simp⟩
  | pass hc ih =>
    rename_i it k m pre post c c' R n
    have ih1 := ih.2 rfl
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    refine ⟨by simp, fun _ => by omega⟩

theorem hpot_eq (r : Heap) : hpot r = (r.map rho).sum := by
  induction r with
  | nil => simp [hpot, markedNonroot]
  | cons a r ih =>
    simp only [hpot, markedNonroot, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    simp only [rho, Pc] at *
    omega


theorem fibphi_core (k : ℕ) :
    Real.goldenRatio ^ k ≤ (Nat.fib (k + 2) : ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 =>
      have := Real.goldenRatio_lt_two
      simp [Nat.fib_add_two]
      linarith
    | k + 2 =>
      have h1 := ih k (by omega)
      have h2 := ih (k+1) (by omega)
      have e : Nat.fib (k + 2 + 2) = Nat.fib (k+2) + Nat.fib (k+1+2) := by
        rw [show k + 2 + 2 = (k+2) + 2 from rfl, Nat.fib_add_two]
      rw [e]; push_cast
      have : Real.goldenRatio ^ (k+2) = Real.goldenRatio ^ k + Real.goldenRatio ^ (k+1) := by
        have := Real.goldenRatio_sq
        calc Real.goldenRatio ^ (k+2)
            = Real.goldenRatio ^ k * (Real.goldenRatio^2) := by ring
          _ = _ := by rw [this]; ring
      linarith



/-! ## Invariant -/

def Chain : ℕ → List FTree → Prop
  | _, [] => True
  | n, c :: cs => n ≤ c.rank + (if c.marked then 1 else 0) ∧ Chain (n+1) cs

theorem Chain_append (l1 l2 : List FTree) (n : ℕ) :
    Chain n (l1 ++ l2) ↔ Chain n l1 ∧ Chain (n + l1.length) l2 := by
  induction l1 generalizing n with
  | nil => simp [Chain]
  | cons a l ih =>
    simp only [List.cons_append, Chain, ih, List.length_cons]
    have : n + 1 + l.length = n + (l.length + 1) := by omega
    rw [this]; tauto

theorem Chain_mono (l : List FTree) : ∀ (m n : ℕ), Chain m l → n ≤ m → Chain n l := by
  induction l with
  | nil => intros; trivial
  | cons a l ih =>
    intro m n h hn
    exact ⟨le_trans hn h.1, ih (m+1) (n+1) h.2 (by omega)⟩

def Inv (t : FTree) : Prop := ∀ x ∈ t.subtrees, Chain 0 x.children

theorem Inv_node (i : ℕ) (k : ℝ) (m : Bool) (cs : List FTree) :
    Inv (.node i k m cs) ↔ Chain 0 cs ∧ ∀ c ∈ cs, Inv c := by
  unfold Inv
  simp only [FTree.subtrees, List.mem_cons, List.mem_flatMap]
  constructor
  · intro h
    refine ⟨h _ (Or.inl rfl), fun c hc x hx => h x (Or.inr ⟨c, hc, hx⟩)⟩
  · rintro ⟨h1, h2⟩ x (rfl | ⟨c, hc, hx⟩)
    · exact h1
    · exact h2 c hc x hx

theorem Inv_children (t : FTree) (h : Inv t) : Chain 0 t.children ∧ ∀ c ∈ t.children, Inv c := by
  cases t; exact (Inv_node _ _ _ _).1 h

theorem Inv_setMarked (t : FTree) (b : Bool) : Inv (t.setMarked b) ↔ Inv t := by
  cases t; simp [FTree.setMarked, Inv_node]

theorem Inv_setKey (t : FTree) (k : ℝ) : Inv (t.setKey k) ↔ Inv t := by
  cases t; simp [FTree.setKey, Inv_node]

theorem Inv_link (a b : FTree) (ha : Inv a) (hb : Inv b) (hr : a.rank = b.rank) :
    Inv (link a b) := by
  have h1 := Inv_children a ha
  have h2 := Inv_children b hb
  have key : ∀ x y : FTree, Inv x → Inv y → x.rank = y.rank →
      Inv (FTree.node x.item x.key x.marked (x.children ++ [y.setMarked false])) := by
    intro x y hx hy hxy
    have h1 := Inv_children x hx
    rw [Inv_node, Chain_append]
    refine ⟨⟨h1.1, ?_⟩, ?_⟩
    · simp only [Chain, FTree.rank] at *
      have : (y.setMarked false).marked = false := by cases y; rfl
      have h3 : (y.setMarked false).rank = y.rank := by cases y; rfl
      simp [this, h3, FTree.rank] at *
      omega
    · intro c hc
      simp at hc
      rcases hc with hc | rfl
      · exact h1.2 c hc
      · rw [Inv_setMarked]; exact hy
  unfold link
  split_ifs
  · exact key a b ha hb hr
  · exact key b a hb ha hr.symm


theorem mc_setMarked_false (t : FTree) : markedCount (t.setMarked false) = Pc t := by
  cases t; simp [markedCount, Pc, FTree.setMarked, FTree.children]

theorem rho_link (a b : FTree) : rho (link a b) + 1 = rho a + rho b := by
  unfold link
  split_ifs
  · simp [rho, Pc, FTree.children, List.map_append, mc_setMarked_false]
    try ring
  · simp [rho, Pc, FTree.children, List.map_append, mc_setMarked_false]
    try ring

theorem cons_inv {rs rs' : Heap} {n : ℕ} (h : Consolidate rs rs' n) :
    (∀ τ ∈ rs, Inv τ) → (∀ τ ∈ rs', Inv τ) ∧ (rs'.map rho).sum + n = (rs.map rho).sum := by
  induction h with
  | done _ => intro h; exact ⟨h, by simp⟩
  | step hp hr hc ih =>
    rename_i rs rest rs' a b n
    intro hinv
    have hs := hp.subset
    have ha : Inv a := hinv a (hp.symm.subset (by simp))
    have hb : Inv b := hinv b (hp.symm.subset (by simp))
    have hl : ∀ τ ∈ link a b :: rest, Inv τ := by
      intro τ hτ
      rcases List.mem_cons.1 hτ with rfl | hτ
      · exact Inv_link a b ha hb hr
      · exact hinv τ (hp.symm.subset (by simp [hτ]))
    obtain ⟨h1, h2⟩ := ih hl
    refine ⟨h1, ?_⟩
    have := (hp.map rho).sum_eq
    have e := rho_link a b
    simp only [List.map_cons, List.sum_cons] at this h2
    omega

theorem cut_rank {i : ℕ} {f : FTree → List FTree} {t t' : FTree} {R : List FTree} {n : ℕ}
    {lost : Bool} (h : CutAt i f t t' R n lost) :
    (lost = true → t'.rank + 1 = t.rank) ∧ (lost = false → t'.rank = t.rank) := by
  cases h <;> simp [FTree.rank, FTree.children] <;> omega

theorem cut_inv {i : ℕ} {f : FTree → List FTree} {t t' : FTree} {R : List FTree} {n : ℕ}
    {lost : Bool} (h : CutAt i f t t' R n lost)
    (hf : ∀ c, Inv c → ∀ r ∈ f c, Inv r) :
    Inv t → Inv t' ∧ ∀ r ∈ R, Inv r := by
  induction h with
  | direct hc =>
    rename_i it k m pre post c
    intro ht
    rw [Inv_node] at ht ⊢
    obtain ⟨h1, h2⟩ := ht
    rw [Chain_append] at h1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Chain_append]
      refine ⟨h1.1, Chain_mono _ _ _ h1.2.2 (by omega)⟩
    · intro c' hc'
      exact h2 c' (by simp at hc' ⊢; tauto)
    · exact hf c (h2 c (by simp))
  | markParent hc hm ih =>
    rename_i it k m pre post c c' R n
    intro ht
    rw [Inv_node] at ht ⊢
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨ih1, ih2⟩ := ih (h2 c (by simp))
    refine ⟨⟨?_, ?_⟩, ih2⟩
    · rw [Chain_append] at h1 ⊢
      refine ⟨h1.1, ?_⟩
      have h3 := h1.2.1
      simp only [Chain] at h3 ⊢
      refine ⟨?_, h1.2.2⟩
      have r := (cut_rank hc).1 rfl
      have : (c'.setMarked true).marked = true := by cases c'; rfl
      have h4 : (c'.setMarked true).rank = c'.rank := by cases c'; rfl
      rw [this, h4]
      simp [hm] at h3
      simp; omega
    · intro c1 hc1
      simp only [List.mem_append, List.mem_cons] at hc1
      rcases hc1 with h5 | rfl | h5
      · exact h2 c1 (by simp [h5])
      · rw [Inv_setMarked]; exact ih1
      · exact h2 c1 (by simp [h5])
  | cascade hc hm ih =>
    rename_i it k m pre post c c' R n
    intro ht
    rw [Inv_node] at ht ⊢
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨ih1, ih2⟩ := ih (h2 c (by simp))
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Chain_append] at h1 ⊢
      refine ⟨h1.1, Chain_mono _ _ _ h1.2.2 (by omega)⟩
    · intro c1 hc1
      exact h2 c1 (by simp at hc1 ⊢; tauto)
    · intro r hr
      simp at hr
      rcases hr with hr | rfl
      · exact ih2 r hr
      · exact ih1
  | pass hc ih =>
    rename_i it k m pre post c c' R n
    intro ht
    rw [Inv_node] at ht ⊢
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨ih1, ih2⟩ := ih (h2 c (by simp))
    refine ⟨⟨?_, ?_⟩, ih2⟩
    · rw [Chain_append] at h1 ⊢
      refine ⟨h1.1, ?_⟩
      have h3 := h1.2.1
      simp only [Chain] at h3 ⊢
      refine ⟨?_, h1.2.2⟩
      have r := (cut_rank hc).2 rfl
      have mk := cut_marked hc
      rw [r, mk]; exact h3
    · intro c1 hc1
      simp only [List.mem_append, List.mem_cons] at hc1
      rcases hc1 with h5 | rfl | h5
      · exact h2 c1 (by simp [h5])
      · exact ih1
      · exact h2 c1 (by simp [h5])


def Pl (l : List FTree) : Prop := ∀ τ ∈ l, Inv τ

theorem Pl_append (a b : List FTree) : Pl (a ++ b) ↔ Pl a ∧ Pl b := by
  simp [Pl, or_imp, forall_and]

theorem Pl_cons (a : FTree) (b : List FTree) : Pl (a :: b) ↔ Inv a ∧ Pl b := by
  simp [Pl]

theorem Pl_nil : Pl [] := by simp [Pl]

def AllInv (s : Coll) : Prop := ∀ r ∈ s, Pl r

theorem AllInv_set {s : Coll} (h : ℕ) {r' : Heap} (hs : AllInv s) (hr : Pl r') :
    AllInv (s.set h r') := by
  intro r hr0
  rcases List.mem_or_eq_of_mem_set hr0 with h1 | rfl
  · exact hs r h1
  · exact hr

theorem AllInv_get {s : Coll} {h : ℕ} {r : Heap} (hs : AllInv s) (hg : s[h]? = some r) : Pl r :=
  hs r (List.mem_of_getElem? hg)

theorem Pl_children (x : FTree) (hx : Inv x) : Pl x.children := (Inv_children x hx).2

theorem step_inv {s s' : Coll} {op : Op} {d : StepData} (hstep : Step s op s' d)
    (hs : AllInv s) : AllInv s' := by
  cases hstep
  case makeHeap =>
    intro r hr
    simp at hr
    rcases hr with hr | rfl
    · exact hs r hr
    · exact Pl_nil
  case findMin => exact hs
  case insert r i k h hg _ =>
    apply AllInv_set h hs
    rw [Pl_append, Pl_cons]
    refine ⟨AllInv_get hs hg, ?_, Pl_nil⟩
    rw [Inv_node]; simp [Chain]
  case meld r1 r2 h1 h2 hg1 hg2 _ =>
    apply AllInv_set h2 (AllInv_set h1 hs _) Pl_nil
    rw [Pl_append]; exact ⟨AllInv_get hs hg1, AllInv_get hs hg2⟩
  case deleteMin h pre post r' x L hg _ hc =>
    apply AllInv_set h hs
    have hp := AllInv_get hs hg
    rw [Pl_append, Pl_cons] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    exact (cons_inv hc (by
      rw [← Pl]; rw [Pl_append, Pl_append]; exact ⟨⟨h1, h3⟩, Pl_children x h2⟩)).1
  case decreaseKeyRoot h pre post x Δ i _ hg _ =>
    apply AllInv_set h hs
    have hp := AllInv_get hs hg
    rw [Pl_append, Pl_cons] at hp
    rw [Pl_append, Pl_cons]
    exact ⟨hp.1, (Inv_setKey _ _).2 hp.2.1, hp.2.2⟩
  case decreaseKeyCut h pre post τ τ' R n lost Δ i _ hg _ hcut =>
    apply AllInv_set h hs
    have hp := AllInv_get hs hg
    rw [Pl_append, Pl_cons] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    obtain ⟨a, b⟩ := cut_inv hcut (fun c hc r hr => by
      simp at hr; subst hr; exact (Inv_setKey _ _).2 hc) h2
    rw [Pl_append, Pl_append, Pl_cons]
    exact ⟨⟨h1, a, h3⟩, b⟩
  case deleteMinRoot h pre post r' x L i hg _ _ hc =>
    apply AllInv_set h hs
    have hp := AllInv_get hs hg
    rw [Pl_append, Pl_cons] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    exact (cons_inv hc (by
      rw [← Pl]; rw [Pl_append, Pl_append]; exact ⟨⟨h1, h3⟩, Pl_children x h2⟩)).1
  case deleteOtherRoot h pre post x i hg _ _ =>
    apply AllInv_set h hs
    have hp := AllInv_get hs hg
    rw [Pl_append, Pl_cons] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [Pl_append, Pl_append]; exact ⟨⟨h1, h3⟩, Pl_children x h2⟩
  case deleteCut h pre post τ τ' R n lost i hg _ hcut =>
    apply AllInv_set h hs
    have hp := AllInv_get hs hg
    rw [Pl_append, Pl_cons] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    obtain ⟨a, b⟩ := cut_inv hcut (fun c hc r hr => (Inv_children c hc).2 r hr) h2
    rw [Pl_append, Pl_append, Pl_cons]
    exact ⟨⟨h1, a, h3⟩, b⟩

theorem run_inv {T : ℕ} {s : ℕ → Coll} {op : ℕ → Op} {d : ℕ → StepData}
    (hrun : IsRun T s op d) : ∀ t ≤ T, AllInv (s t) := by
  intro t
  induction t with
  | zero => intro _; rw [hrun.1]; intro r hr; simp at hr
  | succ t ih =>
    intro ht
    exact step_inv (hrun.2 t (by omega)) (ih (by omega))

theorem reach_inv {c : Coll} (hc : Reachable c) : AllInv c := by
  obtain ⟨T, s, op, d, hrun, rfl⟩ := hc
  exact run_inv hrun T le_rfl


theorem chain_sum (cs : List FTree) : ∀ n : ℕ, Chain n cs →
    (∀ c ∈ cs, Nat.fib (c.rank + 2) ≤ c.size) →
    Nat.fib (n + cs.length + 2) ≤ (cs.map FTree.size).sum + Nat.fib (n + 2) := by
  induction cs with
  | nil => intro n _ _; simp
  | cons c cs ih =>
    intro n hc hs
    have h1 := hc.1
    have h2 := ih (n+1) hc.2 (fun c' hc' => hs c' (by simp [hc']))
    have h3 := hs c (by simp)
    have h4 : Nat.fib (n + 1) ≤ Nat.fib (c.rank + 2) := Nat.fib_mono (by split_ifs at h1 <;> omega)
    have h5 : Nat.fib (n + 3) = Nat.fib (n+1) + Nat.fib (n+2) := by
      rw [show n + 3 = (n+1) + 2 from rfl, Nat.fib_add_two]
    have e : n + 1 + cs.length + 2 = n + (c :: cs).length + 2 := by simp only [List.length_cons]; omega
    have e2 : n + 1 + 2 = n + 3 := by omega
    rw [e, e2] at h2
    simp only [List.map_cons, List.sum_cons]
    omega

theorem fib_size : ∀ (N : ℕ) (t : FTree), t.size ≤ N → Inv t →
    Nat.fib (t.rank + 2) ≤ t.size := by
  intro N
  induction N with
  | zero =>
    intro t ht
    cases t; simp [FTree.size] at ht
  | succ N ih =>
    intro t ht hi
    obtain ⟨i, k, m, cs⟩ := t
    obtain ⟨h1, h2⟩ := (Inv_node _ _ _ _).1 hi
    have hsz : ∀ c ∈ cs, c.size ≤ N := by
      intro c hc
      have : c.size ≤ (cs.map FTree.size).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hc)
      simp only [FTree.size] at ht
      omega
    have := chain_sum cs 0 h1 (fun c hc => ih c (hsz c hc) (h2 c hc))
    simp only [FTree.rank, FTree.children, FTree.size] at *
    simp only [Nat.zero_add] at this
    have f2 : Nat.fib 2 = 1 := by decide
    rw [f2] at this
    omega

theorem subtree_prop : ∀ (N : ℕ) (t : FTree), t.size ≤ N →
    ∀ x ∈ t.subtrees, x.size ≤ t.size ∧ ∀ y ∈ x.subtrees, y ∈ t.subtrees := by
  intro N
  induction N with
  | zero => intro t ht; cases t; simp [FTree.size] at ht
  | succ N ih =>
    intro t ht x hx
    obtain ⟨i, k, m, cs⟩ := t
    simp only [FTree.subtrees, List.mem_cons, List.mem_flatMap] at hx
    rcases hx with rfl | ⟨c, hc, hxc⟩
    · exact ⟨le_rfl, fun y hy => hy⟩
    · have hcs : c.size ≤ (cs.map FTree.size).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hc)
      have hcN : c.size ≤ N := by simp only [FTree.size] at ht; omega
      obtain ⟨a, b⟩ := ih c hcN x hxc
      refine ⟨?_, fun y hy => ?_⟩
      · simp only [FTree.size]; omega
      · simp only [FTree.subtrees, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨c, hc, b y hy⟩

theorem Inv_sub {t x : FTree} (hi : Inv t) (hx : x ∈ t.subtrees) : Inv x := by
  intro y hy
  exact hi y ((subtree_prop _ t le_rfl x hx).2 y hy)

theorem corollary_core (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Nat.fib (x.rank + 2) ≤ x.size ∧
        Real.goldenRatio ^ x.rank ≤ (Nat.fib (x.rank + 2) : ℝ) := by
  intro r hr τ hτ x hx
  have hi := reach_inv hs r hr τ hτ
  have := fib_size _ x le_rfl (Inv_sub hi hx)
  exact ⟨this, fibphi_core _⟩

theorem rank_core (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Real.goldenRatio ^ x.rank ≤ (heapSize r : ℝ) ∧
        (x.rank : ℝ) ≤ Real.logb Real.goldenRatio (heapSize r) := by
  intro r hr τ hτ x hx
  obtain ⟨h1, h2⟩ := corollary_core s hs r hr τ hτ x hx
  have e1 : x.size ≤ τ.size := (subtree_prop _ τ le_rfl x hx).1
  have e2 : τ.size ≤ heapSize r := by
    unfold heapSize
    exact List.le_sum_of_mem (List.mem_map_of_mem hτ)
  have hle : Real.goldenRatio ^ x.rank ≤ (heapSize r : ℝ) := by
    calc Real.goldenRatio ^ x.rank ≤ (Nat.fib (x.rank + 2) : ℝ) := h2
      _ ≤ (x.size : ℝ) := by exact_mod_cast h1
      _ ≤ (heapSize r : ℝ) := by exact_mod_cast le_trans e1 e2
  refine ⟨hle, ?_⟩
  have hp : 0 < Real.goldenRatio ^ x.rank := by positivity
  have := Real.logb_le_logb_of_le Real.one_lt_goldenRatio hp hle
  rwa [Real.logb_pow, Real.logb_self_eq_one Real.one_lt_goldenRatio, mul_one] at this

end FibHeap.Amort

open FibHeap.Amort


theorem solution (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Real.goldenRatio ^ x.rank ≤ (heapSize r : ℝ) ∧
        (x.rank : ℝ) ≤ Real.logb Real.goldenRatio (heapSize r) := by
  exact rank_core s hs
