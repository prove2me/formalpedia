-- Prove2me | solution 1 for DetDLP.joint_terminal_edge_partition
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:55:02.561343+00:00
-- url     : https://prove2.me/submissions/6da9f8c1-d49d-4d5c-8c07-a1795e81cb4b

import Definitions.Def_DetDLP_BTN


namespace DetDLP.LocalLabelSearch
open Finset

/-- Each penalty depends on at most four vertex labels. -/
structure Term (n q : ℕ) where
  arity : ℕ
  small : arity ≤ 4
  vertex : Fin arity → Fin n
  distinct : Function.Injective vertex
  penalty : (Fin arity → Fin q) → ℕ

abbrev Partial (n q : ℕ) := Fin n → Option (Fin q)

def termScore {n q : ℕ} (t : Term n q) (s : Partial n q) : ℕ :=
  q^(4-t.arity) * ∑ z : Fin t.arity → Fin q,
    t.penalty (fun h => (s (t.vertex h)).getD (z h))

def score {n q : ℕ} (T : List (Term n q)) (s : Partial n q) : ℕ :=
  (T.map (termScore · s)).sum

private def swapAt {q r : ℕ} (h : Fin r) : (Fin q × (Fin r → Fin q)) ≃ (Fin q × (Fin r → Fin q)) where
  toFun x := (x.2 h, Function.update x.2 h x.1)
  invFun x := (x.2 h, Function.update x.2 h x.1)
  left_inv x := by simp
  right_inv x := by simp

private theorem term_average {n q : ℕ} (t : Term n q) (s : Partial n q)
    (v : Fin n) (fresh : s v = none) :
    ∑ x : Fin q, termScore t (Function.update s v (some x)) = q * termScore t s := by
  classical
  let f (z : Fin t.arity → Fin q) := t.penalty fun h => (s (t.vertex h)).getD (z h)
  by_cases hm : ∃ h, t.vertex h = v
  · obtain ⟨h,rfl⟩ := hm
    have he (x : Fin q) (z : Fin t.arity → Fin q) :
        t.penalty (fun a => (Function.update s (t.vertex h) (some x) (t.vertex a)).getD (z a)) =
        f (Function.update z h x) := by
      congr 1
      funext a
      by_cases ha : a = h
      · simp [ha,fresh]
      · simp [Function.update_of_ne ha,Function.update_of_ne (t.distinct.ne ha)]
    have hsum : ∑ x : Fin q, ∑ z : Fin t.arity → Fin q, f (Function.update z h x) =
        q * ∑ z : Fin t.arity → Fin q, f z := by
      let F (a : Fin q × (Fin t.arity → Fin q)) := f a.2
      calc
        _ = ∑ a : Fin q × (Fin t.arity → Fin q), F (swapAt h a) := Fintype.sum_prod_type _ |>.symm
        _ = ∑ a : Fin q × (Fin t.arity → Fin q), F a := (swapAt h).sum_comp F
        _ = _ := by rw [Fintype.sum_prod_type]; simp [F]
    unfold termScore
    simp_rw [he]
    rw [← mul_sum,hsum]
    dsimp only [f]
    ring
  · have he (x : Fin q) : termScore t (Function.update s v (some x)) = termScore t s := by
      unfold termScore
      congr 1
      apply sum_congr rfl
      intro z _
      congr 1; funext h
      rw [Function.update_of_ne (fun h' => hm ⟨h,h'⟩)]
    simp [he]

theorem score_average {n q : ℕ} (T : List (Term n q)) (s : Partial n q)
    (v : Fin n) (h : s v = none) :
    ∑ x : Fin q, score T (Function.update s v (some x)) = q * score T s := by
  induction T with
  | nil => simp [score]
  | cons t ts ih =>
    simp only [score,List.map_cons,List.sum_cons] at ih ⊢
    rw [sum_add_distrib,term_average t s v h,ih,Nat.mul_add]

private def better {q : ℕ} (f : Fin q → ℕ) (x y : Fin q) := if f y < f x then y else x

private theorem fold_min {q : ℕ} (f : Fin q → ℕ) (xs : List (Fin q)) (start : Fin q) :
    let z := xs.foldl (better f) start
    f z ≤ f start ∧ ∀ x ∈ xs, f z ≤ f x := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h0,h1⟩ := ih (better f start x)
    have hl : f (better f start x) ≤ f start ∧ f (better f start x) ≤ f x := by
      unfold better; split <;> omega
    exact ⟨h0.trans hl.1,fun y h => by
      rcases List.mem_cons.mp h with rfl|h
      · exact h0.trans hl.2
      · exact h1 y h⟩

def chooseLabel {n q : ℕ} [NeZero q] (T : List (Term n q)) (s : Partial n q) (v : Fin n) :=
  let cost (x : Fin q) := score T (Function.update s v (some x))
  (List.finRange q).foldl (better cost) 0

theorem chooseLabel_le {n q : ℕ} [NeZero q] (T : List (Term n q)) (s : Partial n q) (v : Fin n)
    (hf : s v = none) :
    score T (Function.update s v (some (chooseLabel T s v))) ≤ score T s := by
  let f (x : Fin q) := score T (Function.update s v (some x))
  let x := chooseLabel T s v
  have hl (y : Fin q) : f x ≤ f y :=
    (fold_min f (List.finRange q) 0).2 y (by simp)
  have hs : q*f x ≤ q*score T s := by
    rw [← score_average T s v hf,← show (∑ _ : Fin q, f x)=q*f x by simp]
    exact sum_le_sum (fun y _ => hl y)
  exact Nat.le_of_mul_le_mul_left hs (Nat.pos_of_ne_zero (NeZero.ne q))

def fixLabels {n q : ℕ} [NeZero q] (T : List (Term n q)) : ℕ → Partial n q
  | 0 => fun _ => none
  | k+1 =>
    let s := fixLabels T k
    if h : k < n then Function.update s ⟨k,h⟩ (some (chooseLabel T s ⟨k,h⟩)) else s

theorem fixLabels_spec {n q : ℕ} [NeZero q] (T : List (Term n q)) (k : ℕ) (hk : k ≤ n) :
    (∀ i : Fin n, (fixLabels T k i).isSome ↔ i.val < k) ∧
    score T (fixLabels T k) ≤ score T (fun _ => none) := by
  induction k with
  | zero => simp [fixLabels]
  | succ k ih =>
    have h : k < n := by omega
    obtain ⟨hset,hscore⟩ := ih (by omega)
    let v : Fin n := ⟨k,h⟩
    have hf : fixLabels T k v = none := by
      cases he : fixLabels T k v with
      | none => rfl
      | some x => have hh := (hset v).mp (by simp [he]); exact False.elim (lt_irrefl k hh)
    simp only [fixLabels,dif_pos h]
    refine ⟨fun i => ?_,(chooseLabel_le T _ v hf).trans hscore⟩
    by_cases he : i = v
    · subst i; simp [v]
    · rw [Function.update_of_ne he,hset]
      have hv : i.val ≠ k := fun e => he (Fin.ext e)
      omega

def labeling {n q : ℕ} [NeZero q] (T : List (Term n q)) : Fin n → Fin q :=
  fun v => (fixLabels T n v).getD 0

/-- The executable search attains at most the average score of all assignments;
each trial inspects at most q^4 local tuples per term. -/
theorem labeling_bound {n q : ℕ} [NeZero q] (T : List (Term n q)) :
    q^4 * (T.map (fun t => t.penalty (fun h => labeling T (t.vertex h)))).sum ≤
    score T (fun _ => none) := by
  obtain ⟨hfill,h⟩ := fixLabels_spec T n le_rfl
  have hs (v : Fin n) : fixLabels T n v = some (labeling T v) := by
    have hv := (hfill v).mpr v.isLt
    cases he : fixLabels T n v <;> simp_all [labeling]
  have ht (t : Term n q) : termScore t (fixLabels T n) = q^4 * t.penalty (fun h => labeling T (t.vertex h)) := by
    simp [termScore,hs,Fintype.card_fun,← mul_assoc,← pow_add, Nat.sub_add_cancel t.small]
  have sum_eq (ts : List (Term n q)) :
      score ts (fixLabels T n) = q^4*(ts.map (fun t => t.penalty (fun h => labeling T (t.vertex h)))).sum := by
    induction ts with
    | nil => simp [score]
    | cons t ts ih =>
      simp only [score,List.map_cons,List.sum_cons] at ih ⊢
      rw [ht,ih,Nat.mul_add]
  rw [sum_eq] at h
  exact h

end DetDLP.LocalLabelSearch

namespace DetDLP.EdgeLabelPartition
open Finset LocalLabelSearch

private def left (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
private def right (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2

private theorem left_side (G : BipartiteMultigraph) (e : Fin G.nE) : G.side (left G e) = false := by
  have h := G.bipartite e
  cases ha : G.side (G.endpoints e).1 <;> cases hb : G.side (G.endpoints e).2 <;> simp_all [left]
private theorem right_side (G : BipartiteMultigraph) (e : Fin G.nE) : G.side (right G e) = true := by
  have h := G.bipartite e
  cases ha : G.side (G.endpoints e).1 <;> cases hb : G.side (G.endpoints e).2 <;> simp_all [right]
private theorem lr_ne (G : BipartiteMultigraph) (e f : Fin G.nE) : left G e ≠ right G f := by
  intro h
  have he := left_side G e
  rw [h,right_side] at he
  contradiction

private def eqTwo {q : ℕ} (z : Fin 2 → Fin q) : ℕ := if z 0 = z 1 then 1 else 0
private def eqFour {q : ℕ} (z : Fin 4 → Fin q) : ℕ :=
  if z 0 = z 1 ∧ z 2 = z 3 then 1 else 0

private theorem sum_eqTwo (q : ℕ) : ∑ z : Fin 2 → Fin q, eqTwo z = q := by
  classical
  let e : {z : Fin 2 → Fin q // z 0 = z 1} ≃ Fin q :=
    { toFun z := z.1 0, invFun x := ⟨![x,x],rfl⟩
      left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> simp [z.property]
      right_inv _ := rfl }
  have hh := Fintype.card_congr e
  simpa [eqTwo,Fintype.card_subtype,Finset.sum_boole] using hh

private theorem sum_eqFour (q : ℕ) : ∑ z : Fin 4 → Fin q, eqFour z = q^2 := by
  classical
  let e : {z : Fin 4 → Fin q // z 0 = z 1 ∧ z 2 = z 3} ≃ Fin q × Fin q :=
    { toFun z := (z.1 0,z.1 2), invFun x := ⟨![x.1,x.1,x.2,x.2],rfl,rfl⟩
      left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> simp [z.property.1,z.property.2]
      right_inv _ := rfl }
  have hh := Fintype.card_congr e
  simpa [eqFour,Fintype.card_subtype,Finset.sum_boole,pow_two] using hh

private def constantTerm (n q : ℕ) : Term n q :=
  ⟨0,by decide,Fin.elim0,fun x => Fin.elim0 x,fun _ => 1⟩

private def pairTerm {n q : ℕ} (x y : Fin n) (h : x ≠ y) : Term n q :=
  ⟨2,by decide,![x,y],by intro i j; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm h],eqTwo⟩

private def fourTerm (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE)
    (hl : left G e ≠ left G f) (hr : right G e ≠ right G f) : Term G.nV q :=
  ⟨4,by decide,![left G e,left G f,right G e,right G f],by
      intro x y
      fin_cases x <;> fin_cases y <;> simp_all [lr_ne,Ne.symm hl,Ne.symm hr,Ne.symm (lr_ne G _ _)],eqFour⟩

private def edgeTerm (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE) : Term G.nV q :=
  if hl : left G e = left G f then
    if hr : right G e = right G f then constantTerm _ _ else pairTerm _ _ hr
  else if hr : right G e = right G f then pairTerm _ _ hl
  else fourTerm G q e f hl hr

private def pairCollision (G : BipartiteMultigraph) {q : ℕ} (e f : Fin G.nE) (L : Fin G.nV → Fin q) : ℕ :=
  if (L (left G e),L (right G e)) = (L (left G f),L (right G f)) then 1 else 0

private theorem cost_edge (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE)
    (L : Fin G.nV → Fin q) :
    (edgeTerm G q e f).penalty (fun i => L ((edgeTerm G q e f).vertex i)) =
    pairCollision G e f L := by
  by_cases hl : left G e = left G f
  · by_cases hr : right G e = right G f
    · have he : edgeTerm G q e f = constantTerm _ _ := by rw [edgeTerm,dif_pos hl,dif_pos hr]
      rw [he]; simp [constantTerm,pairCollision,hl,hr]
    · have he : edgeTerm G q e f = pairTerm _ _ hr := by rw [edgeTerm,dif_pos hl,dif_neg hr]
      rw [he]; simp [pairTerm,pairCollision,eqTwo,hl]
  · by_cases hr : right G e = right G f
    · have he : edgeTerm G q e f = pairTerm _ _ hl := by rw [edgeTerm,dif_neg hl,dif_pos hr]
      rw [he]; simp [pairTerm,pairCollision,eqTwo,hr]
    · have he : edgeTerm G q e f = fourTerm G q e f hl hr := by rw [edgeTerm,dif_neg hl,dif_neg hr]
      rw [he]; simp [fourTerm,pairCollision,eqFour,Prod.ext_iff]
      by_cases h : L (left G e) = L (left G f) <;> by_cases k : L (right G e) = L (right G f) <;> simp_all [h,k]

private theorem initial_edge (G : BipartiteMultigraph) (q : ℕ) [NeZero q] (e f : Fin G.nE) :
    termScore (edgeTerm G q e f) (fun _ => none) ≤
      q^2 + (if left G e = left G f ∨ right G e = right G f then q^4 else 0) := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hm : q^2*q ≤ q^4 := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right hq (by decide)
  have hs2 : (∑ z : Fin 2 → Fin q, eqTwo (fun h => z h)) = q := sum_eqTwo q
  have hs4 : (∑ z : Fin 4 → Fin q, eqFour (fun h => z h)) = q^2 := sum_eqFour q
  have hs0 : (∑ _ : Fin 0 → Fin q, 1 : ℕ) = 1 := by simp [Fintype.card_fun]
  have hc : termScore (constantTerm G.nV q) (fun _ => none) = q^4 := by
    change q^(4-0) * (∑ _ : Fin 0 → Fin q, 1 : ℕ) = q^4
    rw [hs0]; simp
  have hp (x y : Fin G.nV) (h : x ≠ y) : termScore (pairTerm (q := q) x y h) (fun _ => none) = q^2*q := by
    change q^2 * (∑ z : Fin 2 → Fin q, eqTwo z) = _
    rw [sum_eqTwo]
  by_cases hl : left G e = left G f
  · by_cases hr : right G e = right G f
    · rw [edgeTerm,dif_pos hl,dif_pos hr,hc,if_pos (Or.inl hl)]; omega
    · rw [edgeTerm,dif_pos hl,dif_neg hr,hp,if_pos (Or.inl hl)]; omega
  · by_cases hr : right G e = right G f
    · rw [edgeTerm,dif_neg hl,dif_pos hr,hp,if_pos (Or.inr hr)]; omega
    · rw [edgeTerm,dif_neg hl,dif_neg hr,if_neg (by tauto),add_zero]
      change q^(4-4) * (∑ z : Fin 4 → Fin q, eqFour z) ≤ _
      rw [sum_eqFour]; simp

private def edgePairs (G : BipartiteMultigraph) :=
  (List.finRange G.nE).flatMap fun e => (List.finRange G.nE).map fun f => (e,f)

private def terms (G : BipartiteMultigraph) (q : ℕ) :=
  (edgePairs G).map fun p => edgeTerm G q p.1 p.2

private theorem pair_sum {n : ℕ} (f : Fin n × Fin n → ℕ) :
    (((List.finRange n).flatMap fun e => (List.finRange n).map fun z => (e,z)).map f).sum =
    ∑ e, ∑ z, f (e,z) := by
  have hf (l : List (Fin n)) : (l.flatMap (fun a => (List.finRange n).map (fun z => f (a,z)))).sum =
      (l.map fun a => ((List.finRange n).map fun z => f (a,z)).sum).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simpa [List.map_flatMap,List.map_map,Function.comp_def,Fin.sum_univ_def] using hf (List.finRange n)

private theorem shared_subset (G : BipartiteMultigraph) (e f : Fin G.nE)
    (h : left G e = left G f ∨ right G e = right G f) :
    f ∈ G.ports (left G e) ∨ f ∈ G.ports (right G e) := by
  rcases h with hl|hr
  · left; rw [hl]; cases h : G.side (G.endpoints f).1 <;> simp [BipartiteMultigraph.ports,left,h]
  · right; rw [hr]; cases h : G.side (G.endpoints f).1 <;> simp [BipartiteMultigraph.ports,right,h]

private theorem ports_card (G : BipartiteMultigraph) (v : Fin G.nV) :
    (G.ports v).toFinset.card ≤ G.maxDeg := by
  refine (List.toFinset_card_le _).trans ?_
  change G.deg v ≤ (univ : Finset (Fin G.nV)).sup G.deg
  exact Finset.le_sup (f := G.deg) (Finset.mem_univ v)

private theorem shared_card (G : BipartiteMultigraph) (e : Fin G.nE) :
    (univ.filter fun f => left G e = left G f ∨ right G e = right G f).card ≤ 2*G.maxDeg := by
  let S := (G.ports (left G e)).toFinset
  let T := (G.ports (right G e)).toFinset
  have h : (univ.filter fun f => left G e = left G f ∨ right G e = right G f) ⊆ S ∪ T := by
    intro f hf
    simpa [S,T] using shared_subset G e f (mem_filter.mp hf).2
  calc
    _ ≤ (S ∪ T).card := card_le_card h
    _ ≤ S.card+T.card := card_union_le _ _
    _ ≤ _ := by have := ports_card G (left G e); have := ports_card G (right G e); dsimp [S,T]; omega

/-- Ordered pairs of edges sharing both endpoint labels. -/
def collisions (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) : ℕ :=
  ∑ e : Fin G.nE, ∑ f : Fin G.nE, pairCollision G e f L

def labels (G : BipartiteMultigraph) (q : ℕ) [NeZero q] : Fin G.nV → Fin q := labeling (terms G q)

private theorem initial_edge_sum (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    score (terms G q) (fun _ => none) ≤ G.nE*(G.nE*q^2+2*G.maxDeg*q^4) := by
  have per (e : Fin G.nE) :
      (∑ f : Fin G.nE, termScore (edgeTerm G q e f) (fun _ => none)) ≤
        G.nE*q^2 + 2*G.maxDeg*q^4 := by
    calc
      _ ≤ ∑ f : Fin G.nE, (q^2 + if left G e = left G f ∨ right G e = right G f then q^4 else 0) :=
        sum_le_sum fun f _ => initial_edge G q e f
      _ ≤ _ := by
        rw [sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,add_zero]
        simp only [Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        simpa using Nat.add_le_add_left (Nat.mul_le_mul_right (q^4) (shared_card G e)) (G.nE*q^2)
  have hs := sum_le_sum (s := univ) (fun e _ => per e)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_cast at hs
  simpa only [score,terms,edgePairs,List.map_map,Function.comp_def,pair_sum] using hs
private def finalScore {n q : ℕ} (ts : List (Term n q)) (L : Fin n → Fin q) :=
  (ts.map (fun t => t.penalty (fun i => L (t.vertex i)))).sum

private theorem edge_final (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    finalScore (terms G q) L = collisions G L := by
  simp only [finalScore,terms,edgePairs,List.map_map,Function.comp_def,cost_edge,pair_sum,collisions]

theorem collision_bound (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    q^2 * collisions G (labels G q) ≤ G.nE^2+2*G.nE*G.maxDeg*q^2 := by
  have hl := labeling_bound (terms G q)
  change q^4 * finalScore (terms G q) (labels G q) ≤ _ at hl
  rw [edge_final] at hl
  have hu := hl.trans (initial_edge_sum G q)
  have hcancel : q^2 * (q^2 * collisions G (labels G q)) ≤
      q^2 * (G.nE^2+2*G.nE*G.maxDeg*q^2) := by
    norm_cast at hu
    nlinarith only [hu]
  exact Nat.le_of_mul_le_mul_left hcancel (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
private def edgeCell (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (e : Fin G.nE) :=
  (L (left G e),L (right G e))

def cellSize (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (c : Fin q × Fin q) : ℕ :=
  ∑ e, if edgeCell G L e = c then 1 else 0

theorem cell_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c = G.nE := by
  unfold cellSize
  rw [sum_comm]; simp

theorem cell_square_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c ^ 2 = collisions G L := by
  have hp (c : Fin q × Fin q) : cellSize G L c ^2 =
      ∑ e, if edgeCell G L e = c then cellSize G L c else 0 := by
    calc
      _ = (∑ e, if edgeCell G L e = c then 1 else 0)*cellSize G L c := by rw [pow_two]; rfl
      _ = _ := by rw [sum_mul]; simp [ite_mul]
  simp_rw [hp]; rw [sum_comm]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold cellSize collisions pairCollision edgeCell
  apply sum_congr rfl; intro e he
  apply sum_congr rfl; intro f hf
  split_ifs <;> simp_all [eq_comm]

theorem cell_cap (G : BipartiteMultigraph) (q : ℕ) [NeZero q] (c : Fin q × Fin q)
    (hm : 2*G.maxDeg*q^4 ≤ G.nE) :
    q^2*cellSize G (labels G q) c ≤ 2*G.nE := by
  let X (g : Fin q × Fin q) : ℤ := cellSize G (labels G q) g
  let M : ℤ := G.nE
  let Q : ℤ := q
  let D : ℤ := G.maxDeg
  have hsum : ∑ g, X g = M := by dsimp only [X,M]; exact_mod_cast cell_sum G (labels G q)
  have henergy : Q^2*(∑ g, X g ^2) ≤ M^2+2*M*D*Q^2 := by
    have h := collision_bound G q
    rw [← cell_square_sum] at h
    dsimp only [Q,X,M,D]; exact_mod_cast h
  have hcard : (Fintype.card (Fin q × Fin q) : ℤ) = Q^2 := by simp [Q,pow_two]
  have hvar : ∑ g, (Q^2*X g-M)^2 = Q^4*∑ g, X g^2-Q^2*M^2 := by
    calc
      _ = ∑ g, (Q^4*X g^2-(2*Q^2*M)*X g+M^2) := by apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hsum,sum_const,card_univ,nsmul_eq_mul,hcard]; ring
  have hsingle := Finset.single_le_sum (f := fun g => (Q^2*X g-M)^2)
    (fun g _ => sq_nonneg _) (mem_univ c)
  rw [hvar] at hsingle
  have he := mul_le_mul_of_nonneg_left henergy (sq_nonneg Q)
  have hm' : 2*D*Q^4 ≤ M := by dsimp only [D,Q,M]; exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_left hm' (show 0 ≤ M by dsimp [M]; positivity)
  have hx : 0 ≤ Q^2*X c := by dsimp [Q,X]; positivity
  have h : Q^2 * X c ≤ 2*M := by
    by_contra! hf
    nlinarith only [hsingle,he,hh,mul_pos (sub_pos.mpr hf) (show 0 < Q^2*X c by dsimp [M] at hf; omega)]
  dsimp only [Q,X,M] at h
  exact_mod_cast h

private def weighted {n q : ℕ} (w : ℕ) (t : Term n q) : Term n q :=
  { t with penalty := fun z => w*t.penalty z }

private theorem weight_score {n q : ℕ} (w : ℕ) (ts : List (Term n q)) (p : Partial n q) :
    score (ts.map (weighted w)) p = w * score ts p := by
  induction ts with
  | nil => simp [score]
  | cons t ts ih =>
    have ht : termScore (weighted w t) p = w*termScore t p := by
      unfold termScore
      change q^(4-t.arity) * (∑ z : Fin t.arity → Fin q, w*t.penalty (fun h => (p (t.vertex h)).getD (z h))) = _
      rw [← mul_sum,mul_left_comm]
    simp only [score,List.map_cons,List.sum_cons] at ih ⊢
    rw [ht,ih,Nat.mul_add]

private theorem weight_final {n q : ℕ} (w : ℕ) (ts : List (Term n q)) (L : Fin n → Fin q) :
    finalScore (ts.map (weighted w)) L = w * finalScore ts L := by
  induction ts with
  | nil => simp [finalScore]
  | cons t ts ih => simp only [finalScore,List.map_cons,List.sum_cons,weighted] at ih ⊢; rw [ih,Nat.mul_add]

private def digitMatch {q s : ℕ} (d : Fin q → Fin s) (z : Fin 2 → Fin q) : ℕ :=
  if d (z 0) = d (z 1) then 1 else 0

private def legTerm {n q s : ℕ} (d : Fin q → Fin s) (x y : Fin n) : Term n q :=
  if h : x = y then constantTerm _ _ else
    { (pairTerm (q := q) x y h) with penalty := digitMatch d }

private theorem leg_final {n q s : ℕ} (d : Fin q → Fin s) (x y : Fin n) (L : Fin n → Fin q) :
    (legTerm d x y).penalty (fun i => L ((legTerm d x y).vertex i)) =
      if d (L x) = d (L y) then 1 else 0 := by
  by_cases h : x = y
  · have he : legTerm d x y = constantTerm n q := by rw [legTerm,dif_pos h]
    rw [he]; simp [constantTerm,h]
  · have he : legTerm d x y = { (pairTerm (q := q) x y h) with penalty := digitMatch d } := by rw [legTerm,dif_neg h]
    rw [he]; simp [pairTerm,digitMatch]

private theorem leg_initial {n q s : ℕ} (d : Fin q → Fin s)
    (hd : s * (∑ z, digitMatch d z) ≤ q^2) (x y : Fin n) :
    s * termScore (legTerm d x y) (fun _ => none) ≤
       q^4 + (if x = y then s*q^4 else 0) := by
  by_cases h : x = y
  · have he : legTerm d x y = constantTerm n q := by rw [legTerm,dif_pos h]
    rw [he,if_pos h]
    have hs0 : (∑ _ : Fin 0 → Fin q, 1 : ℕ) = 1 := by simp
    change s*(q^(4-0)*(∑ _ : Fin 0 → Fin q, 1 : ℕ)) ≤ _
    rw [hs0]; simp
  · simp only [legTerm,dif_neg h,if_neg h,add_zero]
    change s*(q^2*(∑ z, digitMatch d z)) ≤ q^4
    have hi := Nat.mul_le_mul_left (q^2) hd
    nlinarith only [hi]

private def legTerms {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n) :=
  (List.finRange a).flatMap fun i =>
    ((List.finRange b).flatMap fun x => (List.finRange b).map fun y => (x,y)).map
      fun p => legTerm (d i) (host p.1) (host p.2)

private theorem flat_sum {α γ : Type*} (F : α → List γ) (H : γ → ℕ) (l : List α) :
    ((l.flatMap F).map H).sum = (l.map fun x => ((F x).map H).sum).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem leg_cost_sum {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (H : Term n q → ℕ) :
    ((legTerms d host).map H).sum = ∑ i, ∑ x, ∑ y, H (legTerm (d i) (host x) (host y)) := by
  rw [legTerms,flat_sum,← Fin.sum_univ_def]
  simp only [List.map_map,Function.comp_def,pair_sum]

def terminalCollisions {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (L : Fin n → Fin q) : ℕ :=
  ∑ i, ∑ x, ∑ y, if d i (L (host x)) = d i (L (host y)) then 1 else 0

private theorem terminal_initial {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (τ : ℕ) (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hd : ∀ i, s * (∑ z, digitMatch (d i) z) ≤ q^2) :
    s * score (legTerms d host) (fun _ => none) ≤ a*(b*(b*q^4+τ*(s*q^4))) := by
  have per (i : Fin a) (x : Fin b) :
      (∑ y, s * termScore (legTerm (d i) (host x) (host y)) (fun _ => none)) ≤
        b*q^4+τ*(s*q^4) := by
    calc
      _ ≤ ∑ y, (q^4 + if host x = host y then s*q^4 else 0) := sum_le_sum fun y _ => leg_initial _ (hd i) _ _
      _ ≤ _ := by
        rw [sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,add_zero]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (ht x)) _
  unfold score
  rw [leg_cost_sum]
  simp_rw [mul_sum]
  have hh := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun x _ => per i x))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact_mod_cast hh

/-- Simultaneous edge and terminal collision control, with arbitrary integral objective weights. -/
theorem joint_collision_bound (G : BipartiteMultigraph) (q : ℕ) [NeZero q] {a s b : ℕ}
    (d : Fin a → Fin q → Fin s) (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hd : ∀ i, s * (∑ z, digitMatch (d i) z) ≤ q^2) :
    ∃ L : Fin G.nV → Fin q,
      s*q^2*(w*collisions G L + v*terminalCollisions d host L) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*q^2) + v*a*b*q^2*(b+τ*s) := by
  let E := terms G q
  let T := legTerms d host
  let ts := E.map (weighted w) ++ T.map (weighted v)
  let L := labeling ts
  refine ⟨L,?_⟩
  have he := initial_edge_sum G q
  have ht' := terminal_initial d host τ ht hd
  have hl := labeling_bound ts
  have hfin : finalScore ts L = w*collisions G L + v*terminalCollisions d host L := by
    change finalScore (_++_) L = _
    simp only [finalScore,List.map_append,List.sum_append]
    change finalScore (E.map _) L + finalScore (T.map _) L = _
    rw [weight_final,weight_final,edge_final]
    simp only [T,finalScore,leg_cost_sum,leg_final,terminalCollisions]
  have hinit : score ts (fun _ => none) = w*score E (fun _ => none)+v*score T (fun _ => none) := by
    simp only [ts,score,List.map_append,List.sum_append]
    exact congrArg₂ (·+·) (weight_score w E _) (weight_score v T _)
  change q^4 * finalScore ts L ≤ score ts (fun _ => none) at hl
  rw [hfin,hinit] at hl
  have R := Nat.mul_le_mul_left s hl
  have F := Nat.mul_le_mul_left (s*w) he
  have H := Nat.mul_le_mul_left v ht'
  change s * (q^4 * _) ≤ s*(w*score (terms G q) _ + v*score (legTerms d host) _) at R
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < q^2 from pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
  nlinarith only [R,F,H]


private theorem coord_balanced {q s : ℕ} {R : Type*} [Fintype R]
    (e : Fin q ≃ Fin s × R) :
    s * (∑ z, digitMatch (fun t => (e t).1) z) = q^2 := by
  classical
  let P (z : Fin 2 → Fin q) := (e (z 0)).1 = (e (z 1)).1
  let equiv : {z // P z} ≃ Fin s × (R × R) := {
    toFun := fun z => ((e (z.1 0)).1,(e (z.1 0)).2,(e (z.1 1)).2)
    invFun := fun t => ⟨![e.symm (t.1,t.2.1),e.symm (t.1,t.2.2)],by simp [P]⟩
    left_inv := by
      intro z; apply Subtype.ext; funext k
      fin_cases k
      · simp
      · have hh := z.property
        change (e (z.1 0)).1 = (e (z.1 1)).1 at hh
        simp [hh]
    right_inv := by intro t; simp }
  have hcount : (∑ z, digitMatch (fun t => (e t).1) z) = s*Fintype.card R^2 := by
    simpa [digitMatch,P,Fintype.card_subtype,pow_two,mul_assoc] using Fintype.card_congr equiv
  have hq : q = s*Fintype.card R := by simpa using Fintype.card_congr e
  rw [hcount,hq]; ring

/-- Ordered label cells and base-s digit legs can be balanced with one vertex assignment. -/
theorem digit_collision_bound (G : BipartiteMultigraph) (s : ℕ) [NeZero s] (a : ℕ)
    {b : ℕ} (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ) :
    ∃ L : Fin G.nV → Fin (s^a),
      s*(s^a)^2*(w*collisions G L +
          v*terminalCollisions (fun i z => finFunctionFinEquiv.symm z i) host L) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*(s^a)^2) + v*a*b*(s^a)^2*(b+τ*s) := by
  apply joint_collision_bound G _ _ _ _ _ _ ht
  intro i
  let e : Fin (s^a) ≃ Fin s × ({j : Fin a // j ≠ i} → Fin s) :=
    finFunctionFinEquiv.symm.trans (Equiv.funSplitAt i (Fin s))
  exact (coord_balanced e).le

end DetDLP.EdgeLabelPartition

open DetDLP DetDLP.EdgeLabelPartition

theorem solution (G : BipartiteMultigraph) (s : ℕ) [NeZero s] (a : ℕ)
    {b : ℕ} (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (Finset.univ.filter fun y => host x = host y).card ≤ τ) :
    let q := s^a
    let l := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
    let r := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2
    ∃ L : Fin G.nV → Fin q,
      let X := fun c : Fin q × Fin q => ∑ e : Fin G.nE, if (L (l e),L (r e)) = c then 1 else 0
      let Y := ∑ i : Fin a, ∑ x : Fin b, ∑ y : Fin b,
        if finFunctionFinEquiv.symm (L (host x)) i = finFunctionFinEquiv.symm (L (host y)) i then 1 else 0
      s*q^2*(w*(∑ c, (X c)^2) + v*Y) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*q^2) + v*a*b*q^2*(b+τ*s) := by
  intro q l r
  obtain ⟨L,hL⟩ := digit_collision_bound G s a host τ w v ht
  rw [← cell_square_sum] at hL
  exact ⟨L,hL⟩
