-- Prove2me | solution 1 for DirectedHamiltonicity.Main.bounded_adaptive_cycle_controller
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T04:12:04.423592+00:00
-- url     : https://prove2.me/submissions/32eda6fa-1699-4dd7-9515-d3080d06d5a5

import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_DirectedHamiltonicity_CycleController
import Definitions.Def_LogCostRAM_StructuredExecution
import Theorems.Thm_DirectedHamiltonicity_Main_read_cycle_graph_ram
import Theorems.Thm_DirectedHamiltonicity_Main_prepare_cycle_parity_query_ram
import Mathlib.Algebra.Order.Floor.Div

namespace DirectedHamiltonicity.Main.CycleReduction.GraphWords

open TargetedSamplers

/-- Row-major bit index and the decoded adjacency matrix. -/
def index {n : ℕ} (u v : Fin n) := v.val+n*u.val
def graph (n word : ℕ) (u v : Fin n) := word.testBit (index u v)

theorem index_eq {n : ℕ} (u v : Fin n) : index u v=(finProdFinEquiv (u,v)).val := rfl

theorem index_inj {n : ℕ} {u v s t : Fin n} : index u v=index s t ↔ (u,v)=(s,t) := by
  change (finProdFinEquiv (u,v)).val=(finProdFinEquiv (s,t)).val ↔ _
  rw [Fin.val_inj,Equiv.apply_eq_iff_eq]

theorem index_lt {n : ℕ} (u v : Fin n) : index u v<n*n := (finProdFinEquiv (u,v)).isLt

theorem clipped (n word : ℕ) : graph n (word%2^(n*n))=graph n word := by
  funext u v;simp [graph,Nat.testBit_mod_two_pow,index_lt]

/-- Adding the mask of a missing bit sets exactly that bit. -/
theorem insert_bit (x p : ℕ) (off : x.testBit p=false) (i : ℕ) :
    (x+2^p).testBit i = (decide (i=p) || x.testBit i) := by
  by_cases eq : i=p
  · subst i;rw [Nat.add_comm,Nat.testBit_two_pow_add_eq,off];simp
  by_cases lower : i<p
  · rw [Nat.add_comm,Nat.testBit_two_pow_add_gt lower];simp [eq]
  let a := x/2^(p+1)
  let b := x%2^(p+1)
  have pos := Nat.two_pow_pos (p+1)
  have cap : b<2^(p+1) := Nat.mod_lt _ pos 
  have split : x=2^(p+1)*a+b := (Nat.div_add_mod ..).symm
  have lo : b<2^p := by
    by_contra! le
    have on : b.testBit p=true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt le cap
    have bit := Nat.testBit_mod_two_pow x (p+1) p
    change b.testBit p=_ at bit
    simp [off] at bit
    simp_all
  have fits : b+2^p<2^(p+1) := by rw [pow_succ];omega
  conv_lhs => rw [split,Nat.add_assoc,Nat.testBit_two_pow_mul_add _ fits]
  conv_rhs => rw [split,Nat.testBit_two_pow_mul_add _ cap]
  simp [eq,show ¬i<p+1 by omega]

/-- Erasing a bit uses only integer quotient, remainder and truncated subtraction. -/
def erase (x p : ℕ) := if x/2^p%2=0 then x else x-2^p

theorem erase_bit (x p i : ℕ) : (erase x p).testBit i = (decide (i≠p) && x.testBit i) := by
  cases on : x.testBit p with
  | false =>
    have digit : x/2^p%2=0 := by rw [←Nat.toNat_testBit,on];rfl
    by_cases e : i=p <;> simp_all [erase,digit]
  | true =>
    have digit : x/2^p%2=1 := by rw [←Nat.toNat_testBit,on];rfl
    have fits : 2^p ≤ x := by
      by_contra! lt
      rw [Nat.testBit_lt_two_pow lt] at on;contradiction
    let y := x-2^p
    have sum : y+2^p=x := Nat.sub_add_cancel fits
    have off : y.testBit p=false := by
      have h := Nat.testBit_two_pow_add_eq y p
      rw [Nat.add_comm, sum,on] at h
      cases b : y.testBit p <;> simp [b] at h ⊢
    have rest := insert_bit y p off i
    rw [sum] at rest
    change (if x/2^p%2=0 then x else y).testBit i=_
    rw [if_neg (by omega)]
    by_cases e : i=p
    · subst i;simp [off]
    · simpa [e] using rest.symm

theorem erase_graph {n : ℕ} (word : ℕ) (p : Fin n × Fin n) :
    graph n (erase word (index p.1 p.2))=adjacency ((edges (graph n word)).erase p) := by
  funext u v
  change (erase word (index p.1 p.2)).testBit (index u v)=_
  rw [erase_bit]
  have key : index u v=index p.1 p.2 ↔ (u,v)=p := index_inj
  have mem : (u,v) ∈ edges (graph n word) ↔ word.testBit (index u v)=true := by
    unfold edges;rw [Finset.mem_filter];simp only [Finset.mem_univ,true_and];rfl
  unfold adjacency
  simp only [Finset.mem_erase,mem]
  by_cases e : (u,v)=p <;> cases bit : word.testBit (index u v) <;> simp [key,e,bit]

theorem adjacency_edges {n : ℕ} (a : Fin n → Fin n → Bool) : adjacency (edges a)=a := by
  funext u v;simp [adjacency,edges]

theorem edges_adjacency {n : ℕ} (a : Finset (Fin n × Fin n)) : edges (adjacency a)=a := by
  ext p;simp [adjacency,edges]

theorem row_order (n : ℕ) : edgeOrder n=(List.finRange (n*n)).map (fun i => finProdFinEquiv.symm i) := by
  unfold edgeOrder
  conv_rhs => rw [←List.ofFn_eq_map,List.ofFn_mul]
  simp only [List.ofFn_eq_map,←List.flatMap_def]
  apply congrArg (fun f => (List.finRange n).flatMap f)
  funext i
  apply congrArg (fun f => (List.finRange n).map f)
  funext j
  have idx (h : i.val*n+j.val<n*n) : (⟨i.val*n+j.val,h⟩ : Fin (n*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext;change _=j.val+n*i.val;ring
  rw [idx _,Equiv.symm_apply_apply]

end DirectedHamiltonicity.Main.CycleReduction.GraphWords

namespace DirectedHamiltonicity.Main.CycleReduction.GraphWords

structure Walk (n : ℕ) where
  vertex : Fin n
  seen : ℕ
  valid : Bool

def advance {n : ℕ} (R : Finset (Fin n × Fin n)) (a : Walk n) : Walk n :=
  let u := a.vertex
  let v := nextVertex R u
  let seen := a.seen.testBit u.val
  ⟨v,if seen then a.seen else a.seen+2^u.val,
    a.valid && (!seen) && decide ((u,v)∈R)⟩

def tour {n : ℕ} (R : Finset (Fin n × Fin n)) (root : Fin n) (j : ℕ) :=
  (advance R)^[j] ⟨root,0,true⟩

def acceptable {n : ℕ} (R : Finset (Fin n × Fin n)) (f : ℕ → Fin n) (i : ℕ) :=
  (∀ j < i,(f j,nextVertex R (f j))∈R) ∧ ∀ a < i, ∀ b < i, f a=f b → a=b

private theorem extend {n : ℕ} (R : Finset (Fin n × Fin n)) (f : ℕ → Fin n) (i : ℕ) :
    acceptable R f (i+1) ↔ acceptable R f i ∧ (∀ j < i, f j≠f i) ∧ (f i,nextVertex R (f i))∈R := by
  constructor
  · rintro ⟨edges,distinct⟩
    exact ⟨⟨fun j hj => edges _ (by omega),fun a ha b hb eq => distinct _ (by omega) _ (by omega) eq⟩,
      fun j hj eq => (Nat.ne_of_lt hj) (distinct _ (by omega) _ (by omega) eq),edges _ (by omega)⟩
  · rintro ⟨⟨edges,distinct⟩,fresh,edge⟩
    constructor
    · intro j hj;rcases Nat.lt_or_eq_of_le (by omega : j ≤ i) with h|rfl
      · exact edges _ h
      · exact edge
    · intro a ha b hb eq
      by_cases aSmall : a < i
      · by_cases bSmall : b < i
        · exact distinct _ aSmall _ bSmall eq
        · have bi : b=i := by omega
          exact (fresh _ aSmall (bi ▸ eq)).elim
      · by_cases bSmall : b < i
        · have ai : a=i := by omega
          exact (fresh _ bSmall (ai ▸ eq.symm)).elim
        · omega

/-- The seen word records exactly the vertices of the processed orbit prefix, even after
a duplicate or a missing outgoing arc has made the certificate invalid. -/
theorem tour_invariant {n : ℕ} (R : Finset (Fin n × Fin n)) (root : Fin n) (j : ℕ) :
    let f := fun k => (nextVertex R)^[k] root
    let t := tour R root j
    t.vertex=f j ∧ (∀ i, t.seen.testBit i=true ↔ ∃ k < j, (f k).val=i) ∧
      (t.valid=true ↔ acceptable R f j) := by
  let f := fun k => (nextVertex R)^[k] root
  induction j with
  | zero => simp [tour,acceptable]
  | succ j ih =>
    let t := tour R root j
    let u := f j
    obtain ⟨vertex,words,ok⟩ := ih
    change t.vertex=u at vertex
    change ∀ i, t.seen.testBit i=true ↔ ∃ k < j, (f k).val=i at words
    change t.valid=true ↔ acceptable R f j at ok
    change (tour R root (j+1)).vertex=f (j+1) ∧ _ ∧ _
    have step : tour R root (j+1)=advance R t := Function.iterate_succ_apply' ..
    have split (i : ℕ) : (∃ k < j+1,(f k).val=i) ↔ u.val=i ∨ ∃ k < j,(f k).val=i := by
      constructor
      · rintro ⟨k,h,v⟩
        rcases Nat.lt_or_eq_of_le (by omega : k ≤ j) with lt|rfl
        · exact Or.inr ⟨_,lt,v⟩
        · exact Or.inl v
      · rintro (h|⟨k,lt,h⟩)
        · exact ⟨j,by omega,h⟩
        · exact ⟨k,by omega,h⟩
    refine ⟨?_,?_,?_⟩
    · rw [step];change nextVertex R t.vertex=f (j+1);rw [vertex];exact (Function.iterate_succ_apply' ..).symm
    · intro i
      change (tour R root (j+1)).seen.testBit i=true ↔ _
      rw [step,split]
      cases seen : t.seen.testBit u.val with
      | false =>
        simp only [advance,vertex,seen,Bool.false_eq_true,if_false,insert_bit _ _ seen, Bool.or_eq_true,
          decide_eq_true_eq,words];rw [show (i=u.val) ↔ (u.val=i) from eq_comm]
      | true =>
        simp only [advance,vertex,seen,if_true,words]
        constructor
        · exact Or.inr
        · rintro (h|w)
          · rw [←h];exact (words _).1 seen
          · exact w
    · change (tour R root (j+1)).valid=true ↔ acceptable R f (j+1)
      rw [step,extend]
      have fresh : t.seen.testBit u.val=false ↔ ∀ k < j,f k≠u := by
        constructor
        · intro off k hk eq
          have seen := (words u.val).2 ⟨k,hk,congrArg Fin.val eq⟩
          rw [off] at seen;contradiction
        · intro fresh
          cases eq : t.seen.testBit u.val with
          | false => rfl
          | true =>
            obtain ⟨k,hk,h⟩ := (words u.val).1 eq
            exact (fresh k hk (Fin.ext h)).elim
      simp only [advance,vertex,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,ok,fresh]
      tauto

theorem certify_by_word (n word : ℕ) :
    let R := edges (graph (n+1) word)
    let z := tour R 0 (n+1)
    (z.valid && decide (z.vertex=0))=certify (n+1) R := by
  intro R z
  obtain ⟨vertex,_,valid⟩ := tour_invariant R 0 (n+1)
  let f := fun k => (nextVertex R)^[k] (0 : Fin (n+1))
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq,certify]
  change (z.valid=true ∧ z.vertex=0) ↔ f (n+1)=0 ∧
    (∀ i : Fin (n+1),(f i,nextVertex R (f i))∈R) ∧ ∀ i j : Fin (n+1), f i=f j → i=j
  change z.vertex=f (n+1) at vertex
  change z.valid=true ↔ acceptable R f (n+1) at valid
  rw [vertex,valid];constructor
  · rintro ⟨⟨arcs,inject⟩,closed⟩
    exact ⟨closed,fun i => arcs _ i.isLt,fun i j eq => Fin.ext (inject _ i.isLt _ j.isLt eq)⟩
  · rintro ⟨closed,arcs,unique⟩
    exact ⟨⟨fun i hi => arcs ⟨i,hi⟩,fun i hi j hj eq => congrArg Fin.val (unique ⟨i,hi⟩ ⟨j,hj⟩ eq)⟩,closed⟩

end DirectedHamiltonicity.Main.CycleReduction.GraphWords

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

@[simp] theorem Store.write_overwrite (s : Store) (a x y : ℕ) : (s.write a x).write a y = s.write a y := by
  simp [Store.write]

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)


end TargetedSamplers.Structured

section LogCostRAMDivisionStep

namespace TargetedSamplers.Structured.Word

private theorem doublePair_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b z a : ℕ} {s : Store}
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (fit : s.Fits b)
    (hz : (2*z).size ≤ b) (hz' : (2*(2*z)).size ≤ b) (ha : (2*a).size ≤ b) :
    let t := ((doublePair r).run τ s).last
    Exec τ (fun u => u.Fits b) (doublePair r).cmd s t 3 ∧
      t.mem (r 3) = 2*z ∧ t.mem (r 4) = 2*a ∧ t.mem (r 5) = 2*(2*z) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  simp only [two_mul] at hz hz' ha
  have width : ((doublePair r).run τ s).writeWidth ≤ b := by
    simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,scale,factor,hz,hz',ha]
  refine ⟨(doublePair r).exec τ s b fit width,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro k h3 h4 h5
       simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
         Function.update_apply,h3,h4,h5])
    | simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,eq,scale,factor,two_mul]

/-- Select the largest shifted multiple fitting in the remainder. Only addition and a
comparison are used; doubling until the next multiple is too large takes 5j+1 primitive
instructions, where j is the selected shift. -/
theorem growPair_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (j rem z a : ℕ) (s : Store)
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (dbl : s.mem (r 5) = 2*z)
    (upper : s.mem (r 6) = rem+1) (fit : s.Fits b) (width : (2*rem).size ≤ b)
    (amountWidth : (a*2^j).size ≤ b) (low : z*2^j ≤ rem) (high : rem < 2*(z*2^j)) :
    ∃ t, Exec τ (fun u => u.Fits b) (grow r) s t (5*j+1) ∧
      t.mem (r 3) = z*2^j ∧ t.mem (r 4) = a*2^j ∧ t.mem (r 5) = 2*(z*2^j) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  induction j generalizing s z a with
  | zero =>
    simp only [pow_zero,Nat.mul_one] at high ⊢
    exact ⟨s,.done (by rw [upper,dbl]; omega),scale,factor,dbl,rfl,fun _ _ _ _ => rfl⟩
  | succ j ih =>
    have zs : 2*z*2^j = z*2^(j+1) := by rw [pow_succ]; ring
    have zs' : 2*z ≤ rem := (by
      have h := Nat.mul_le_mul_left (2*z) (Nat.one_le_two_pow (n := j))
      rw [Nat.mul_one,zs] at h
      exact h.trans low)
    have pw (v : ℕ) (hv : v ≤ 2*rem) : v.size ≤ b := (Nat.size_le_size hv).trans width
    have az : 2*a*2^j = a*2^(j+1) := by rw [pow_succ]; ring
    have amt : 2*a ≤ a*2^(j+1) := by
      simpa only [Nat.mul_one,az] using Nat.mul_le_mul_left (2*a) (Nat.one_le_two_pow (n := j))
    obtain ⟨ex,sz,sz',db,out,save⟩ := doublePair_exec (τ := τ) r scale factor fit
      (pw _ (by omega)) (pw _ (by omega)) ((Nat.size_le_size amt).trans amountWidth)
    let u := ((doublePair r).run τ s).last
    have ne {i k : Fin 9} (h : i ≠ k) := r.injective.ne h
    have up := (save (r 6) (ne (by decide)) (ne (by decide)) (ne (by decide))).trans upper
    obtain ⟨t,loop,finalZ,finalA,finalD,log,frame⟩ := ih (2*z) (2*a) u sz sz' db up
      (ex.post fit) (by rwa [az]) (by rwa [zs]) (by rwa [zs])
    have go : ¬s.mem (r 6) ≤ s.mem (r 5) := by rw [upper,dbl]; omega
    have count : 5*(j+1)+1 = 1+3+1+(5*j+1) := by omega
    refine ⟨t,?_,?_,?_,?_,log.trans out,?_⟩
    · rw [count]; exact .again go ex loop
    · simpa only [zs] using finalZ
    · simpa only [show 2*a*2^j = a*2^(j+1) by rw [pow_succ]; ring] using finalA
    · simpa only [zs] using finalD
    · intro k h3 h4 h5; exact (frame k h3 h4 h5).trans (save k h3 h4 h5)

/-- Specialization for division, where the quotient-place register never exceeds the
shifted divisor. -/
theorem grow_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (j rem z a : ℕ) (s : Store)
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (dbl : s.mem (r 5) = 2*z)
    (upper : s.mem (r 6) = rem+1) (ha : a ≤ z) (fit : s.Fits b) (width : (2*rem).size ≤ b)
    (low : z*2^j ≤ rem) (high : rem < 2*(z*2^j)) :
    ∃ t, Exec τ (fun u => u.Fits b) (grow r) s t (5*j+1) ∧
      t.mem (r 3) = z*2^j ∧ t.mem (r 4) = a*2^j ∧ t.mem (r 5) = 2*(z*2^j) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  have small := (Nat.mul_le_mul_right (2^j) ha).trans low
  exact growPair_exec r j rem z a s scale factor dbl upper fit width
    ((Nat.size_le_size (show a*2^j ≤ 2*rem by omega)).trans width) low high

/-- The binary shift is bounded by the number of bits of the dividend, independent of
the numerical quotient. -/
theorem shift_exists {d x : ℕ} (hd : 0 < d) (hx : d ≤ x) :
    ∃ j ≤ x.size, d*2^j ≤ x ∧ x < 2*(d*2^j) := by
  let q := x/d
  have hp : 0 < q := Nat.div_pos hx hd
  have pos := Nat.size_pos.mpr hp
  let j := q.size-1
  have hj : j+1 = q.size := by dsimp [j]; omega
  have hlo : 2^j ≤ q := Nat.lt_size.mp (by omega)
  have hhi : q < 2^(j+1) := by rw [hj]; exact Nat.lt_size_self q
  have small := (Nat.le_div_iff_mul_le hd).mp hlo
  have large := (Nat.div_lt_iff_lt_mul hd).mp hhi
  refine ⟨j,le_trans (by omega : j ≤ q.size) (Nat.size_le_size (Nat.div_le_self x d)),?_,?_⟩
  · simpa [Nat.mul_comm] using small
  · have e : 2^(j+1)*d = 2*(d*2^j) := by rw [pow_succ]; ring
    rwa [← e]

end TargetedSamplers.Structured.Word

end LogCostRAMDivisionStep

section LogCostRAMDivision

namespace TargetedSamplers.Structured.Word

structure DivRegs (r : Fin 9 ↪ ℕ) (s : Store) (rem d q : ℕ) : Prop where
  remReg : s.mem (r 0) = rem
  divisor : s.mem (r 1) = d
  quotient : s.mem (r 2) = q
  upper : s.mem (r 6) = rem+1
  zero : s.mem (r 7) = 0
  one : s.mem (r 8) = 1

theorem DivRegs.scratch {r : Fin 9 ↪ ℕ} {s t : Store} {rem d q : ℕ} (h : DivRegs r s rem d q)
    (frame : ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → t.mem a = s.mem a) : DivRegs r t rem d q := by
  have get (i : Fin 9) (a : i ≠ 3) (b : i ≠ 4) (c : i ≠ 5) := frame (r i) (r.injective.ne a) (r.injective.ne b) (r.injective.ne c)
  exact ⟨(get 0 (by decide) (by decide) (by decide)).trans h.remReg,
    (get 1 (by decide) (by decide) (by decide)).trans h.divisor,(get 2 (by decide) (by decide) (by decide)).trans h.quotient,
    (get 6 (by decide) (by decide) (by decide)).trans h.upper,(get 7 (by decide) (by decide) (by decide)).trans h.zero,
    (get 8 (by decide) (by decide) (by decide)).trans h.one⟩

private theorem start_exec {r : Fin 9 ↪ ℕ} {τ : Tapes} {b rem d q : ℕ} {s : Store}
    (hr : DivRegs r s rem d q) (fit : s.Fits b) (hb : 1 ≤ b) (wd : (2*d).size ≤ b) :
    let t := ((startRound r).run τ s).last
    Exec τ (fun u => u.Fits b) (startRound r).cmd s t 3 ∧ t.mem (r 3) = d ∧ t.mem (r 4) = 1 ∧
      t.mem (r 5) = 2*d ∧ t.out = s.out ∧ ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → t.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have h := hr.divisor ▸ fit (r 1)
  have ww : ((startRound r).run τ s).writeWidth ≤ b := by
    simp only [two_mul] at wd
    simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,hr.divisor,hr.zero,wd,h,hb]
  refine ⟨(startRound r).exec τ s b fit ww,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a n3 n4 n5; simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,n3,n4,n5])
    | simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,eq,hr.divisor,hr.zero,two_mul]

theorem finishRound_exec {r : Fin 9 ↪ ℕ} {τ : Tapes} {b rem d q z a : ℕ} {s : Store}
    (hr : DivRegs r s rem d q) (scale : s.mem (r 3) = z) (amount : s.mem (r 4) = a) (fit : s.Fits b)
    (wrem : (rem-z+1).size ≤ b) (wq : (q+a).size ≤ b) :
    let t := ((finishRound r).run τ s).last
    Exec τ (fun u => u.Fits b) (finishRound r).cmd s t 3 ∧ DivRegs r t (rem-z) d (q+a) ∧
      t.out = s.out ∧ ∀ k, (∀ i, k ≠ r i) → t.mem k = s.mem k := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have ww' := (Nat.size_le_size (show rem-z ≤ rem-z+1 by omega)).trans wrem
  have ww : ((finishRound r).run τ s).writeWidth ≤ b := by
    simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,hr.remReg,hr.quotient,hr.one,scale,amount,ww',wrem,wq]
  refine ⟨(finishRound r).exec τ s b fit ww,?_,rfl,?_⟩
  · constructor <;> simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,hr.remReg,hr.divisor,hr.quotient,hr.zero,hr.one,scale,amount]
  · intro k hk
    simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,hk]

theorem size_lt_of_double_lt {old new : ℕ} (h : 2*new < old) : new.size < old.size := by
  have ho := Nat.size_pos.mpr (show 0 < old by omega)
  have e : 2^old.size = 2^(old.size-1)*2 := by
    conv_lhs => rw [show old.size = old.size-1+1 by omega,pow_succ]
  have lim := Nat.lt_size_self old
  rw [e] at lim
  have hn := Nat.size_le.mpr (show new < 2^(old.size-1) by omega)
  omega

/-- Quotient selection by maximal doubling removes at least half of the remainder at
each round. Thus division is polynomial in bit *length* on the addition-only RAM. -/
theorem quotientLoop_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (x d : ℕ) (hd : 0 < d)
    (hb : 1 ≤ b) (width : (2*x+2).size ≤ b) (fuel rem q : ℕ) (s : Store)
    (hr : DivRegs r s rem d q) (law : d*q+rem = x) (bound : rem.size ≤ fuel) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (quotientLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
      DivRegs r t (x%d) d (x/d) ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have done {rem q fuel : ℕ} {s : Store} (hr : DivRegs r s rem d q) (law : d*q+rem = x) (lt : rem < d) :
      ∃ t j, Exec τ (fun u => u.Fits b) (quotientLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
        DivRegs r t (x%d) d (x/d) ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
    have eq : x = rem+d*q := by omega
    refine ⟨s,1,.done (by rw [hr.upper,hr.divisor]; omega),by omega,?_,rfl,fun _ _ => rfl⟩
    simpa only [eq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lt,Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt lt,Nat.zero_add] using hr
  induction fuel generalizing s rem q with
  | zero =>
    have h := Nat.size_eq_zero.mp (by omega : rem.size = 0)
    exact done hr law (by omega)
  | succ fuel ih =>
    by_cases stop : rem < d
    · exact done hr law stop
    have le : d ≤ rem := by omega
    obtain ⟨k,hk,low,high⟩ := shift_exists hd le
    have wr (v : ℕ) (hv : v ≤ 2*x+2) := (Nat.size_le_size hv).trans width
    obtain ⟨init,z,a,z₂,oi,fi⟩ := start_exec (τ := τ) hr fit hb (wr _ (by omega))
    obtain ⟨v,loop,scale,amount,_,og,fg⟩ := grow_exec (τ := τ) r k rem d 1 _ z a z₂
      (hr.scratch fi).upper hd (init.post fit) (wr _ (by omega)) low high
    let pow := 2^k
    let rem' := rem-d*pow
    have next : d*(q+pow)+rem' = x := by
      dsimp [rem',pow]; rw [Nat.mul_add]; omega
    have qx : q+pow ≤ x := by
      have h := Nat.mul_le_mul_right (q+pow) hd
      simp only [Nat.one_mul] at h; omega
    have red : 2*rem' < rem := by dsimp [rem',pow]; omega
    have shrink := size_lt_of_double_lt red
    obtain ⟨finish,hr',ofin,ff⟩ := finishRound_exec (τ := τ) ((hr.scratch fi).scratch fg) scale
      (show v.mem (r 4) = pow by simpa [pow] using amount) (loop.post (init.post fit))
      (wr _ (by change rem-d*pow+1 ≤ _; omega)) (wr _ (by omega))
    obtain ⟨t,j,rest,hj,reg,out,fre⟩ := ih rem' (q+pow) _ hr' next (by omega) (finish.post (loop.post (init.post fit)))
    have go : ¬s.mem (r 6) ≤ s.mem (r 1) := by rw [hr.upper,hr.divisor]; omega
    have hx := hk.trans (Nat.size_le_size (by omega : rem ≤ x))
    refine ⟨t,_,.again go (init.seq (loop.seq finish)) rest,?_,reg,out.trans (ofin.trans (og.trans oi)),?_⟩
    · rw [Nat.succ_mul fuel (5*x.size+9)]; omega
    · intro addr f
      exact (fre addr f).trans ((ff addr f).trans ((fg addr (f 3) (f 4) (f 5)).trans (fi addr (f 3) (f 4) (f 5))))

/-- Shared zero accumulator, constant registers, and upper bound for shifted arithmetic. -/
theorem initDiv_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {width : ℕ} (x d : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (divisor : s.mem (r 1) = d) (fit : s.Fits width) (hb : 1 ≤ width)
    (upper : (x+1).size ≤ width) :
    let u := ((initDiv r).run τ s).last
    Exec τ (fun v => v.Fits width) (initDiv r).cmd s u 4 ∧ DivRegs r u x d 0 ∧ u.out = s.out ∧
      ∀ a, (∀ i, a ≠ r i) → u.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  let u := ((initDiv r).run τ s).last
  have good : ((initDiv r).run τ s).writeWidth ≤ width := by
    simp [initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,input,hb,upper]
  have init : Exec τ (fun v => v.Fits width) (initDiv r).cmd s u 4 := (initDiv r).exec τ s width fit good
  have hr : DivRegs r u x d 0 := by
    constructor <;> simp [u,initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,input,divisor]
  have fr (a : ℕ) (f : ∀ i, a ≠ r i) : u.mem a = s.mem a := by
    simp [u,initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,f]
  exact ⟨init,hr,rfl,fr⟩

/-- Compute both natural division and remainder on the posted RAM, including divisor
zero. A b-bit dividend uses at most 5b²+9b+7 primitive instructions; the largest new
word is at most 2x+2. Caller memory is framed. -/
theorem divMod_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {width : ℕ} (x d : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (divisor : s.mem (r 1) = d) (fit : s.Fits width)
    (hb : 1 ≤ width) (hw : (2*x+2).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (divMod r) s t j ∧ j ≤ x.size*(5*x.size+9)+7 ∧
      t.mem (r 0) = x%d ∧ t.mem (r 2) = x/d ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  let u := ((initDiv r).run τ s).last
  obtain ⟨init,hr,_,fr⟩ := initDiv_exec (τ := τ) r x d s input divisor fit hb
    ((Nat.size_le_size (by omega : x+1 ≤ 2*x+2)).trans hw)
  by_cases hd : d = 0
  · refine ⟨u,_,init.seq (.yes (by rw [hr.divisor,hr.zero,hd]) (.skip u)),by omega,
      by simpa [hd] using hr.remReg,by simpa [hd] using hr.quotient,rfl,fr⟩
  · obtain ⟨t,j,loop,hj,out,ot,ft⟩ := quotientLoop_exec (τ := τ) r x d (by omega) hb hw x.size x 0 u hr
      (by simp) le_rfl (init.post fit)
    refine ⟨t,_,init.seq (.no (by rw [hr.divisor,hr.zero]; omega) loop),by omega,
      out.remReg,out.quotient,ot,fun a f => (ft a f).trans (fr a f)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMDivision

section LogCostRAMMultiply

namespace TargetedSamplers.Structured.Word

private theorem startMultiple_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b rem y q : ℕ} {s : Store}
    (h : DivRegs r s rem y q) (fit : s.Fits b) (hb : 2 ≤ b) :
    let u := ((startMultiple r).run τ s).last
    Exec τ (fun t => t.Fits b) (startMultiple r).cmd s u 3 ∧ u.mem (r 3) = 1 ∧
      u.mem (r 4) = y ∧ u.mem (r 5) = 2 ∧ u.out = s.out ∧
      ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → u.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have hy := h.divisor ▸ fit (r 1)
  have two : (2:ℕ).size ≤ b := (by decide : (2:ℕ).size ≤ 2).trans hb
  have safe : ((startMultiple r).run τ s).writeWidth ≤ b := by
    simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,h.divisor,h.zero,hy,two]; omega
  refine ⟨(startMultiple r).exec τ s b fit safe,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a h₃ h₄ h₅; simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Store.write,h₃,h₄,h₅])
    | simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.divisor,h.zero]

private theorem multiplyLoop_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b : ℕ} (x y : ℕ)
    (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b) (wp : (x*y).size ≤ b) (fuel rem q : ℕ) (s : Store)
    (hr : DivRegs r s rem y q) (hx : rem ≤ x) (law : q+rem*y = x*y)
    (bound : rem.size ≤ fuel) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (multiplyLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
      t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have done {n q : ℕ} {s : Store} (hr : DivRegs r s 0 y q) (h : q+0*y = x*y) :
      ∃ t j, Exec τ (fun v => v.Fits b) (multiplyLoop r) s t j ∧ j ≤ n*(5*x.size+9)+1 ∧
        t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a :=
    ⟨s,1,.done (by rw [hr.remReg,hr.zero]),by omega,hr.quotient.trans (by simpa using h),rfl,fun _ _ => rfl⟩
  induction fuel generalizing rem q s with
  | zero =>
    have zero : rem = 0 := Nat.size_eq_zero.mp (by omega)
    subst rem; exact done hr law
  | succ fuel ih =>
    by_cases hzero : rem=0
    · subst rem; exact done hr law
    obtain ⟨k,hk,lo,hi⟩ := shift_exists (by decide : 0 < 1) (show 1 ≤ rem by omega)
    simp only [Nat.one_mul] at lo hi
    let z := 2^k
    have amount : y*z ≤ x*y := by
      simpa only [Nat.mul_comm y z] using Nat.mul_le_mul_right y (lo.trans hx)
    obtain ⟨init,start,coeff,dbl,oi,fi⟩ := startMultiple_exec (τ := τ) r hr fit hb
    obtain ⟨u,loop,pow,term,_,og,fg⟩ := growPair_exec (τ := τ) r k rem 1 y _ start coeff dbl (hr.scratch fi).upper
      (init.post fit) ((Nat.size_le_size (by omega : 2*rem ≤ 2*x+2)).trans wx)
      ((Nat.size_le_size amount).trans wp) (by simpa using lo) (by simpa using hi)
    have split : z+(rem-z) = rem := Nat.add_sub_of_le lo
    have product := congrArg (fun v : ℕ => v*y) split
    simp only [Nat.add_mul] at product
    have law' : (q+y*z)+(rem-z)*y = x*y := by rw [Nat.mul_comm y z]; omega
    have sumWidth := (Nat.size_le_size (show q+y*z ≤ x*y by omega)).trans wp
    obtain ⟨finish,hnext,ofin,ff⟩ := finishRound_exec (τ := τ) ((hr.scratch fi).scratch fg)
      (show u.mem (r 3) = z by simpa only [Nat.one_mul] using pow) term (loop.post (init.post fit))
      ((Nat.size_le_size (by omega : rem-z+1 ≤ 2*x+2)).trans wx) sumWidth
    have shrink := size_lt_of_double_lt (show 2*(rem-z) < rem by change 2*(rem-2^k) < rem; omega)
    obtain ⟨t,j,tail,hj,answer,out,frame⟩ := ih (rem-z) (q+y*z) _ hnext (by omega) law' (by omega)
      (finish.post (loop.post (init.post fit)))
    have go : ¬s.mem (r 0) ≤ s.mem (r 7) := by rw [hr.remReg,hr.zero]; omega
    have cost := hk.trans (Nat.size_le_size hx)
    refine ⟨t,_,.again go (init.seq (loop.seq finish)) tail,?_,answer,out.trans (ofin.trans (og.trans oi)),?_⟩
    · rw [Nat.succ_mul fuel (5*x.size+9)]; omega
    · intro a free
      exact (frame a free).trans ((ff a free).trans ((fg a (free 3) (free 4) (free 5)).trans (fi a (free 3) (free 4) (free 5))))

/-- Multiply two arbitrary words on the addition-only logarithmic-cost RAM. Register 2
receives the exact product; the step count is quadratic in the bit length of the first
operand, including zero. No loop runs once per unit of an exponential operand. -/
theorem multiply_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b : ℕ} (x y : ℕ) (s : Store)
    (inX : s.mem (r 0) = x) (inY : s.mem (r 1) = y) (fit : s.Fits b) (hb : 2 ≤ b)
    (wx : (2*x+2).size ≤ b) (wp : (x*y).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (multiply r) s t j ∧ j ≤ x.size*(5*x.size+9)+5 ∧
      t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  obtain ⟨init,regs,out,save⟩ := initDiv_exec (τ := τ) r x y s inX inY fit (by omega)
    ((Nat.size_le_size (by omega : x+1 ≤ 2*x+2)).trans wx)
  obtain ⟨t,j,loop,cost,correct,ret,frame⟩ := multiplyLoop_exec r x y hb wx wp x.size x 0 _ regs le_rfl
    (by simp) le_rfl (init.post fit)
  exact ⟨t,_,init.seq loop,by omega,correct,ret.trans out,fun a free => (frame a free).trans (save a free)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMMultiply

section LogCostRAMPower

namespace TargetedSamplers.Structured.Word

private structure PowerState (r : Fin 13 ↪ ℕ) (s : Store) (x e a : ℕ) : Prop where
  base : s.mem (r 9) = x
  count : s.mem (r 10) = e
  result : s.mem (r 2) = a
  zero : s.mem (r 11) = 0
  one : s.mem (r 12) = 1

private theorem powerLoop_exec {τ : TargetedSamplers.Tapes} (r : Fin 13 ↪ ℕ) {b : ℕ} (x e a : ℕ)
    (s : Store) (h : PowerState r s x e a) (fit : s.Fits b) (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b)
    (finalWidth : (a*x^e).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (powerLoop r) s t j ∧ j ≤ e*(x.size*(5*x.size+9)+10)+1 ∧
      t.mem (r 2) = a*x^e ∧ t.out = s.out ∧ ∀ v, (∀ i, v ≠ r i) → t.mem v = s.mem v := by
  have eq (i j : Fin 13) : r i = r j ↔ i=j := r.injective.eq_iff
  have ne {i j : Fin 13} (hne : i ≠ j) := r.injective.ne hne
  induction e generalizing s a with
  | zero =>
    exact ⟨s,1,.done (by rw [h.count,h.zero]),by simp,by simpa using h.result,rfl,fun _ _ => rfl⟩
  | succ e ih =>
    let u := ((powerOperands r).run τ s).last
    have xw := h.base ▸ fit (r 9)
    have aw := h.result ▸ fit (r 2)
    have safe : ((powerOperands r).run τ s).writeWidth ≤ b := by
      simp [powerOperands,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,h.base,h.result,h.zero,xw,aw]
    have setup := (powerOperands r).exec τ s b fit safe
    have xarg : u.mem (r 0) = x := by simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.base,h.zero]
    have aarg : u.mem (r 1) = a := by simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.result,h.zero]
    have old (v : ℕ) (h₀ : v ≠ r 0) (h₁ : v ≠ r 1) : u.mem v = s.mem v := by
      simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,h₀,h₁]
    have step : x ≤ x^(e+1) := by
      by_cases z : x=0
      · simp [z]
      · simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by omega : 1 ≤ e+1)
    have part : x*a ≤ a*x^(e+1) := by simpa only [Nat.mul_comm x a] using Nat.mul_le_mul_left a step
    obtain ⟨v,k,mul,hk,product,out,fr⟩ := multiply_exec (τ := τ) (powerMulRegs r) x a u xarg aarg
      (setup.post fit) hb wx ((Nat.size_le_size part).trans finalWidth)
    have keep (i : Fin 13) (large : 9 ≤ i.val) : v.mem (r i) = s.mem (r i) := by
      have diff (j : Fin 13) (hj : j.val < 9) : i ≠ j := by intro he; subst j; omega
      have outside (j : Fin 9) : r i ≠ powerMulRegs r j := by
        intro he
        have same := congrArg (fun u : Fin 13 => u.val) (r.injective he)
        change i.val = j.val at same; have := j.isLt; omega
      exact (fr _ outside).trans (old _ (ne (diff 0 (by decide))) (ne (diff 1 (by decide))))
    let w := v.write (r 10) e
    have update : (Op.sub (r 10) (r 10) (r 12)).eval τ v = w := by
      simp [Op.eval,w,(keep 10 (by decide)).trans h.count,(keep 12 (by decide)).trans h.one]
    have countWidth : (e+1).size ≤ b := by rw [← h.count]; exact fit (r 10)
    have fw := Store.write_fits (mul.post (setup.post fit)) (r 10)
      ((Nat.size_le_size (Nat.le_succ e)).trans countWidth)
    have dec : Exec τ (fun v => v.Fits b) (.op (.sub (r 10) (r 10) (r 12))) v w 1 := by
      simpa only [update] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) v (.sub (r 10) (r 10) (r 12)) (by rwa [update]))
    change v.mem (r 2) = x*a at product
    have next : PowerState r w x e (x*a) := by
      constructor <;> simp [w,Store.write,eq,keep 9 (by decide),keep 11 (by decide),keep 12 (by decide),
        h.base,h.zero,h.one,product]
    have total : x*a*x^e = a*x^(e+1) := by rw [pow_succ]; ring
    obtain ⟨t,j,loop,hj,last,ret,save⟩ := ih (x*a) w next fw (by rwa [total])
    have go : ¬s.mem (r 10) ≤ s.mem (r 11) := by rw [h.count,h.zero]; omega
    have setupSteps : ((powerOperands r).run τ s).steps = 2 := rfl
    refine ⟨t,_,.again go (setup.seq (mul.seq dec)) loop,?_,last.trans total,ret.trans out,?_⟩
    · rw [Nat.succ_mul e (x.size*(5*x.size+9)+10)]; omega
    · intro v' free
      have outside (j : Fin 9) : v' ≠ powerMulRegs r j := free ⟨j.val,by have := j.isLt; omega⟩
      exact (save _ free).trans ((show w.mem v' = v.mem v' by simp [w,Store.write,free]).trans
        ((fr v' outside).trans (old _ (free 0) (free 1))))

/-- Raise a word to an input exponent by counted multiplication. The loop count is the
exponent itself, and each iteration costs a polynomial in the base's bit length. -/
theorem power_exec {τ : TargetedSamplers.Tapes} (r : Fin 13 ↪ ℕ) {b : ℕ} (x e : ℕ) (s : Store)
    (base : s.mem (r 9) = x) (exponent : s.mem (r 10) = e) (fit : s.Fits b) (hb : 2 ≤ b)
    (wx : (2*x+2).size ≤ b) (wp : (x^e).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (power r) s t j ∧ j ≤ e*(x.size*(5*x.size+9)+10)+4 ∧
      t.mem (r 2) = x^e ∧ t.out = s.out ∧ ∀ v, (∀ i, v ≠ r i) → t.mem v = s.mem v := by
  have eq (i j : Fin 13) : r i = r j ↔ i=j := r.injective.eq_iff
  let u := ((initPower r).run τ s).last
  have safe : ((initPower r).run τ s).writeWidth ≤ b := by
    simp [initPower,Structured.sequence,Fragment.run,Op.written]; omega
  have init := (initPower r).exec τ s b fit safe
  have regs : PowerState r u x e 1 := by
    constructor <;> simp [u,initPower,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,base,exponent]
  obtain ⟨t,j,loop,hj,last,ret,fr⟩ := powerLoop_exec (τ := τ) r x e 1 u regs (init.post fit) hb wx (by simpa using wp)
  have count : ((initPower r).run τ s).steps = 3 := rfl
  refine ⟨t,_,init.seq loop,by omega,by simpa using last,ret,?_⟩
  intro v free
  simpa [u,initPower,Structured.sequence,Fragment.run,Op.eval,Store.write,free] using fr v free

end TargetedSamplers.Structured.Word

end LogCostRAMPower

section LogCostRAMArithmetic

namespace TargetedSamplers.Structured.Word

theorem size_twice_add_two (x : ℕ) : (2*x+2).size ≤ x.size+2 := by
  apply Nat.size_le.mpr
  have scale : 2^(x.size+2) = 4*2^x.size := by rw [pow_add]; ring
  rw [scale]
  have := Nat.lt_size_self x; omega

def Arithmetic.steps : Arithmetic → ℕ → ℕ → ℕ
  | .mul, x, _ => x.size*(5*x.size+9)+5
  | .div, x, _ | .mod, x, _ => x.size*(5*x.size+9)+7
  | .pow, x, y => y*(x.size*(5*x.size+9)+10)+4

private theorem Arithmetic.native_exec {τ : TargetedSamplers.Tapes} (op : Arithmetic) {b : ℕ}
    (x y : ℕ) (s : Store) (left : s.mem op.leftReg = x) (right : s.mem op.rightReg = y)
    (fit : s.Fits b) (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b) (wy : (op.value x y).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) op.native s t j ∧ j ≤ op.steps x y ∧
      t.mem op.outReg = op.value x y ∧ t.out = s.out ∧ ∀ a, 13 ≤ a → t.mem a = s.mem a := by
  have outside (n : ℕ) (hn : n ≤ 13) (a : ℕ) (ha : 13 ≤ a) (i : Fin n) : a ≠ Fin.valEmbedding i := by
    change a ≠ i.val; have := i.isLt; omega
  cases op with
  | mul =>
    obtain ⟨t,j,ex,hj,ans,out,fr⟩ := multiply_exec (τ := τ) Fin.valEmbedding x y s left right fit hb wx wy
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | div =>
    obtain ⟨t,j,ex,hj,_,ans,out,fr⟩ := divMod_exec (τ := τ) Fin.valEmbedding x y s left right fit (by omega) wx
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | mod =>
    obtain ⟨t,j,ex,hj,ans,_,out,fr⟩ := divMod_exec (τ := τ) Fin.valEmbedding x y s left right fit (by omega) wx
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | pow =>
    obtain ⟨t,j,ex,hj,ans,out,fr⟩ := power_exec (τ := τ) Fin.valEmbedding x y s left right fit hb wx wy
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 13 le_rfl a ha)⟩

private theorem loadArgs_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (p q l r : ℕ) (s : Store)
    (hp : p < 13) (hq : q < 13) (ne : p ≠ q) (fit : s.Fits b) :
    let t := ((loadArgs p q l r).run τ s).last
    Exec τ (fun u => u.Fits b) (loadArgs p q l r).cmd s t 3 ∧ t.mem p = s.mem (cell l) ∧
      t.mem q = s.mem (cell r) ∧ t.mem 13 = 0 ∧ t.out = s.out ∧ ∀ i, t.mem (cell i) = s.mem (cell i) := by
  have far (i v : ℕ) (h : v ≤ 13) : cell i ≠ v := by dsimp [cell]; omega
  have z : 13 ≠ p := by omega
  have safe : ((loadArgs p q l r).run τ s).writeWidth ≤ b := by
    simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,far l 13 le_rfl,far r 13 le_rfl,
      far r p hp.le,z,fit (cell l),fit (cell r)]
  refine ⟨(loadArgs p q l r).exec τ s b fit safe,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro i; simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,far i p hp.le,far i q hq.le,far i 13 le_rfl])
    | simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,ne,far l 13 le_rfl,far r 13 le_rfl,
        far r p hp.le,z,show 13 ≠ q by omega]

theorem Arithmetic.call_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (op : Arithmetic) (d l r : ℕ) (s : Store)
    (fit : s.Fits b) (hb : 2 ≤ b) :
    let x := s.mem (cell l)
    let y := s.mem (cell r)
    (2*x+2).size ≤ b → (op.value x y).size ≤ b →
    ∃ t j, Exec τ (fun u => u.Fits b) (op.call d l r) s t j ∧ j ≤ op.steps x y+4 ∧ t.out = s.out ∧
      ∀ i, t.mem (cell i) = if i=d then op.value x y else s.mem (cell i) := by
  intro x y wx wy
  obtain ⟨load,left,right,zero,out₀,fr₀⟩ := loadArgs_exec (τ := τ) op.leftReg op.rightReg l r s
    (by cases op <;> decide) (by cases op <;> decide) (by cases op <;> decide) fit
  obtain ⟨v,j,run,hj,value,out,fr⟩ := op.native_exec (τ := τ) x y _ left right (load.post fit) hb wx wy
  let t := v.write (cell d) (op.value x y)
  have put : (Op.add (cell d) op.outReg 13).eval τ v = t := by simp [Op.eval,t,value,(fr 13 le_rfl).trans zero]
  have write : Exec τ (fun u => u.Fits b) (.op (.add (cell d) op.outReg 13)) v t 1 := by
    simpa only [put] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) v (.add (cell d) op.outReg 13)
      (by rw [put]; exact Store.write_fits (run.post (load.post fit)) _ wy))
  refine ⟨t,_,load.seq (run.seq write),by omega,out.trans out₀,?_⟩
  intro i
  by_cases eq : i=d
  · subst i; simp [t,Store.write]
  · have ne : cell i ≠ cell d := by simpa [cell] using eq
    simp [t,Store.write,ne,eq,(fr (cell i) (by dsimp [cell]; omega)).trans (fr₀ i)]

end TargetedSamplers.Structured.Word

end LogCostRAMArithmetic

section LogCostRAMArithmeticCircuit

namespace TargetedSamplers.Structured.Word

def Expression.steps (v : ℕ → ℕ) : Expression → ℕ
  | .arithmetic op l r => op.steps (v l) (v r)+4
  | _ => 1

def Expression.width (v : ℕ → ℕ) (e : Expression) : ℕ :=
  match e with
  | .arithmetic _ l _ => max (2*v l+2).size (e.eval v).size
  | _ => (e.eval v).size

/-- The only arithmetic loop counted in the numerical value of an operand is a power's
exponent. The other primitives have cost polynomial in word width. -/
def Expression.multiplicity (v : ℕ → ℕ) : Expression → ℕ
  | .arithmetic .pow _ r => v r+1
  | _ => 1

theorem Expression.steps_le (e : Expression) (v : ℕ → ℕ) (b : ℕ) (h : e.width v ≤ b) :
    e.steps v ≤ e.multiplicity v*(b*(5*b+9)+15) := by
  cases e with
  | literal | add | sub => simp [steps,multiplicity]
  | arithmetic op l r =>
    have wl := (max_le_iff.mp h).1
    have le := (Nat.size_le_size (show v l ≤ 2*v l+2 by omega)).trans wl
    have quad := Nat.mul_le_mul le (show 5*(v l).size+9 ≤ 5*b+9 by omega)
    cases op with
    | mul | div | mod => simp [steps,multiplicity,Arithmetic.steps]; omega
    | pow =>
      simp only [steps,multiplicity,Arithmetic.steps,Nat.succ_mul (v r) (b*(5*b+9)+15)]
      have := Nat.mul_le_mul_left (v r) (show (v l).size*(5*(v l).size+9)+10 ≤ b*(5*b+9)+15 by omega)
      omega

def Assignment.update (a : Assignment) (v : ℕ → ℕ) := Function.update v a.dst (a.rhs.eval v)

def Represents (s : Store) (v : ℕ → ℕ) : Prop := ∀ i, s.mem (cell i) = v i

theorem Assignment.exec {τ : TargetedSamplers.Tapes} {b : ℕ} (a : Assignment) (v : ℕ → ℕ) (s : Store)
    (h : Represents s v) (fit : s.Fits b) (hb : 2 ≤ b) (width : a.rhs.width v ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) a.cmd s t j ∧ j ≤ a.rhs.steps v ∧ Represents t (a.update v) ∧ t.out = s.out := by
  obtain ⟨d,e⟩ := a
  have simple (op : Op) (z : ℕ) (ev : op.eval τ s = s.write (cell d) z) (wz : z.size ≤ b) :
      let t := s.write (cell d) z
      Exec τ (fun u => u.Fits b) (.op op) s t 1 ∧ Represents t (Function.update v d z) ∧ t.out = s.out := by
    refine ⟨?_,?_,rfl⟩
    · simpa only [ev] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s op (by rw [ev]; exact Store.write_fits fit _ wz))
    · intro i
      by_cases eq : i=d
      · subst i; simp [Store.write]
      · have dif : cell i ≠ cell d := by simpa [cell] using eq
        simpa [Store.write,Function.update_of_ne eq,Function.update_of_ne dif] using h i
  cases e with
  | literal x =>
    obtain ⟨ex,post,out⟩ := simple (.const (cell d) x) x rfl width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | add l r =>
    obtain ⟨ex,post,out⟩ := simple (.add (cell d) (cell l) (cell r)) (v l+v r) (by simp [Op.eval,h l,h r]) width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | sub l r =>
    obtain ⟨ex,post,out⟩ := simple (.sub (cell d) (cell l) (cell r)) (v l-v r) (by simp [Op.eval,h l,h r]) width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | arithmetic op l r =>
    change max (2*v l+2).size (op.value (v l) (v r)).size ≤ b at width
    obtain ⟨wl,wr⟩ := max_le_iff.mp width
    obtain ⟨t,j,ex,work,out,regs⟩ := op.call_exec (τ := τ) d l r s fit hb (by rwa [h l]) (by rwa [h l,h r])
    refine ⟨t,j,ex,by simpa only [Expression.steps,h l,h r] using work,?_,out⟩
    intro i
    by_cases eq : i=d
    · subst i; simpa [Assignment.update,Expression.eval,h l,h r] using regs d
    · simpa [Assignment.update,Expression.eval,Function.update_of_ne eq,eq,h i] using regs i

namespace Circuit

def result (v : ℕ → ℕ) : List Assignment → (ℕ → ℕ)
  | [] => v
  | a::as => result (a.update v) as

def steps (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => a.rhs.steps v + steps (a.update v) as

def width (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => max (a.rhs.width v) (width (a.update v) as)

def multiplicity (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => a.rhs.multiplicity v + multiplicity (a.update v) as

theorem steps_le (as : List Assignment) (v : ℕ → ℕ) (b : ℕ) (h : width v as ≤ b) :
    steps v as ≤ multiplicity v as*(b*(5*b+9)+15) := by
  induction as generalizing v with
  | nil => simp [steps,multiplicity]
  | cons a as ih =>
    obtain ⟨first,rest⟩ := max_le_iff.mp h
    simpa only [steps,multiplicity,Nat.add_mul] using Nat.add_le_add (a.rhs.steps_le v b first) (ih (a.update v) rest)

theorem result_untouched (as : List Assignment) (v : ℕ → ℕ) (i : ℕ) (free : ∀ a ∈ as, i ≠ a.dst) :
    result v as i = v i := by
  induction as generalizing v with
  | nil => rfl
  | cons a as ih =>
    rw [result,ih (a.update v) (fun x hx => free x (List.mem_cons_of_mem _ hx))]
    exact Function.update_of_ne (free a (by simp)) _ _

/-- A finite arithmetic circuit is a fixed program on the public RAM. Its bound is a
sum of the individual operation costs, and its width accounts for their intermediates. -/
theorem exec {τ : TargetedSamplers.Tapes} {b : ℕ} (as : List Assignment) (v : ℕ → ℕ) (s : Store)
    (repr : Represents s v) (fit : s.Fits b) (hb : 2 ≤ b) (bound : width v as ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (cmd as) s t j ∧ j ≤ steps v as ∧ Represents t (result v as) ∧ t.out = s.out := by
  induction as generalizing v s with
  | nil => exact ⟨s,0,.skip s,le_rfl,repr,rfl⟩
  | cons a as ih =>
    obtain ⟨first,later⟩ := max_le_iff.mp bound
    obtain ⟨u,i,run,hi,rep,out⟩ := a.exec (τ := τ) v s repr fit hb first
    obtain ⟨t,j,tail,hj,final,ret⟩ := ih (a.update v) u rep (run.post fit) later
    exact ⟨t,_,run.seq tail,Nat.add_le_add hi hj,final,ret.trans out⟩

end Circuit

end TargetedSamplers.Structured.Word

end LogCostRAMArithmeticCircuit

section PackedBinaryStacks

namespace TargetedSamplers.Structured.BinaryStack

open Word

@[simp] theorem packed_nil : packed [] = 1 := rfl

theorem packed_cons (b : Bool) (xs : List Bool) : packed (b::xs) = packed xs+packed xs+b.toNat := by
  cases b <;> simp [packed,Nat.bit,two_mul]

theorem packed_pos (xs : List Bool) : 0 < packed xs := by
  induction xs with
  | nil => decide
  | cons b xs ih => rw [packed_cons]; omega

@[simp] theorem packed_size (xs : List Bool) : (packed xs).size = xs.length+1 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    change (Nat.bit b (packed xs)).size = _
    rw [Nat.size_bit (Nat.ne_of_gt (packed_pos (b::xs))),ih,List.length_cons]

def headSymbol : List Bool → ℕ
  | [] => 0
  | b::_ => 1+b.toNat

def headOfWord (x : ℕ) := if x ≤ 1 then 0 else x-(x/2+x/2)+1

theorem headOfWord_packed (xs : List Bool) : headOfWord (packed xs) = headSymbol xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    have pos := packed_pos xs
    rw [headOfWord,packed_cons,if_neg (show ¬ packed xs+packed xs+b.toNat ≤ 1 by omega)]
    cases b <;> simp only [headSymbol,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem tail_of_packed {xs : List Bool} (nonempty : xs ≠ []) : packed xs / 2 = packed xs.tail := by
  cases xs with
  | nil => contradiction
  | cons b xs => cases b <;> simp [packed_cons] <;> omega

/-- The three fixed constants used by the stack and finite-control instructions. -/
structure Constants (s : Store) : Prop where
  one : s.mem (cell 1) = 1
  two : s.mem (cell 2) = 2
  zero : s.mem (cell 5) = 0

theorem push_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (k : ℕ) (hk : 8 ≤ k) (bit : Bool)
    (xs : List Bool) (s : Store) (c : Constants s) (v : s.mem (cell k) = packed xs) (fit : s.Fits b)
    (room : xs.length+2 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (push k bit) s t j ∧ j ≤ 2 ∧
      t.mem (cell k) = packed (bit::xs) ∧ t.out = s.out ∧ ∀ a, a ≠ cell k → t.mem a = s.mem a := by
  let x := packed xs
  let u := s.write (cell k) (x+x)
  have ev : (Op.add (cell k) (cell k) (cell k)).eval τ s = u := by simp [Op.eval,u,x,v]
  have size : (x+x).size ≤ b := by
    have e : x+x = packed (false::xs) := by simp [packed_cons,x]
    rw [e,packed_size,List.length_cons]; omega
  have fu := Store.write_fits fit (cell k) size
  have first : Exec τ (fun st => st.Fits b) (.op (.add (cell k) (cell k) (cell k))) s u 1 := by
    simpa only [ev] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.add (cell k) (cell k) (cell k)) (by rw [ev]; exact fu))
  cases bit with
  | false => exact ⟨u,1,first,by decide,by simp [u,Store.write,packed_cons,x],rfl,fun a h => by simp [u,Store.write,h]⟩
  | true =>
    have diff : cell 1 ≠ cell k := by simp [cell]; omega
    have e : (Op.add (cell k) (cell k) (cell 1)).eval τ u = u.write (cell k) (packed (true::xs)) := by
      simp [Op.eval,u,Store.write,diff,c.one,packed_cons,x]
    have second := Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.add (cell k) (cell k) (cell 1))
      (by rw [e]; exact Store.write_fits fu _ (by rw [packed_size,List.length_cons]; omega))
    exact ⟨_,2,first.seq second,le_rfl,by rw [e]; simp [Store.write],rfl,
      fun a h => by rw [e]; simp [u,Store.write,h]⟩

private def cut (k : ℕ) (remove : Bool) : List Assignment :=
  [⟨4,.arithmetic .div k 2⟩,⟨3,.add 4 4⟩,⟨6,.sub k 3⟩,⟨6,.add 6 1⟩] ++
    (if remove then [⟨k,.add 4 5⟩] else [])

def inspect (k : ℕ) (remove : Bool) : Cmd := .branch (cell k) (cell 1)
  (.op (.const (cell 6) 0)) (Circuit.cmd (cut k remove))

/-- Inspect a stack's top symbol and optionally pop it. Arbitrarily long stacks use
binary division on an explicitly bounded word, with no unit-cost division instruction. -/
theorem inspect_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (k : ℕ) (hk : 8 ≤ k) (remove : Bool)
    (xs : List Bool) (s : Store) (c : Constants s) (v : s.mem (cell k) = packed xs) (fit : s.Fits b)
    (room : xs.length+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (inspect k remove) s t j ∧ j ≤ 5*(b*(5*b+9)+15)+2 ∧
      t.mem (cell 6) = headSymbol xs ∧ t.mem (cell k) = packed (if remove then xs.tail else xs) ∧ t.out = s.out ∧
      ∀ i, i ≠ k → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.mem (cell i) = s.mem (cell i) := by
  by_cases nil : xs = []
  · subst xs
    have ex := Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.const (cell 6) 0) (Store.write_fits fit _ (by simp))
    refine ⟨_,_,Exec.yes (n := Circuit.cmd (cut k remove)) (by rw [v,c.one]; decide) ex,by omega,?_,?_,rfl,?_⟩
    · simp [Op.eval,Store.write,headSymbol]
    · have diff : cell k ≠ cell 6 := by simp [cell]; omega
      cases remove <;> simp [Op.eval,Store.write,diff,v]
    · intro i _ _ _ hi
      have neq : cell i ≠ cell 6 := by dsimp [cell]; omega
      simp [Op.eval,Store.write,neq]
  · let vals := fun i => s.mem (cell i)
    let x := packed xs
    have vx : vals k = x := v
    have c₁ : vals 1 = 1 := c.one
    have c₂ : vals 2 = 2 := c.two
    have c₅ : vals 5 = 0 := c.zero
    have notSmall : 1 < x := by
      cases xs with
      | nil => contradiction
      | cons bit bs =>
        change 1 < packed (bit::bs)
        rw [packed_cons]; have := packed_pos bs; omega
    have dif (i : ℕ) (hi : i < 8) : k ≠ i := by omega
    have rev (i : ℕ) (hi : i < 8) : i ≠ k := by omega
    have wx : x.size+2 ≤ b := by simpa [x] using room
    have xx := (size_twice_add_two x).trans wx
    have half : (x/2).size ≤ b := (Nat.size_le_size (Nat.div_le_self _ _)).trans (by omega)
    have twice : (x/2+x/2).size ≤ b := (Nat.size_le_size (show x/2+x/2 ≤ x by omega)).trans (by omega)
    have rem : (x-(x/2+x/2)).size ≤ b := (Nat.size_le_size (Nat.sub_le _ _)).trans (by omega)
    have out : (x-(x/2+x/2)+1).size ≤ b := (Nat.size_le_size (show x-(x/2+x/2)+1 ≤ 2 by omega)).trans
      (show (2:ℕ).size ≤ b by change 2 ≤ b; omega)
    have width : Circuit.width vals (cut k remove) ≤ b := by
      cases remove <;> simp (disch := decide) [cut,Circuit.width,Assignment.update,Expression.width,Expression.eval,
        Arithmetic.value,Function.update_apply,dif,rev,vx,c₁,c₂,c₅,xx,half,twice,rem,out]
    obtain ⟨t,j,run,work,regs,hout⟩ := Circuit.exec (τ := τ) (cut k remove) vals s (fun _ => rfl) fit (by omega) width
    have wt := Circuit.steps_le (cut k remove) vals b width
    have count : Circuit.multiplicity vals (cut k remove) ≤ 5 := by
      cases remove <;> norm_num [cut,Circuit.multiplicity,Expression.multiplicity]
    have time := Nat.mul_le_mul_right (b*(5*b+9)+15) count
    have output : Circuit.result vals (cut k remove) 6 = headOfWord x := by
      cases remove <;> simp (disch := decide) [cut,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,
        dif,rev,vx,c₁,c₂,c₅,headOfWord,show ¬x ≤ 1 by omega]
    have stack : Circuit.result vals (cut k remove) k = (if remove then x/2 else x) := by
      cases remove <;> simp (disch := decide) [cut,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,
        dif,rev,vx,c₁,c₂,c₅]
    have unchanged (i : ℕ) (hi : i ≠ k) (h₃ : i ≠ 3) (h₄ : i ≠ 4) (h₆ : i ≠ 6) :
        t.mem (cell i) = s.mem (cell i) := by
      apply (regs i).trans
      apply Circuit.result_untouched
      cases remove <;> simp [cut,hi,h₃,h₄,h₆]
    refine ⟨t,_,Exec.no (y := .op (.const (cell 6) 0)) (by rw [v,c.one]; exact Nat.not_le_of_gt notSmall) run,
      by omega,(regs 6).trans (output.trans (headOfWord_packed xs)),?_,hout,unchanged⟩
    rw [regs k,stack]; cases remove <;> simp [x,tail_of_packed nil]

end TargetedSamplers.Structured.BinaryStack

end PackedBinaryStacks

namespace DirectedHamiltonicity.Main.CycleReduction.OuterMachine

open TargetedSamplers TargetedSamplers.Structured Word BinaryStack

def pushPort : Code := .seq (.pure (inspect 8 true)) <|
  .seq (.pure (.op (.sub (cell 6) (cell 6) (cell 1)))) <|
  .seq (.port (cell 9) (cell 6)) (.pure (.op (.add (cell 9) (cell 9) (cell 1))))

def loadLoop := Code.loop (cell 8) (cell 1) pushPort
def loadUnit (w : ℕ) := 5*(w*(5*w+9)+15)+10

structure Loaded (d t : Data) (xs : List Bool) (start : ℕ) : Prop where
  cursor : t.bank.mem (cell 9)=start+xs.length
  stack : t.bank.mem (cell 8)=1
  output : t.bank.out=d.bank.out
  epoch : t.epoch=d.epoch
  high : ∀ i, 10 ≤ i → t.bank.mem (cell i)=d.bank.mem (cell i)
  range : ∀ i (hi : i<xs.length), t.port (start+i)=(xs[i]).toNat
  frame : ∀ i, i<start ∨ start+xs.length ≤ i → t.port i=d.port i

theorem load_loop (Q : Program) (τ : Tapes) (w : ℕ) (xs : List Bool) (start : ℕ) (d : Data)
    (stack : d.bank.mem (cell 8)=packed xs) (ptr : d.bank.mem (cell 9)=start) (c : Constants d.bank)
    (fit : d.bank.Fits w) (room : xs.length+3 ≤ w) (total : (start+xs.length).size ≤ w) :
    ∃ t j, Eval Q τ w loadLoop d t j ∧ j ≤ (xs.length+1)*loadUnit w ∧ t.bank.Fits w ∧ Loaded d t xs start := by
  induction xs generalizing start d with
  | nil =>
    have stop : d.bank.mem (cell 8) ≤ d.bank.mem (cell 1) := by rw [stack,c.one];decide
    refine ⟨d,1,.done fit stop,by simp [loadUnit],fit,by simpa using ptr,by simpa using stack,rfl,rfl,
      fun _ _ => rfl,fun i hi => by simp at hi,fun _ _ => rfl⟩
  | cons b xs ih =>
    have top : ¬d.bank.mem (cell 8) ≤ d.bank.mem (cell 1) := by
      rw [stack,c.one,packed_cons];have := packed_pos xs;omega
    obtain ⟨z,k,read,step,bit,tail,out,frame⟩ := inspect_exec (τ:=τ) 8 (by decide) true (b::xs) d.bank c stack fit room
    let u : Data := {d with bank := z}
    have r1 : Eval Q τ w (.pure (inspect 8 true)) d u k := .pure fit read
    have ufit := read.post fit
    change z.mem (cell 6)=1+b.toNat at bit
    change z.mem (cell 8)=packed xs at tail
    have keep (i : ℕ) (hi : i≠8) (h3 : i≠3) (h4 : i≠4) (h6 : i≠6) := frame i hi h3 h4 h6
    have z1 : z.mem (cell 1)=1 := (keep 1 (by decide) (by decide) (by decide) (by decide)).trans c.one
    have z2 := (keep 2 (by decide) (by decide) (by decide) (by decide)).trans c.two
    have z5 := (keep 5 (by decide) (by decide) (by decide) (by decide)).trans c.zero
    have z9 : z.mem (cell 9)=start := (keep 9 (by decide) (by decide) (by decide) (by decide)).trans ptr
    let z' := z.write (cell 6) b.toNat
    let u' : Data := {u with bank := z'}
    have bw : b.toNat.size ≤ w := by cases b <;> change _ ≤ w <;> simp [Bool.toNat] <;> omega
    have zfit : z'.Fits w := Store.write_fits ufit _ bw
    have ez : (Op.sub (cell 6) (cell 6) (cell 1)).eval τ z=z' := by simp [Op.eval,z',bit,z1]
    have sub : Exec τ (fun v => v.Fits w) (.op (.sub (cell 6) (cell 6) (cell 1))) z z' 1 := by
      rw [←ez];exact .op _ _ (ez.symm ▸ zfit)
    have r2 : Eval Q τ w (.pure (.op (.sub (cell 6) (cell 6) (cell 1)))) u u' 1 := .pure ufit sub
    let p := u'.publish (cell 9) (cell 6)
    have r3 : Eval Q τ w (.port (cell 9) (cell 6)) u' p 1 := .port _ _ _ zfit
    have port : p.port=Function.update d.port start b.toNat := by simp [p,Data.publish,u',u,z',Store.write,show cell 9≠cell 6 by decide,z9]
    let z'' := z'.write (cell 9) (start+1)
    let v : Data := {p with bank := z''}
    have sw : (start+1).size ≤ w := (Nat.size_le_size (by simp : start+1 ≤ start+(b::xs).length)).trans total
    have vfit : v.bank.Fits w := Store.write_fits zfit _ sw
    have einc : (Op.add (cell 9) (cell 9) (cell 1)).eval τ z'=z'' := by simp [Op.eval,z'',z',Store.write,cell] at z9 z1 ⊢;rw [z9,z1]
    have add : Exec τ (fun v => v.Fits w) (.op (.add (cell 9) (cell 9) (cell 1))) z' z'' 1 := by
      rw [←einc];exact .op _ _ (einc.symm ▸ vfit)
    have r4 : Eval Q τ w (.pure (.op (.add (cell 9) (cell 9) (cell 1)))) p v 1 := .pure zfit add
    have body : Eval Q τ w pushPort d v (k+(1+(1+1))) := r1.seq (r2.seq (r3.seq r4))
    have unchanged (i : ℕ) (h9 : i≠9) (h6 : i≠6) : v.bank.mem (cell i)=z.mem (cell i) := by
      simp [v,z'',z',Store.write,show cell i≠cell 9 by unfold cell;omega,show cell i≠cell 6 by unfold cell;omega]
    have v0 : Constants v.bank := ⟨(unchanged 1 (by decide) (by decide)).trans z1,
      (unchanged 2 (by decide) (by decide)).trans z2,(unchanged 5 (by decide) (by decide)).trans z5⟩
    have cursor : v.bank.mem (cell 9)=start+1 := by simp [v,z'',Store.write]
    have vslot : v.bank.mem (cell 8)=packed xs := (unchanged 8 (by decide) (by decide)).trans tail
    have size : (start+1+xs.length).size ≤ w := by simpa [Nat.add_assoc,Nat.add_comm 1] using total
    obtain ⟨t,l,rest,steps,doneFit,info⟩ := ih (start+1) v vslot cursor v0 vfit (by simp at room;omega) size
    refine ⟨t,_,.again fit top body rest,?_,doneFit,?_,info.stack,info.output.trans out,info.epoch,?_,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul];have per : 1+(k+(1+(1+1)))+1 ≤ loadUnit w := by unfold loadUnit;omega
      omega
    · rw [info.cursor,List.length_cons];omega
    · intro i hi
      exact (info.high i hi).trans ((unchanged i (by omega) (by omega)).trans (keep i (by omega) (by omega) (by omega) (by omega)))
    · intro i hi
      cases i with
      | zero =>
        have retained := info.frame start (Or.inl (by omega))
        change t.port start=p.port start at retained
        simpa [port] using retained
      | succ i =>
        have index : start+(i+1)=start+1+i := by omega
        simpa only [index,List.getElem_cons_succ] using info.range i (by simpa using hi)
    · intro i hi
      have pass : i<start+1 ∨ start+1+xs.length ≤ i := by simp at hi;omega
      have retained := info.frame i pass
      change t.port i=p.port i at retained
      rw [port,Function.update_of_ne (by simp at hi;omega : i≠start)] at retained
      exact retained

end DirectedHamiltonicity.Main.CycleReduction.OuterMachine

namespace DirectedHamiltonicity.Main.CycleReduction.TapeReader

open TargetedSamplers TargetedSamplers.Structured FiniteSampling
open scoped BigOperators

inductive Port | input | coin

def Port.read (port : Port) (dst addr : ℕ) : Op :=
  match port with | .input => .input dst addr | .coin => .coin dst addr

def Port.tape (port : Port) (τ : Tapes) : List Bool :=
  match port with | .input => τ.input | .coin => τ.coins

@[simp] theorem read_eval (p : Port) (d a : ℕ) (τ : Tapes) (s : Store) :
    (p.read d a).eval τ s = s.write d (bitVal (p.tape τ)[s.mem a]?) := by cases p <;> rfl
@[simp] theorem read_written (p : Port) (d a : ℕ) (τ : Tapes) (s : Store) :
    (p.read d a).written τ s = bitVal (p.tape τ)[s.mem a]? := by cases p <;> rfl

/-- Read little-endian bits. Missing cells of a short tape have value zero. -/
def value (coins : List Bool) (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => value coins base k + (coins[base+k]?.getD false).toNat * 2^k

/-- Registers hold a descending cursor, its lower endpoint, one, the read symbol and the accumulator. -/
def digit (port : Port) (r : Fin 5 ↪ ℕ) : Fragment := Structured.sequence [
  .op (.sub (r 0) (r 0) (r 2)),.op (port.read (r 3) (r 0)),.op (.add (r 4) (r 4) (r 4)),
  .branch (r 3) (r 2) (.branch (r 2) (r 3) (.op (.add (r 4) (r 4) (r 2))) .skip) .skip]

def loop (port : Port) (r : Fin 5 ↪ ℕ) : Cmd := .whileGt (r 0) (r 1) (digit port r).cmd

private theorem digit_exec (port : Port) {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (p v : ℕ)
    (pos : s.mem (r 0) = p+1) (one : s.mem (r 2) = 1) (acc : s.mem (r 4) = v)
    (fit : s.Fits width) (hb : 2 ≤ width) (w : (v+v+1).size ≤ width) :
    let t := ((digit port r).run τ s).last
    ∃ j ≤ 7, Exec τ (fun u => u.Fits width) (digit port r).cmd s t j ∧
      t.mem (r 0) = p ∧ t.mem (r 4) = v+v+((port.tape τ)[p]?.getD false).toNat ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  cases port with
  | input =>
    have eq (i j : Fin 5) : r i = r j ↔ i=j := r.injective.eq_iff
    have wp := (Nat.size_le_size (Nat.le_succ p)).trans (pos ▸ fit (r 0))
    have wv := (Nat.size_le_size (Nat.le_succ (v+v))).trans w
    have two : (2:ℕ).size ≤ width := hb
    have unit : 1 ≤ width := by omega
    have ww : ((digit .input r).run τ s).writeWidth ≤ width := by
      cases h : τ.input[p]? with
      | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv]
      | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv,w]
    refine ⟨_,?_,(digit .input r).exec τ s width fit ww,?_,?_,?_,?_⟩
    all_goals first
      | (intro a h₀ h₃ h₄
         cases h : τ.input[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄])
      | (cases h : τ.input[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal])
  | coin =>
    have eq (i j : Fin 5) : r i = r j ↔ i=j := r.injective.eq_iff
    have wp := (Nat.size_le_size (Nat.le_succ p)).trans (pos ▸ fit (r 0))
    have wv := (Nat.size_le_size (Nat.le_succ (v+v))).trans w
    have two : (2:ℕ).size ≤ width := hb
    have unit : 1 ≤ width := by omega
    have ww : ((digit .coin r).run τ s).writeWidth ≤ width := by
      cases h : τ.coins[p]? with
      | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv]
      | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,pos,one,acc,h,bitVal,two,unit,wp,wv,w]
    refine ⟨_,?_,(digit .coin r).exec τ s width fit ww,?_,?_,?_,?_⟩
    all_goals first
      | (intro a h₀ h₃ h₄
         cases h : τ.coins[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal,h₀,h₃,h₄])
      | (cases h : τ.coins[p]? with
         | none => simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal]
         | some x => cases x <;> simp [Port.read,Port.tape,digit,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,pos,one,acc,h,bitVal])

/-- A fixed bounded loop port reads a coin block at an arbitrary address. No length query is used. -/
theorem loop_exec (port : Port) {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (base k v : ℕ)
    (pos : s.mem (r 0) = base+k) (stop : s.mem (r 1) = base) (one : s.mem (r 2) = 1)
    (acc : s.mem (r 4) = v) (fit : s.Fits width) (hb : 2 ≤ width) (room : ((v+1)*2^k).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (loop port r) s t j ∧ j ≤ 9*k+1 ∧
      t.mem (r 0) = base ∧ t.mem (r 4) = v*2^k+value (port.tape τ) base k ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  induction k generalizing s v with
  | zero =>
    exact ⟨s,1,.done (by simp [pos,stop]),by simp,by simpa using pos,by simpa [value] using acc,rfl,fun _ _ _ _ => rfl⟩
  | succ k ih =>
    have ne {i j : Fin 5} (h : i ≠ j) := r.injective.ne h
    let x := ((port.tape τ)[base+k]?.getD false).toNat
    have bit : x ≤ 1 := Bool.toNat_le _
    have lower : v+v+1 ≤ (v+1)*2^(k+1) := by
      rw [pow_succ]
      have m := Nat.mul_le_mul_left (v+1) (Nat.one_le_two_pow (n := k))
      nlinarith only [m]
    obtain ⟨j,hj,first,pp,vv,out,frame⟩ := digit_exec port (τ := τ) r s (base+k) v (by simpa [Nat.add_assoc] using pos)
      one acc fit hb ((Nat.size_le_size lower).trans room)
    let u := ((digit port r).run τ s).last
    have bound : (v+v+x+1)*2^k ≤ (v+1)*2^(k+1) := by
      rw [pow_succ,show (v+1)*(2^k*2) = ((v+1)*2)*2^k by ring]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨t,i,rest,hi,done',number,ofinal,last⟩ := ih u (v+v+x) pp
      ((frame _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans stop)
      ((frame _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans one) vv (first.post fit)
      ((Nat.size_le_size bound).trans room)
    refine ⟨t,_,.again (by rw [pos,stop]; omega) first rest,by omega,done',?_,ofinal.trans out,
      fun a h₀ h₃ h₄ => (last a h₀ h₃ h₄).trans (frame a h₀ h₃ h₄)⟩
    rw [number,value,pow_succ]
    dsimp [x]
    ring

private theorem binaryRank_val (k : ℕ) (bits : Fin k → Bool) :
    (binaryRank k bits).val = ∑ i, (bits i).toNat*2^i.val := by
  change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))).val = _
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h (x : Bool) : (finTwoEquiv.symm x).val = x.toNat := by cases x <;> rfl
  rw [h]

theorem coinValue_eq_binaryRank (coins : List Bool) (base k : ℕ) :
    value coins base k = (binaryRank k fun i => coins[base+i.val]?.getD false).val := by
  rw [binaryRank_val]
  induction k with
  | zero => simp [value]
  | succ k ih => simp only [value,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,ih]

def readRank (port : Port) (r : Fin 5 ↪ ℕ) : Cmd := .seq (.op (.const (r 4) 0)) (loop port r)

/-- The RAM returns the rank used by the sampling proof, for every finite tape. -/
theorem readRank_exec (port : Port) {τ : Tapes} {width : ℕ} (r : Fin 5 ↪ ℕ) (s : Store) (base k : ℕ)
    (pos : s.mem (r 0) = base+k) (stop : s.mem (r 1) = base) (one : s.mem (r 2) = 1)
    (fit : s.Fits width) (hw : 2 ≤ width) (room : k+1 ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (readRank port r) s t j ∧ j ≤ 9*k+2 ∧
      t.mem (r 0) = base ∧ t.mem (r 4) = (binaryRank k fun i => (port.tape τ)[base+i.val]?.getD false).val ∧
      t.out = s.out ∧ ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 4 → t.mem a = s.mem a := by
  let u := s.write (r 4) 0
  have f : u.Fits width := Store.write_fits fit _ (by simp)
  have init : Exec τ (fun v => v.Fits width) (.op (.const (r 4) 0)) s u 1 := .op _ _ f
  have kept (i : Fin 5) (hi : i ≠ 4) : u.mem (r i) = s.mem (r i) := by simp [u,Store.write,r.injective.ne hi]
  obtain ⟨t,j,run,work,cursor,val,out,frame⟩ := loop_exec port (τ := τ) r u base k 0
    ((kept 0 (by decide)).trans pos) ((kept 1 (by decide)).trans stop) ((kept 2 (by decide)).trans one)
    (by simp [u,Store.write]) f hw (by simpa only [Nat.zero_add,Nat.one_mul,Nat.size_pow] using room)
  exact ⟨t,_,init.seq run,by omega,cursor,by simpa [coinValue_eq_binaryRank] using val,out,
    fun a h₀ h₃ h₄ => (frame a h₀ h₃ h₄).trans (by simp [u,Store.write,h₄])⟩


end DirectedHamiltonicity.Main.CycleReduction.TapeReader

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word
open OuterMachine

/-- Persistent scalar registers of the graph-search controller. The numerical encoder may use
all of its lower scratch registers between any two trial iterations. -/
inductive Reg where
  | zero
  | one
  | two
  | n
  | graph
  | candidate
  | nSq
  | nMinus
  | maxWeight
  | maxTotalPlus
  | threeN
  | drawCount
  | seedWidth
  | trials
  | blocks
  | half
  | repeats
  | span
  | parityStart
  | fieldWidth
  | radix
  | edge
  | mask
  | trial
  | seedStart
  | rank
  | parity
  | coinPos
  | votes
  | accepted
  | inputLen
  | cur
  | next
  | seen
  | valid
  | found
  | row
  | col
  | walk
  | workPow
  | tmp
  | tmp2
  | tmp3
  | tmp4
  | six
  | three
  | four
  | fifty
  | fortyNine
  | fifteen
  | eight
  deriving DecidableEq

def Reg.index : Reg → ℕ
  | .zero => 0
  | .one => 1
  | .two => 2
  | .n => 3
  | .graph => 4
  | .candidate => 5
  | .nSq => 6
  | .nMinus => 7
  | .maxWeight => 8
  | .maxTotalPlus => 9
  | .threeN => 10
  | .drawCount => 11
  | .seedWidth => 12
  | .trials => 13
  | .blocks => 14
  | .half => 15
  | .repeats => 16
  | .span => 17
  | .parityStart => 18
  | .fieldWidth => 19
  | .radix => 20
  | .edge => 21
  | .mask => 22
  | .trial => 23
  | .seedStart => 24
  | .rank => 25
  | .parity => 26
  | .coinPos => 27
  | .votes => 28
  | .accepted => 29
  | .inputLen => 30
  | .cur => 31
  | .next => 32
  | .seen => 33
  | .valid => 34
  | .found => 35
  | .row => 36
  | .col => 37
  | .walk => 38
  | .workPow => 39
  | .tmp => 40
  | .tmp2 => 41
  | .tmp3 => 42
  | .tmp4 => 43
  | .six => 44
  | .three => 45
  | .four => 46
  | .fifty => 47
  | .fortyNine => 48
  | .fifteen => 49
  | .eight => 50

structure Layout where
  floor : ℕ

def Layout.args (w : Layout) := w.floor+10
def Layout.slot (w : Layout) (r : Reg) := w.floor+128+r.index
def Layout.reg (w : Layout) (r : Reg) := cell (w.slot r)

def cmds : List Code → Code
  | [] => .pure .skip
  | c::cs => .seq c (cmds cs)

def copy (w : Layout) (dst src : ℕ) : Code := .pure (.op (.add dst src (w.reg .zero)))
def lit (w : Layout) (dst : Reg) (v : ℕ) : Code := .pure (.op (.const (w.reg dst) v))
def add (w : Layout) (dst left right : Reg) : Code := .pure (.op (.add (w.reg dst) (w.reg left) (w.reg right)))
def sub (w : Layout) (dst left right : Reg) : Code := .pure (.op (.sub (w.reg dst) (w.reg left) (w.reg right)))
def arith (w : Layout) (op : Arithmetic) (dst left right : Reg) : Code :=
  .pure (op.call (w.slot dst) (w.slot left) (w.slot right))
def inc (w : Layout) (r : Reg) := add w r r .one
def test (w : Layout) (a b : Reg) (yes no : Code) := Code.branch (w.reg a) (w.reg b) yes no
def nop := Code.pure Cmd.skip

def indexLoop (w : Layout) (counter stop : Reg) (body : Code) : Code :=
  .seq (lit w counter 0) (.loop (w.reg stop) (w.reg counter) (.seq body (inc w counter)))

/-- Fill the guest port from the packed output of the instance encoder. -/
def initPort : Fragment := Structured.sequence [
  .op (.const (cell 1) 1),.op (.const (cell 2) 2),.op (.const (cell 5) 0),
  .op (.add (cell 8) 0 (cell 5)),.op (.const (cell 9) 0)]

def loadPort (w : Layout) := Code.seq (.pure initPort.cmd) (.seq loadLoop (copy w (w.reg .inputLen) (cell 9)))

def voteArgs (w : Layout) : Fragment := Structured.sequence [
  .op (.add 0 (w.reg .span) (w.reg .zero)),.op (.add 1 (w.reg .one) (w.reg .zero)),
  .op (.add 2 (w.reg .inputLen) (w.reg .zero)),.op (.add 3 (w.reg .coinPos) (w.reg .zero)),
  .op (.add 4 (w.reg .span) (w.reg .zero))]

def collectVote (w : Layout) : Fragment := Structured.sequence [
  .op (.add (w.reg .votes) (w.reg .votes) 5),.op (.add (w.reg .coinPos) (w.reg .coinPos) (w.reg .span))]

def vote (w : Layout) := Code.seq (.pure (voteArgs w).cmd) (.seq .query (.pure (collectVote w).cmd))

def seedArgs (w : Layout) : Fragment := Structured.sequence [
  .op (.add 0 (w.reg .seedStart) (w.reg .seedWidth)),.op (.add 1 (w.reg .seedStart) (w.reg .zero)),
  .op (.add 2 (w.reg .one) (w.reg .zero))]

def encodeArgs (w : Layout) : Fragment := Structured.sequence [
  .op (.add (cell (w.args+2)) 4 (w.reg .zero)),.op (.add (cell w.args) (w.reg .n) (w.reg .zero)),
  .op (.add (cell (w.args+1)) (w.reg .candidate) (w.reg .zero)),
  .op (.add (cell (w.args+3)) (w.reg .radix) (w.reg .zero)),
  .op (.add (w.reg .seedStart) (w.reg .seedStart) (w.reg .seedWidth))]

def prepareTrial (w : Layout) (prepare : Cmd) : Cmd := .seq (seedArgs w).cmd
  (.seq (TapeReader.readRank .coin Fin.valEmbedding) (.seq (encodeArgs w).cmd prepare))

def initVotes (w : Layout) : Fragment := Structured.sequence [
  .op (.const (w.reg .votes) 0),.op (.add (w.reg .coinPos) (w.reg .parityStart) (w.reg .zero))]

def scoreTrial (w : Layout) := Code.seq (loadPort w) (.seq (.pure (initVotes w).cmd)
  (.seq (indexLoop w .parity .repeats (vote w)) (test w .votes .half nop (lit w .accepted 1))))

def trialBody (w : Layout) (prepare : Cmd) : Code := .seq (.pure (prepareTrial w prepare))
  (.branch 0 (w.reg .one) nop (scoreTrial w))

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word OuterMachine

/-- Induction rule for every finite loop in the search code. The guard and back jump each
incur one source step. Its invariant can depend on the processed prefix. -/
theorem counted {Q : Program} {τ : Tapes} {B : ℕ} (stop ptr : ℕ) (body : Code) (N work : ℕ)
    (I : ℕ → Data → Prop) (fields : ∀ i d, I i d → d.bank.Fits B ∧ d.bank.mem stop=N ∧ d.bank.mem ptr=i)
    (next : ∀ i<N, ∀ d, I i d → ∃ t j, Eval Q τ B body d t j ∧ j ≤ work ∧ I (i+1) t)
    (i : ℕ) (le : i ≤ N) (d : Data) (inv : I i d) :
    ∃ t j, Eval Q τ B (.loop stop ptr body) d t j ∧ j ≤ (N-i)*(work+2)+1 ∧ I N t := by
  suffices r : ∀ f i, i+f=N → ∀ d, I i d → ∃ t j, Eval Q τ B (.loop stop ptr body) d t j ∧
      j ≤ f*(work+2)+1 ∧ I N t from r (N-i) i (by omega) d inv
  intro f
  induction f with
  | zero =>
    intro i sum d inv
    obtain ⟨fit,dim,cur⟩ := fields i d inv
    have eq : i=N := by omega
    exact ⟨d,1,.done fit (by rw [dim,cur,eq]),by simp,eq ▸ inv⟩
  | succ f ih =>
    intro i sum d inv
    obtain ⟨fit,dim,cur⟩ := fields i d inv
    obtain ⟨m,k,step,cost,run⟩ := next i (by omega) d inv
    obtain ⟨t,j,rest,cap,ok⟩ := ih (i+1) (by omega) m run
    refine ⟨t,_,.again fit (by rw [dim,cur];omega) step rest,?_,ok⟩
    rw [Nat.succ_mul];omega

theorem setWord (Q : Program) (τ : Tapes) (B a val : ℕ) (d : Data) (fit : d.bank.Fits B) (size : val.size ≤ B) :
    let t := {d with bank := d.bank.write a val}
    Eval Q τ B (.pure (.op (.const a val))) d t 1 ∧ t.bank.Fits B := by
  have h := Store.write_fits fit a size
  exact ⟨.pure fit (.op _ _ h),h⟩

theorem stepCounter (w : Layout) (r : Reg) (Q : Program) (τ : Tapes) (B i : ℕ) (d : Data) (fit : d.bank.Fits B)
    (one : d.bank.mem (w.reg .one)=1) (atI : d.bank.mem (w.reg r)=i) (size : (i+1).size ≤ B) :
    let t := {d with bank := d.bank.write (w.reg r) (i+1)}
    Eval Q τ B (inc w r) d t 1 ∧ t.bank.Fits B := by
  have eq : (Op.add (w.reg r) (w.reg r) (w.reg .one)).eval τ d.bank=d.bank.write (w.reg r) (i+1) := by
    simp only [Op.eval,one,atI]
  have h := Store.write_fits fit (w.reg r) size
  refine ⟨.pure fit ?_,h⟩
  rw [←eq];exact Exec.op _ _ (eq.symm ▸ h)

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word OuterMachine

def logStart (src : ℕ) : Fragment := Structured.sequence [ .op (.const 4 0), .op (.add 0 src 4),
  .op (.const 1 1), .op (.const 2 0), .op (.const 3 1)]
def logStep : Fragment := Structured.sequence [.op (.add 1 1 1),.op (.add 2 2 3)]
def nativeLog (dst src : ℕ) : Cmd :=
  .seq (logStart src).cmd (.seq (.whileGt 0 1 logStep.cmd) (.op (.add dst 2 4)))

private structure LogState (s : Store) (x i : ℕ) : Prop where
  arg : s.mem 0=x
  power : s.mem 1=2^i
  count : s.mem 2=i
  unit : s.mem 3=1
  zero : s.mem 4=0

private theorem logLoop {τ : Tapes} {B x : ℕ} (cap : x.size+2 ≤ B) (f i : ℕ)
    (total : i+f=Nat.clog 2 x) (s : Store) (fit : s.Fits B) (st : LogState s x i) :
    ∃ t j, Exec τ (fun b => b.Fits B) (.whileGt 0 1 logStep.cmd) s t j ∧ j ≤ 4*f+1 ∧
      LogState t x (Nat.clog 2 x) ∧ t.out=s.out ∧ ∀ p, 5 ≤ p → t.mem p=s.mem p := by
  have csize : Nat.clog 2 x ≤ x.size := Nat.clog_le_of_le_pow (Nat.lt_size_self _).le
  induction f generalizing i s with
  | zero =>
    have eq : i=Nat.clog 2 x := by omega
    exact ⟨s,1,.done (by rw [st.arg,st.power,eq];exact Nat.le_pow_clog (by decide) x),by omega,eq ▸ st,rfl,fun _ _ => rfl⟩
  | succ f ih =>
    have less : i < Nat.clog 2 x := by omega
    have guard : ¬s.mem 0 ≤ s.mem 1 := by
      rw [st.arg,st.power];intro h;have := Nat.clog_le_of_le_pow h;omega
    have dbl : 2^i+2^i=2^(i+1) := by rw [pow_succ];omega
    have pw : (2^(i+1)).size ≤ B := by rw [Nat.size_pow];omega
    have isz : (i+1).size ≤ B := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=i+1))).trans (by omega)
    let u := (logStep.run τ s).last
    have width : (logStep.run τ s).writeWidth ≤ B := by
      simp [logStep,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,st.power,st.count,st.unit,dbl,pw,isz]
    have step : Exec τ (fun b => b.Fits B) logStep.cmd s u 2 := logStep.exec τ s B fit width
    have next : LogState u x (i+1) := by
      constructor <;> simp [u,logStep,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
        st.arg,st.power,st.count,st.unit,st.zero,dbl]
    obtain ⟨t,j,rest,fee,done,out,fr⟩ := ih (i+1) (by omega) u (step.post fit) next
    refine ⟨t,_,.again guard step rest,by omega,done,out,?_⟩
    intro p hp;rw [fr p hp];simp (disch := omega) [u,logStep,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]

theorem nativeLog_exec {τ : Tapes} {B : ℕ} (dst src : ℕ) (s : Store) (fit : s.Fits B)
    (hs : 5 ≤ src) (cap : (s.mem src).size+2 ≤ B) :
    ∃ t j, Exec τ (fun a => a.Fits B) (nativeLog dst src) s t j ∧ j ≤ 4*(s.mem src).size+7 ∧
      t.out=s.out ∧ ∀ p, 5 ≤ p → t.mem p=if p=dst then Nat.clog 2 (s.mem src) else s.mem p := by
  let x := s.mem src
  let a := ((logStart src).run τ s).last
  have one : (1:ℕ).size ≤ B := by change 1 ≤ B;omega
  have ww : ((logStart src).run τ s).writeWidth ≤ B := by
    simp (disch := omega) [logStart,Structured.sequence,Fragment.run,Op.eval,Store.write,Op.written,Function.update_apply,fit src,one] <;> omega
  have start : Exec τ (fun a => a.Fits B) (logStart src).cmd s a 5 := (logStart src).exec τ s B fit ww
  have init : LogState a x 0 := by
    constructor <;> simp (disch := omega) [a,x,logStart,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
  have high (p : ℕ) (hp : 5 ≤ p) : a.mem p=s.mem p := by
    simp (disch := omega) [a,logStart,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
  obtain ⟨b,k,loop,fee,c,out,frame⟩ := logLoop (τ:=τ) cap (Nat.clog 2 x) 0 (by simp [x]) a (start.post fit) init
  have final : (Op.add dst 2 4).eval τ b=b.write dst (Nat.clog 2 x) := by simp [Op.eval,c.count,c.zero,x]
  have bound := Nat.clog_le_of_le_pow (Nat.lt_size_self x).le
  have fits : ((Op.add dst 2 4).eval τ b).Fits B := by
    rw [final];apply Store.write_fits (loop.post (start.post fit));exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [x] at bound ⊢;omega)
  refine ⟨_,_,start.seq (loop.seq (.op b (.add dst 2 4) fits)),by dsimp [x] at fee bound;omega,?_,?_⟩
  · rw [final];exact out
  · intro p hp;rw [final];simp [Store.write,Function.update_apply,frame p hp,high p hp,x]

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram.RegisterCode
open TargetedSamplers TargetedSamplers.Structured Word OuterMachine

abbrev Values := ℕ → ℕ
def peek (w : Layout) (d : Data) : Values := fun i => d.bank.mem (cell (w.floor+128+i))

inductive Expr where
  | const (a : ℕ)
  | add (a b : Reg)
  | sub (a b : Reg)
  | arith (op : Arithmetic) (a b : Reg)
  | clog (a : Reg)
def Expr.val (v : Values) : Expr → ℕ
  | .const a => a
  | .add a b => v a.index + v b.index
  | .sub a b => v a.index - v b.index
  | .arith op a b => op.value (v a.index) (v b.index)
  | .clog a => Nat.clog 2 (v a.index)
def Expr.width (v : Values) (e : Expr) := max (e.val v).size (match e with
  | .arith _ a _ => (2*v a.index+2).size
  | .clog a => (v a.index).size+2
  | _ => 0)
def Expr.fee (v : Values) : Expr → ℕ
  | .arith op a b => op.steps (v a.index) (v b.index)+4
  | .clog a => 4*(v a.index).size+7
  | _ => 1
def Expr.cmd (w : Layout) (r : Reg) : Expr → Code
  | .const a => lit w r a
  | .add a b => SearchProgram.add w r a b
  | .sub a b => SearchProgram.sub w r a b
  | .arith op a b => SearchProgram.arith w op r a b
  | .clog a => .pure (nativeLog (w.reg r) (w.reg a))

structure Line where
  dst : Reg
  rhs : Expr
def Line.put (a : Line) (v : Values) := Function.update v a.dst.index (a.rhs.val v)
def Line.cmd (a : Line) (w : Layout) := a.rhs.cmd w a.dst

private theorem low (w : Layout) (i : ℕ) : 5 ≤ cell (w.floor+128+i) := by unfold cell;omega
private theorem update_peek (w : Layout) (d : Data) (r : Reg) (x : ℕ) :
    peek w {d with bank := d.bank.write (w.reg r) x}=Function.update (peek w d) r.index x := by
  funext i;simp [peek,Layout.reg,Layout.slot,cell,Store.write,Function.update_apply]
private theorem unit_op {Q : Program} {τ : Tapes} {B : ℕ} (d : Data) (w : Layout) (r : Reg) (o : Op) (x : ℕ)
    (fit : d.bank.Fits B) (bound : x.size ≤ B) (act : o.eval τ d.bank=d.bank.write (w.reg r) x) :
    ∃ t j, Eval Q τ B (.pure (.op o)) d t j ∧ j ≤ 1 ∧ t.bank.Fits B ∧
      peek w t=Function.update (peek w d) r.index x ∧ t.bank.out=d.bank.out ∧ t.epoch=d.epoch := by
  have good := Store.write_fits fit (w.reg r) bound
  have ex : Exec τ (fun s => s.Fits B) (.op o) d.bank (d.bank.write (w.reg r) x) 1 := by
    rw [←act];exact .op _ _ (act.symm ▸ good)
  exact ⟨_,1,.pure fit ex,le_rfl,good,update_peek ..,rfl,rfl⟩

theorem line_run {Q : Program} {τ : Tapes} {B : ℕ} (w : Layout) (d : Data) (a : Line) (fit : d.bank.Fits B)
    (two : 2 ≤ B) (cap : a.rhs.width (peek w d) ≤ B) :
    ∃ t j, Eval Q τ B (a.cmd w) d t j ∧ j ≤ a.rhs.fee (peek w d) ∧ t.bank.Fits B ∧
      peek w t=a.put (peek w d) ∧ t.bank.out=d.bank.out ∧ t.epoch=d.epoch := by
  have value := (max_le_iff.mp cap).1
  have scratch := (max_le_iff.mp cap).2
  obtain ⟨r,e⟩ := a
  cases e with
  | const a => exact unit_op d w r _ a fit value rfl
  | add a b => exact unit_op d w r _ _ fit value rfl
  | sub a b => exact unit_op d w r _ _ fit value rfl
  | arith op a b =>
    obtain ⟨s,j,ex,time,out,mem⟩ := op.call_exec (τ:=τ) (w.slot r) (w.slot a) (w.slot b) d.bank fit two scratch value
    refine ⟨_,j,.pure fit ex,time,ex.post fit,?_,out,rfl⟩
    funext i;simpa [peek,Layout.slot,Line.put,Expr.val,Function.update_apply] using mem (w.floor+128+i)
  | clog a =>
    obtain ⟨s,j,ex,time,out,mem⟩ := nativeLog_exec (τ:=τ) (w.reg r) (w.reg a) d.bank fit (low w a.index) scratch
    refine ⟨_,j,.pure fit ex,time,ex.post fit,?_,out,rfl⟩
    funext i;simpa [peek,Line.put,Expr.val,Function.update_apply,Layout.reg,Layout.slot,cell] using mem _ (low w i)

def code (w : Layout) (cs : List Line) := cmds (cs.map (Line.cmd · w))
def result (v : Values) : List Line → Values
  | [] => v
  | a::as => result (a.put v) as
def width (v : Values) : List Line → ℕ
  | [] => 0
  | a::as => max (a.rhs.width v) (width (a.put v) as)
def fee (v : Values) : List Line → ℕ
  | [] => 0
  | a::as => a.rhs.fee v+fee (a.put v) as

theorem run {Q : Program} {τ : Tapes} {B : ℕ} (w : Layout) (cs : List Line) (v : Values) (d : Data)
    (matchV : peek w d=v) (fit : d.bank.Fits B) (two : 2 ≤ B) (cap : width v cs ≤ B) :
    ∃ t j, Eval Q τ B (code w cs) d t j ∧ j ≤ fee v cs ∧ t.bank.Fits B ∧
      peek w t=result v cs ∧ t.bank.out=d.bank.out ∧ t.epoch=d.epoch := by
  induction cs generalizing v d with
  | nil => exact ⟨d,0,.pure fit (.skip _),le_rfl,fit,matchV,rfl,rfl⟩
  | cons a as ih =>
    obtain ⟨fst,snd⟩ := max_le_iff.mp cap
    obtain ⟨u,j,step,cost,uf,ur,uo,ue⟩ := line_run (Q:=Q) (τ:=τ) w d a fit two (matchV ▸ fst)
    rw [matchV] at ur cost
    obtain ⟨t,k,tail,time,tf,tr,out,ep⟩ := ih _ u ur uf snd
    exact ⟨_,_,step.seq tail,Nat.add_le_add cost time,tf,tr,out.trans uo,ep.trans ue⟩

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram.RegisterCode

namespace DirectedHamiltonicity.Main.CycleReduction.ControlBounds

/-- A quantity bounded by one fixed polynomial in the graph dimension. -/
def Small (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval (n+1)
/-- A register can hold an exponential value if its binary length has a polynomial bound. -/
def Word (f : ℕ → ℕ) : Prop := Small (fun n => (f n).size)

theorem Small.of_le {f g : ℕ → ℕ} (b : Small g) (h : ∀ n, f n ≤ g n) : Small f := by
  obtain ⟨p,hp⟩ := b;exact ⟨p,fun n => (h n).trans (hp n)⟩
theorem small_const (k : ℕ) : Small (fun _ => k) := ⟨Polynomial.C k,by simp⟩
theorem small_dim : Small (fun n => n) := ⟨Polynomial.X,by simp⟩
theorem Small.add {f g : ℕ → ℕ} (a : Small f) (b : Small g) : Small (fun n => f n+g n) := by
  obtain ⟨p,h⟩ := a;obtain ⟨q,l⟩ := b;exact ⟨p+q,fun n => by rw [Polynomial.eval_add];exact Nat.add_le_add (h n) (l n)⟩
theorem Small.mul {f g : ℕ → ℕ} (a : Small f) (b : Small g) : Small (fun n => f n*g n) := by
  obtain ⟨p,h⟩ := a;obtain ⟨q,l⟩ := b;exact ⟨p*q,fun n => by rw [Polynomial.eval_mul];exact Nat.mul_le_mul (h n) (l n)⟩
theorem Small.comp_polynomial {f : ℕ → ℕ} (h : Small f) (p : Polynomial ℕ) : Small (fun n => p.eval (f n)) := by
  obtain ⟨q,b⟩ := h;refine ⟨p.comp q,fun n => ?_⟩
  rw [Polynomial.eval_comp]
  induction p using Polynomial.induction_on' with
  | monomial j k => simp;exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (b n) j)
  | add p r hp hr => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hr
theorem Small.word {f : ℕ → ℕ} (hf : Small f) : Word f :=
  hf.of_le fun _ => Nat.size_le.mpr Nat.lt_two_pow_self
theorem Word.of_le {f g : ℕ → ℕ} (b : Word g) (h : ∀ n, f n ≤ g n) : Word f :=
  Small.of_le b (fun n => Nat.size_le_size (h n))

theorem sum_width (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a;have hb := Nat.lt_size_self b
  have pa := Nat.two_pow_pos a.size;have pb := Nat.two_pow_pos b.size
  rw [pow_succ,pow_add];nlinarith only [ha,hb,Nat.mul_le_mul_left (2^a.size) pb,Nat.mul_le_mul_right (2^b.size) pa]
theorem prod_width (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr;rw [pow_add]
  exact (Nat.mul_le_mul_left _ (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (Nat.two_pow_pos _))
theorem pow_width (a b : ℕ) : (a^b).size ≤ a.size*b+1 := by
  have le := Nat.pow_le_pow_left (Nat.lt_size_self a).le b;rw [←pow_mul] at le
  exact (Nat.size_le_size le).trans_eq Nat.size_pow

theorem Word.add {f g : ℕ → ℕ} (a : Word f) (b : Word g) : Word (fun n => f n+g n) :=
  Small.of_le ((Small.add a b).add (small_const 1)) (fun _ => sum_width ..)
theorem Word.mul {f g : ℕ → ℕ} (a : Word f) (b : Word g) : Word (fun n => f n*g n) :=
  Small.of_le (Small.add a b) (fun _ => prod_width ..)
theorem Word.pow {f g : ℕ → ℕ} (a : Word f) (b : Small g) : Word (fun n => f n^g n) :=
  Small.of_le ((Small.mul a b).add (small_const 1)) (fun _ => pow_width ..)

theorem small_weight : Small Wmax := ((small_const 6).mul small_dim).of_le fun n => Nat.mul_le_mul_left _ (Nat.sub_le n 1)
theorem small_target : Small Bmax := (small_dim.mul small_weight).of_le fun n => Nat.mul_le_mul_right _ (Nat.sub_le n 1)
theorem small_blocks : Small outerBlocks :=
  (((small_const 6).mul small_dim).mul small_dim).add (small_const 6)

theorem count_width : Word drawCount :=
  (small_dim.mul small_dim).word.mul <| (((small_const 50).word.pow (small_dim.mul small_dim)).mul
    (small_weight.word.pow (small_dim.mul (small_const 3)))).mul (small_target.add (small_const 1)).word

theorem seed_small : Small seedWidth :=
  Small.of_le count_width (fun n => by
    unfold seedWidth;rw [Fintype.card_congr (rankDraw n),Fintype.card_fin]
    exact Nat.clog_le_of_le_pow (Nat.lt_size_self _).le)

theorem ceil_width (a b : ℕ) (pos : 0<b) : Word (fun n => ⌈((a:ℚ)/(b:ℚ))^n⌉₊) := by
  apply Word.of_le ((small_const a).word.pow small_dim)
  intro n;apply Nat.ceil_le.mpr
  push_cast
  apply pow_le_pow_left₀ (by positivity)
  have den : (1:ℚ) ≤ b := by exact_mod_cast pos
  exact div_le_self (by positivity) den

theorem trials_width : Word trials :=
  (((((small_const 4).mul ((small_dim.mul small_dim).mul (small_target.add (small_const 1)))).word).mul
    (ceil_width 50 49 (by decide))).mul small_blocks.word)

theorem majority_small : Small majorityHalf :=
  (small_const 2).mul (Small.add trials_width small_blocks)

theorem span_width (A k : ℕ) : Word (coinSpan A k) :=
  ((small_const A).word.mul (ceil_width 15 8 (by decide))).mul
    ((((small_dim.add ((small_dim.mul small_dim).mul (small_const 3))).add small_weight).add (small_const 1)).word.pow (small_const k))

theorem epoch_width : Word (fun n => n*n*trials n*(2*majorityHalf n)) :=
  ((small_dim.mul small_dim).word.mul trials_width).mul ((small_const 2).mul majority_small).word

theorem seed_cursor_width : Word (fun n => trials n*seedWidth n) := trials_width.mul seed_small.word

theorem tape_cursor_width (A k : ℕ) : Word (fun n => coinCount n (coinSpan A k n)) :=
  seed_cursor_width.add (((small_const 2).mul majority_small).word.mul (span_width A k))

theorem field_small : Small (fun n => n+n*n+seedWidth n+1) :=
  ((small_dim.add (small_dim.mul small_dim)).add seed_small).add (small_const 1)

end DirectedHamiltonicity.Main.CycleReduction.ControlBounds

noncomputable section

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram.RegisterCode

open TargetedSamplers.Structured.Word
abbrev Poly := Polynomial ℕ
structure Limit where
  bits : Poly
  mag : Option Poly

def Limit.Holds (l : Limit) (n x : ℕ) :=
  x.size ≤ l.bits.eval n ∧ ∀ p, l.mag=some p → x ≤ p.eval n
def constL (a : ℕ) : Limit := ⟨Polynomial.C a.size,some (Polynomial.C a)⟩
def magn (l : Limit) := l.mag.getD 0
def combine (op : Poly → Poly → Poly) (l r : Limit) : Option Poly := do
  let a ← l.mag
  let b ← r.mag
  return op a b
private theorem combine_sound {l r : Limit} {x y n : ℕ} (lx : l.Holds n x) (ry : r.Holds n y)
    (op : Poly → Poly → Poly) (f : ℕ → ℕ → ℕ)
    (law : ∀ p q, x ≤ Polynomial.eval n p → y ≤ Polynomial.eval n q → f x y ≤ (op p q).eval n) :
    ∀ p, combine op l r=some p → f x y ≤ p.eval n := by
  intro p eq
  cases a : l.mag with
  | none => simp [combine,a] at eq
  | some s =>
    cases b : r.mag with
    | none => simp [combine,a,b] at eq
    | some t =>
      simp [combine,a,b] at eq;subst p;exact law s t (lx.2 _ a) (ry.2 _ b)
def EFacts (n : ℕ) (v : Values) (env : ℕ → Limit) := ∀ i, (env i).Holds n (v i)

def Expr.bound (env : ℕ → Limit) : Expr → Limit
  | .const a => constL a
  | .add a b => ⟨(env a.index).bits+(env b.index).bits+1,combine (·+·) (env a.index) (env b.index)⟩
  | .sub a _ => env a.index
  | .arith .mul a b => ⟨(env a.index).bits+(env b.index).bits,combine (·*·) (env a.index) (env b.index)⟩
  | .arith .div a _ | .arith .mod a _ => env a.index
  | .arith .pow a b => ⟨(env a.index).bits*magn (env b.index)+1,none⟩
  | .clog a => ⟨(env a.index).bits,some (env a.index).bits⟩
def Expr.ok (env : ℕ → Limit) : Expr → Bool
  | .arith .pow _ b => (env b.index).mag.isSome
  | _ => true
def Expr.space (env : ℕ → Limit) (e : Expr) := (e.bound env).bits + (match e with
  | .arith _ a _ => (env a.index).bits+6
  | .clog a => (env a.index).bits+2
  | _ => 0)
def Expr.time (env : ℕ → Limit) : Expr → Poly
  | .arith .pow a b => magn (env b.index)*((env a.index).bits*(5*(env a.index).bits+9)+10)+8
  | .arith _ a _ => (env a.index).bits*(5*(env a.index).bits+9)+11
  | .clog a => 4*(env a.index).bits+7
  | _ => 1

private theorem below {l : Limit} {n x y : ℕ} (h : l.Holds n x) (le : y ≤ x) : l.Holds n y :=
  ⟨(Nat.size_le_size le).trans h.1,fun p eq => le.trans (h.2 _ eq)⟩
private theorem mag_sound {l : Limit} {n x : ℕ} (h : l.Holds n x) (ok : l.mag.isSome=true) :
    x ≤ (magn l).eval n := by
  cases eq : l.mag with
  | none => simp [eq] at ok
  | some p => simpa [magn,eq] using h.2 _ eq

theorem value_bound (e : Expr) (en : ℕ → Limit) (v : Values) (n : ℕ)
    (h : EFacts n v en) (ok : e.ok en=true) : (e.bound en).Holds n (e.val v) := by
  cases e with
  | const x => simp [Expr.bound,Expr.val,constL,Limit.Holds]
  | sub a b => exact below (h a.index) (Nat.sub_le ..)
  | clog a =>
    have le := (Nat.clog_le_of_le_pow (b:=2) (Nat.lt_size_self (v a.index)).le).trans (h a.index).1
    exact ⟨(Nat.size_le.mpr Nat.lt_two_pow_self).trans le,by intro p eq;cases eq;exact le⟩
  | add a b =>
    refine ⟨?_,combine_sound (h a.index) (h b.index) (·+·) (·+·) (fun p q l r => by simpa using Nat.add_le_add l r)⟩
    simpa [Expr.bound,Expr.val] using (ControlBounds.sum_width _ _).trans
      (Nat.add_le_add_right (Nat.add_le_add (h a.index).1 (h b.index).1) 1)
  | arith op a b =>
    cases op with
    | div => exact below (h a.index) (Nat.div_le_self ..)
    | mod => exact below (h a.index) (Nat.mod_le ..)
    | mul =>
      refine ⟨?_,combine_sound (h a.index) (h b.index) (·*·) (·*·) (fun p q l r => by simpa using Nat.mul_le_mul l r)⟩
      simpa [Expr.bound,Expr.val,Arithmetic.value] using (ControlBounds.prod_width _ _).trans (Nat.add_le_add (h a.index).1 (h b.index).1)
    | pow =>
      have exp := mag_sound (h b.index) ok
      refine ⟨?_,fun p no => by cases no⟩
      simpa [Expr.bound,Expr.val,Arithmetic.value] using (ControlBounds.pow_width _ _).trans
        (Nat.add_le_add_right (Nat.mul_le_mul (h a.index).1 exp) 1)

private theorem scratch_width (x : ℕ) : (2*x+2).size ≤ x.size+6 := by
  have a := ControlBounds.prod_width 2 x
  have b := ControlBounds.sum_width (2*x) 2
  change (2*x).size ≤ 2+x.size at a
  change (2*x+2).size ≤ (2*x).size+2+1 at b
  omega

theorem space_bound (e : Expr) (en : ℕ → Limit) (v : Values) (n : ℕ)
    (h : EFacts n v en) (ok : e.ok en=true) : e.width v ≤ (e.space en).eval n := by
  have out := (value_bound e en v n h ok).1
  unfold Expr.width Expr.space
  rw [Polynomial.eval_add];apply max_le
  · omega
  · cases e with
    | const | add | sub => exact Nat.zero_le _
    | arith op a b =>
      have le := (scratch_width _).trans (Nat.add_le_add_right (h a.index).1 6)
      simp;omega
    | clog a => have := (h a.index).1;simp;omega

theorem time_bound (e : Expr) (en : ℕ → Limit) (v : Values) (n : ℕ)
    (h : EFacts n v en) (ok : e.ok en=true) : e.fee v ≤ (e.time en).eval n := by
  cases e with
  | const | add | sub => simp [Expr.time,Expr.fee]
  | clog a => simpa [Expr.time,Expr.fee] using Nat.add_le_add_right (Nat.mul_le_mul_left 4 (h a.index).1) 7
  | arith op a b =>
    have sz := (h a.index).1
    have coeff := Nat.add_le_add_right (Nat.mul_le_mul_left 5 sz) 9
    have base := Nat.mul_le_mul sz coeff
    cases op with
    | mul | mod | div => simp [Expr.time,Expr.fee,Arithmetic.steps];omega
    | pow =>
      have exp := mag_sound (h b.index) ok
      have prod := Nat.mul_le_mul exp (Nat.add_le_add_right base 10)
      simp [Expr.time,Expr.fee,Arithmetic.steps];omega

structure Budget where
  space : Poly
  time : Poly
  ok : Bool
def budget (en : ℕ → Limit) : List Line → Budget
  | [] => ⟨0,0,true⟩
  | a::as =>
    let tail := budget (Function.update en a.dst.index (a.rhs.bound en)) as
    ⟨a.rhs.space en+tail.space,a.rhs.time en+tail.time,a.rhs.ok en && tail.ok⟩

theorem budget_sound (en : ℕ → Limit) (cs : List Line) (v : Values) (n : ℕ) (h : EFacts n v en)
    (ok : (budget en cs).ok=true) :
    width v cs ≤ (budget en cs).space.eval n ∧ fee v cs ≤ (budget en cs).time.eval n := by
  induction cs generalizing en v with
  | nil => simp [budget,width,fee]
  | cons a as ih =>
    let u := Function.update en a.dst.index (a.rhs.bound en)
    obtain ⟨o1,o2⟩ := Bool.and_eq_true_iff.mp ok
    have post : EFacts n (a.put v) u := by
      intro i;by_cases eq : i=a.dst.index
      · subst i;simpa [u,Line.put] using value_bound a.rhs en v n h o1
      · simpa [u,Line.put,eq] using h i
    obtain ⟨sw,st⟩ := ih u (a.put v) post o2
    have fw := space_bound a.rhs en v n h o1
    have ft := time_bound a.rhs en v n h o1
    change max _ _ ≤ (a.rhs.space en+(budget u as).space).eval n ∧ _ ≤ (a.rhs.time en+(budget u as).time).eval n
    simp only [Polynomial.eval_add]
    exact ⟨max_le (by omega) (by omega),Nat.add_le_add ft st⟩

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram.RegisterCode

end

namespace DirectedHamiltonicity.Main.CycleReduction.Schedule

def ceilPower (a b n : ℕ) := (a^n+b^n-1)/b^n

theorem ceil_ratio (a b : ℕ) (hb : 0<b) : ⌈(a:ℚ)/(b:ℚ)⌉₊=(a+b-1)/b := by
  rw [← Nat.ceilDiv_eq_add_pred_div]
  have test (c : ℕ) : ⌈(a:ℚ)/(b:ℚ)⌉₊ ≤ c ↔ a ⌈/⌉ b ≤ c := by
    rw [Nat.ceil_le,div_le_iff₀ (by exact_mod_cast hb : 0 < (b:ℚ)),ceilDiv_le_iff_le_mul hb,mul_comm b c]
    exact_mod_cast (Iff.rfl : a ≤ c*b ↔ a ≤ c*b)
  exact le_antisymm ((test _).2 le_rfl) ((test _).1 le_rfl)

theorem ceilPower_eq (a b n : ℕ) (hb : 0<b) : ceilPower a b n=⌈((a:ℚ)/(b:ℚ))^n⌉₊ := by
  rw [div_pow,←Nat.cast_pow,←Nat.cast_pow,ceil_ratio _ _ (pow_pos hb n)];rfl

theorem size_eq_clog (x : ℕ) : Nat.clog 2 (x+1)=x.size := by
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (Nat.lt_size_self _)
  · exact Nat.size_le.mpr (Nat.le_pow_clog (by decide) (x+1))

theorem seed_eq (n : ℕ) : Nat.clog 2 (drawCount n)=seedWidth n := by
  unfold seedWidth;rw [Fintype.card_congr (rankDraw n),Fintype.card_fin]

theorem raw_values (n A k : ℕ) :
    let r := 6*(n-1)
    let b := (n-1)*r+1
    let blocks := 6*(n*n)+6
    let m := ceilPower 50 49 n*4*(n*n)*b*blocks
    let half := 2*(Nat.clog 2 (m+1)+blocks)
    let bits := Nat.clog 2 (50^(n*n)*r^(3*n)*b*(n*n))
    let T := ceilPower 15 8 n*((n*n*3+n+r+1)^k)*A
    m=trials n ∧ half=majorityHalf n ∧ bits=seedWidth n ∧ T=coinSpan A k n := by
  dsimp only
  have tr : ceilPower 50 49 n*4*(n*n)*((n-1)*(6*(n-1))+1)*(6*(n*n)+6)=trials n := by
    rw [ceilPower_eq _ _ _ (by decide)];unfold trials trialBlock outerBlocks outerCeil Bmax Wmax;ring
  refine ⟨tr,?_,?_,?_⟩
  · rw [tr,size_eq_clog];unfold majorityHalf outerBlocks;ring
  · rw [←seed_eq];congr 1;unfold drawCount Bmax Wmax;rw [Nat.mul_comm 3 n];ring
  · rw [ceilPower_eq _ _ _ (by decide)];unfold coinSpan
    rw [show n*n*3+n+6*(n-1)+1=n+n*n*3+6*(n-1)+1 by omega];ring

end DirectedHamiltonicity.Main.CycleReduction.Schedule

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word OuterMachine

theorem Layout.high (w : Layout) (r : Reg) : 14 ≤ w.reg r := by unfold Layout.reg Layout.slot cell;omega

structure Voted (w : Layout) (d t : Data) (bit : Bool) (start span : ℕ) : Prop where
  tally : t.bank.mem (w.reg .votes)=d.bank.mem (w.reg .votes)+bit.toNat
  cursor : t.bank.mem (w.reg .coinPos)=start+span
  high : ∀ i, 14 ≤ i → i≠w.reg .votes → i≠w.reg .coinPos → t.bank.mem i=d.bank.mem i
  output : t.bank.out=d.bank.out
  port : t.port=d.port
  epoch : t.epoch=d.epoch+1

theorem single_vote (w : Layout) (Q : Program) (τ : Tapes) (B T start : ℕ) (x : List Bool) (v : Bool) (d : Data)
    (fit : d.bank.Fits B) (clock : d.epoch.size ≤ B) (zero : d.bank.mem (w.reg .zero)=0)
    (one : d.bank.mem (w.reg .one)=1) (dim : d.bank.mem (w.reg .inputLen)=x.length)
    (fuel : d.bank.mem (w.reg .span)=T) (ptr : d.bank.mem (w.reg .coinPos)=start)
    (port : ∀ i<x.length, d.port i=bitVal x[i]?)
    (call : Q.RunsIn (runTapes x (CoinWindow.window τ.coins start T)) T (some [v]))
    (tally : (d.bank.mem (w.reg .votes)+v.toNat).size ≤ B) (cursor : (start+T).size ≤ B) :
    ∃ t j, Eval Q τ B (vote w) d t j ∧ j ≤ T+8 ∧ t.bank.Fits B ∧ Voted w d t v start T := by
  let a : Data := {d with bank := ((voteArgs w).run τ d.bank).last}
  have high (r : Reg) := w.high r
  have score : T.size ≤ B := fuel ▸ fit (w.reg .span)
  have offset : start.size ≤ B := ptr ▸ fit (w.reg .coinPos)
  have size : x.length.size ≤ B := dim ▸ fit (w.reg .inputLen)
  have oneSize : (1:ℕ).size ≤ B := one ▸ fit (w.reg .one)
  have far (r : Reg) (j : ℕ) (h : j<14) : w.reg r≠j := by have := high r;omega
  have small : ((voteArgs w).run τ d.bank).writeWidth ≤ B := by
    simp (disch := decide) [voteArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,far,zero,one,dim,fuel,ptr,score,offset,size,oneSize]
    exact oneSize
  have ex := (voteArgs w).exec τ d.bank B fit small
  have arg : Exec τ (fun b => b.Fits B) (voteArgs w).cmd d.bank a.bank 5 := ex
  have aFit := arg.post fit
  have keep (i : ℕ) (h : 14 ≤ i) : a.bank.mem i=d.bank.mem i := by
    simp (disch := omega) [a,voteArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
  have vals : a.bank.mem 0=T ∧ a.bank.mem 1=1 ∧ a.bank.mem 2=x.length ∧ a.bank.mem 3=start ∧ a.bank.mem 4=T := by
    simp (disch := decide) [a,voteArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,far,zero,one,dim,fuel,ptr]
  obtain ⟨v0,v1,v2,v3,v4⟩ := vals
  let b := a.returnBit v
  have query : Eval Q τ B .query a b (T+1) := by
    rw [←v0]
    apply Eval.query _ x v aFit clock v1 v2 port
    simpa only [v0,v3,v4] using call
  have vSize : v.toNat.size ≤ B := by cases v <;> first | exact Nat.zero_le _ | exact oneSize
  have bFit : b.bank.Fits B := Store.write_fits (Store.write_fits aFit 0 (by simp)) 5 vSize
  have bHigh (i : ℕ) (h : 14 ≤ i) : b.bank.mem i=d.bank.mem i := by
    simp [b,Data.returnBit,Store.write,show i≠5 by omega,show i≠0 by omega,keep i h]
  have bBit : b.bank.mem 5=v.toNat := by simp [b,Data.returnBit,Store.write]
  have distinct : w.reg .votes≠w.reg .coinPos := by simp [Layout.reg,Layout.slot,Reg.index,cell]
  have untouched : w.reg .span≠w.reg .votes := by simp [Layout.reg,Layout.slot,Reg.index,cell]
  let t : Data := {b with bank := ((collectVote w).run τ b.bank).last}
  have widths : ((collectVote w).run τ b.bank).writeWidth ≤ B := by
    simp [collectVote,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,distinct.symm,untouched,bHigh _ (high _),bBit,ptr,fuel,tally,cursor]
  have collect : Exec τ (fun v => v.Fits B) (collectVote w).cmd b.bank t.bank 2 := (collectVote w).exec τ b.bank B bFit widths
  refine ⟨t,_,(Eval.pure fit arg).seq (query.seq (Eval.pure bFit collect)),by omega,collect.post bFit,?_,?_,?_,rfl,rfl,rfl⟩
  · simp [t,collectVote,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      distinct,bHigh _ (high _),bBit]
  · simp [t,collectVote,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      distinct.symm,untouched,bHigh _ (high _),ptr,fuel]
  · intro i hi v c
    simp [t,collectVote,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,v,c,bHigh i hi]

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word OuterMachine

def tallyPrefix (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j+1 => tallyPrefix f j+(f j).toNat

theorem tally_le (f : ℕ → Bool) (j : ℕ) : tallyPrefix f j ≤ j := by
  induction j with
  | zero => rfl
  | succ j ih => have := (f j).toNat_le;simp only [tallyPrefix];omega

theorem tally_card (f : ℕ → Bool) (j : ℕ) : tallyPrefix f j=(Finset.univ.filter fun i : Fin j => f i.val=true).card := by
  have sum (n : ℕ) : tallyPrefix f n=∑ i : Fin n, (f i.val).toNat := by
    induction n with
    | zero => simp [tallyPrefix]
    | succ n ih => rw [tallyPrefix,Fin.sum_univ_castSucc,ih];rfl
  rw [sum,Finset.card_filter]
  apply Finset.sum_congr rfl;intro i _;cases h : f i.val <;> simp [h]

structure Counting (w : Layout) (B start T : ℕ) (f : ℕ → Bool) (d : Data) (j : ℕ) (z : Data) : Prop where
  fits : z.bank.Fits B
  counter : z.bank.mem (w.reg .parity)=j
  tally : z.bank.mem (w.reg .votes)=tallyPrefix f j
  cursor : z.bank.mem (w.reg .coinPos)=start+j*T
  frame : ∀ i, 14 ≤ i → i≠w.reg .parity → i≠w.reg .votes → i≠w.reg .coinPos → z.bank.mem i=d.bank.mem i
  port : z.port=d.port
  output : z.bank.out=d.bank.out
  epoch : z.epoch=d.epoch+j

private theorem named {w : Layout} {a b : Reg} (h : a.index≠b.index) : w.reg a≠w.reg b := by
  simp [Layout.reg,Layout.slot,cell,h]

theorem all_votes (w : Layout) (Q : Program) (τ : Tapes) (B T start N : ℕ) (x : List Bool) (f : ℕ → Bool) (d : Data)
    (fit : d.bank.Fits B) (clock : (d.epoch+N).size ≤ B) (zero : d.bank.mem (w.reg .zero)=0)
    (one : d.bank.mem (w.reg .one)=1) (dim : d.bank.mem (w.reg .inputLen)=x.length)
    (fuel : d.bank.mem (w.reg .span)=T) (ptr : d.bank.mem (w.reg .coinPos)=start)
    (stop : d.bank.mem (w.reg .repeats)=N) (tally : d.bank.mem (w.reg .votes)=0)
    (port : ∀ i<x.length,d.port i=bitVal x[i]?)
    (calls : ∀ j<N,Q.RunsIn (runTapes x (CoinWindow.window τ.coins (start+j*T) T)) T (some [f j]))
    (cursor : (start+N*T).size ≤ B) :
    ∃ t j, Eval Q τ B (indexLoop w .parity .repeats (vote w)) d t j ∧
      j ≤ 2+N*(T+11) ∧ Counting w B start T f d N t := by
  let I := Counting w B start T f d
  let p := w.reg .parity
  let base : Data := {d with bank := d.bank.write p 0}
  have set := setWord Q τ B p 0 d fit (by simp)
  have first : I 0 base := by
    refine ⟨set.2,by simp [base,p,Store.write],?_,?_,?_,rfl,rfl,by simp [base]⟩
    · simp [base,p,Store.write,named (by decide : Reg.votes.index≠Reg.parity.index),tally,tallyPrefix]
    · simp [base,p,Store.write,named (by decide : Reg.coinPos.index≠Reg.parity.index),ptr]
    · intro i hi neq _ _;simp [base,p,Store.write,neq]
  have keep {j z} (h : I j z) (r : Reg) (p₀ : r.index≠Reg.parity.index)
      (p₁ : r.index≠Reg.votes.index) (p₂ : r.index≠Reg.coinPos.index) :
      z.bank.mem (w.reg r)=d.bank.mem (w.reg r) := h.frame _ (w.high r) (named p₀) (named p₁) (named p₂)
  have regs : ∀ j z, I j z → z.bank.Fits B ∧ z.bank.mem (w.reg .repeats)=N ∧ z.bank.mem p=j := by
    intro j z h;exact ⟨h.fits,(keep h .repeats (by decide) (by decide) (by decide)).trans stop,h.counter⟩
  have Nsize : N.size ≤ B := stop ▸ fit (w.reg .repeats)
  have next : ∀ j<N, ∀ z, I j z → ∃ t k, Eval Q τ B (.seq (vote w) (inc w .parity)) z t k ∧ k ≤ T+9 ∧ I (j+1) t := by
    intro j hj z h
    have paid : z.epoch.size ≤ B := (Nat.size_le_size (by rw [h.epoch];omega : z.epoch ≤ d.epoch+N)).trans clock
    have count : (z.bank.mem (w.reg .votes)+(f j).toNat).size ≤ B := by
      apply (Nat.size_le_size (n:=N) _).trans Nsize
      rw [h.tally];have := tally_le f j;have := (f j).toNat_le;omega
    have cap : (start+j*T+T).size ≤ B := by
      apply (Nat.size_le_size _).trans cursor
      have l := Nat.mul_le_mul_right T (show j+1 ≤ N by omega)
      rw [Nat.succ_mul] at l;omega
    have one' := (keep h .one (by decide) (by decide) (by decide)).trans one
    obtain ⟨u,i,run,cost,ufit,wrote⟩ := single_vote w Q τ B T (start+j*T) x (f j) z h.fits paid
      ((keep h .zero (by decide) (by decide) (by decide)).trans zero) one'
      ((keep h .inputLen (by decide) (by decide) (by decide)).trans dim)
      ((keep h .span (by decide) (by decide) (by decide)).trans fuel) h.cursor
      (fun i hi => by rw [h.port];exact port i hi) (calls j hj) count cap
    let t : Data := {u with bank := u.bank.write p (j+1)}
    have uone := (wrote.high _ (w.high .one) (named (by decide)) (named (by decide))).trans one'
    have up := (wrote.high _ (w.high .parity) (named (by decide)) (named (by decide))).trans h.counter
    have inc := stepCounter w .parity Q τ B j u ufit uone up ((Nat.size_le_size hj).trans Nsize)
    refine ⟨t,i+1,run.seq inc.1,by omega,inc.2,by simp [t,p,Store.write],?_,?_,?_,
      wrote.port.trans h.port,wrote.output.trans h.output,?_⟩
    · simp only [t,p,Store.write,Function.update_of_ne (named (by decide : Reg.votes.index≠Reg.parity.index)),wrote.tally,h.tally,tallyPrefix]
    · simp only [t,p,Store.write,Function.update_of_ne (named (by decide : Reg.coinPos.index≠Reg.parity.index)),wrote.cursor,Nat.succ_mul,Nat.add_assoc]
    · intro i hi i0 i1 i2
      change (u.bank.write p (j+1)).mem i=d.bank.mem i
      change i≠p at i0
      simp only [Store.write,Function.update_of_ne i0]
      exact (wrote.high i hi i1 i2).trans (h.frame i hi i0 i1 i2)
    · change u.epoch=d.epoch+(j+1)
      rw [wrote.epoch,h.epoch,Nat.add_assoc]
  obtain ⟨t,k,loop,cost,out⟩ := counted (w.reg .repeats) p _ N (T+9) I regs next 0 (Nat.zero_le _) base first
  refine ⟨t,_,set.1.seq loop,?_,out⟩
  simp only [Nat.sub_zero] at cost
  have eq : T+9+2=T+11 := by omega
  rw [eq] at cost;omega

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph GroupIsolation

private theorem enc_len (n : ℕ) : (encNat n).length=2*n.size+1 := by
  have flat (l : List Bool) : (l.flatMap fun b => [true,b]).length=2*l.length := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons,ih];omega
  simp [encNat,flat,Nat.size_eq_bits_len]

private theorem data_bound {α β : Type*} (l : List α) (g : α → List β) (L : ℕ)
    (h : ∀ a, (g a).length ≤ L) :
    (l.flatMap g).length ≤ l.length*L := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    have := h a;omega

private theorem enc_bound (n : ℕ) : (encNat n).length ≤ 2*n+1 := by
  have small : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [enc_len];omega

private theorem encoded_bound {n m : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ) (s t : Fin n)
    (W B : ℕ) (weights : ∀ i,w i ≤ W) :
    0<(encodeParityInstance n m tail head w s t B).length ∧
    (encodeParityInstance n m tail head w s t B).length ≤
      (2*n+1)+(2*m+1)+m*(4*n+2*W+3)+(2*n+1)+(2*n+1)+(2*B+2) := by
  have bound (i : Fin m) : (encNat (tail i)++encNat (head i)++encNat (w i)).length ≤ 4*n+2*W+3 := by
    simp only [List.length_append]
    have A := enc_bound (tail i);have C := enc_bound (head i);have V := enc_bound (w i)
    have u := (tail i).isLt;have v := (head i).isLt;have l := weights i;omega
  have mid := data_bound (List.finRange m) _ (4*n+2*W+3) bound
  have N := enc_bound n;have M := enc_bound m;have S := enc_bound s;have T := enc_bound t;have ww := enc_bound B
  have ns := s.isLt;have nt := t.isLt;have nonempty := enc_len n
  simp only [List.length_finRange] at mid
  simp only [encodeParityInstance,List.length_append,encInt,List.length_cons,Int.natAbs_natCast]
  constructor <;> omega

/-- Every admitted query has a nonempty raw encoding of polynomial length, including
its padded loops and the sampled target. A rejected draw is represented by the empty string. -/
theorem candidate_size {n : ℕ} (adj : Fin n → Fin n → Bool) (z : Draw n) {x : List Bool}
    (ok : candidateInput adj z=some x) : 0<x.length ∧ x.length ≤ 120*(n+1)^4 := by
  let s := z.1.1
  let t := z.1.2
  let a := pathAdj adj s t
  let hs := clean_no_in adj s t
  let w := labelWeight s (restrictedSeed a s z.2.1).2
  let S := fun i => copyMask ((restrictedSeed a s z.2.1).1 i)
  let H := inputGraph a S s
  change (if s≠t ∧ adj t s=true then some (parityInput a S s t hs w z.2.2.val) else none)=some x at ok
  split at ok
  next accept =>
    have eq : parityInput a S s t hs w z.2.2.val=x := Option.some.inj ok
    have weights (i : Fin (n*n*3)) : inputWeight a S s hs w i ≤ Wmax n := by
      unfold inputWeight paddedWeight
      cases h : decodeSlot a S i with
      | none => exact Nat.zero_le _
      | some copy =>
        change (((restrictedSeed a s z.2.1).2 (dest a S s hs copy,copy.2.1)).val+1) ≤ Wmax n
        have digit := ((restrictedSeed a s z.2.1).2 (dest a S s hs copy,copy.2.1)).isLt
        rwa [weightRange s] 
    have run := encoded_bound H.tail H.head (inputWeight a S s hs w) s t (Wmax n) z.2.2.val weights
    rw [←eq];refine ⟨run.1,run.2.trans ?_⟩
    have wm : Wmax n ≤ 6*n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have wb : z.2.2.val ≤ 6*(n*n) := by
      have h := z.2.2.isLt;change z.2.2.val<(n-1)*Wmax n+1 at h
      have u := Nat.mul_le_mul (Nat.sub_le n 1) wm
      nlinarith only [h,u]
    have slots := Nat.mul_le_mul_left (n*n*3) (show 4*n+2*Wmax n+3 ≤ 16*n+3 by omega)
    nlinarith only [slots,wm,wb,Nat.zero_le n,Nat.zero_le (n*n),Nat.zero_le (n*n*n),Nat.zero_le (n^4)]
  next => contradiction

end DirectedHamiltonicity.Main.CycleReduction

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers FiniteSampling

def trialRank (n : ℕ) (coins : List Bool) (i : ℕ) := (binaryRank (seedWidth n) fun b =>
  coins[i*seedWidth n+b.val]?.getD false).val

def queryData {n : ℕ} (adj : Fin n → Fin n → Bool) (rank : ℕ) : Option (List Bool) :=
  if h : rank<drawCount n then candidateInput adj ((rankDraw n).symm ⟨rank,h⟩) else none

theorem raw_seed (n T : ℕ) (coins : List Bool) (i : Fin (trials n)) :
    (binaryRank _ ((panelFromTape n T coins).1 i)).val=trialRank n coins i := by
  unfold trialRank
  apply congrArg (fun b => (binaryRank _ b).val)
  funext k
  change coins[k.val+seedWidth n*i.val]?.getD false=_
  rw [Nat.mul_comm (seedWidth n),Nat.add_comm]

theorem coin_segment (n T : ℕ) (coins : List Bool) (i : Fin (2*majorityHalf n)) :
    List.ofFn ((panelFromTape n T coins).2 i)=CoinWindow.window coins (trials n*seedWidth n+i.val*T) T := by
  apply congrArg List.ofFn;funext k
  change coins[trials n*seedWidth n+(k.val+T*i.val)]?.getD false=_
  change _=coins[(trials n*seedWidth n+i.val*T)+k.val]?.getD false
  rw [Nat.mul_comm T];congr 2 <;> omega

theorem selected_query {n : ℕ} (adj : Fin n → Fin n → Bool) (T : ℕ) (coins : List Bool) (i : Fin (trials n)) :
    ((decodeRank (rankDraw n) ((panelFromTape n T coins).1 i)).bind (candidateInput adj))=
      queryData adj (trialRank n coins i) := by
  unfold decodeRank queryData
  dsimp only
  rw [raw_seed]
  split <;> rfl

/-- The bit returned by the native majority counter is the formal verified-query value;
every individual call meets the same allowance on the corresponding finite tape. -/
theorem trial_interface {n : ℕ} (adj : Fin n → Fin n → Bool) (Q : Program) (A k : ℕ) (time : QueryTime Q A k)
    (coins : List Bool) (i : Fin (trials n)) :
    let T := coinSpan A k n
    let r := majorityHalf n
    let base := trials n*seedWidth n
    let x := (queryData adj (trialRank n coins i)).getD []
    let panel := panelFromTape n T coins
    let yes := verifiedQuery Q adj r T (panel.1 i) panel.2
    (x=[] ∧ yes=false) ∨
      (0<x.length ∧ x.length ≤ 120*(n+1)^4 ∧ ∃ f : ℕ → Bool,
        (∀ j<2*r,Q.RunsIn (runTapes x (CoinWindow.window coins (base+j*T) T)) T (some [f j])) ∧
        decide (r<tallyPrefix f (2*r))=yes) := by
  dsimp only
  let T := coinSpan A k n
  let r := majorityHalf n
  let start := trials n*seedWidth n
  let panel := panelFromTape n T coins
  let rank := trialRank n coins i
  unfold verifiedQuery
  rw [selected_query]
  cases q : queryData adj (trialRank n coins i) with
  | none => left;exact ⟨rfl,rfl⟩
  | some x =>
    change queryData adj rank=some x at q
    have h : ∃ z : Draw n, candidateInput adj z=some x := by
      unfold queryData at q
      split at q
      · exact ⟨_,q⟩
      · contradiction
    obtain ⟨z,accepted⟩ := h
    obtain ⟨pos,size⟩ := candidate_size adj z accepted
    let f := fun j => outputBit Q x (CoinWindow.window coins (start+j*T) T)
    refine Or.inr ⟨pos,size,f,?_,?_⟩
    · intro j hj
      obtain ⟨fee,⟨terminal,halt,work,out⟩,bounded⟩ := time adj z x accepted (CoinWindow.window coins (start+j*T) T)
      exact ⟨terminal,halt,work.trans bounded,out⟩
    · change decide (r<tallyPrefix f (2*r))=majority (fun c => outputBit Q x (List.ofFn c)) r panel.2
      rw [tally_card];unfold majority
      congr 2
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro j _
      change outputBit Q x (CoinWindow.window coins (start+j.val*T) T)=true ↔ _
      rw [←coin_segment n T coins j]

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word BinaryStack OuterMachine FiniteSampling

/-- The chosen instance builder uses a fixed argument bank above its own temporary registers. -/
def Encoder (w : Layout) (prepare : Cmd) (required work : Polynomial ℕ) :=
  ∀ (width n a r : ℕ) (adj : Fin n → Fin n → Bool) (τ : Tapes) (s : Store) (B : ℕ),
    required.eval width ≤ B → s.Fits B → n ≤ width → n<2^width → a<2^width → r<2^width →
    (∀ u v : Fin n, a.testBit (v.val+n*u.val)=adj u v) →
    s.mem (cell w.args)=n → s.mem (cell (w.args+1))=a → s.mem (cell (w.args+2))=r →
    s.mem (cell (w.args+3))=2^width →
    ∃ t k, Exec τ (fun v => v.Fits B) prepare s t k ∧ k ≤ work.eval B ∧
      t.mem 0=packed ((queryData adj r).getD []) ∧ t.out=s.out ∧
      ∀ i, w.floor ≤ i → t.mem (cell i)=s.mem (cell i)

theorem encoder_exists : ∃ w c p q, Encoder w c p q := by
  obtain ⟨floor,code,room,time,run⟩ := prepare_cycle_parity_query_ram
  let w : Layout := ⟨floor⟩
  refine ⟨w,code w.args,room,time,?_⟩
  intro width n a r adj τ s B cap fits nW nw aw rw g n1 a1 r1 width1
  obtain ⟨t,k,ex,b,out,frame⟩ := run w.args width n a r adj τ s B (by dsimp [w,Layout.args];omega) cap fits nW nw aw rw g n1 a1 r1 width1
  refine ⟨t,k,ex,b,?_,frame⟩
  by_cases small : r<drawCount n <;> simpa [queryData,small] using out

structure Encoded (w : Layout) (s t : Store) (x : List Bool) (next : ℕ) : Prop where
  word : t.mem 0=packed x
  cursor : t.mem (w.reg .seedStart)=next
  output : t.out=s.out
  frame : ∀ r, w.floor+128 ≤ r → cell r≠w.reg .seedStart → t.mem (cell r)=s.mem (cell r)

private theorem arg_low (w : Layout) (r : Reg) (j : ℕ) (h : j≤3) :
    w.reg r ≠ cell (w.args+j) := by unfold Layout.reg Layout.slot Layout.args cell;omega

set_option maxHeartbeats 900000 in
theorem encode_trial (w : Layout) (prepare : Cmd) (P J : Polynomial ℕ) (enc : Encoder w prepare P J)
    (n g i B : ℕ) (adj : Fin n → Fin n → Bool) (τ : Tapes) (s : Store) (fit : s.Fits B)
    (dim : s.mem (w.reg .n)=n) (graph : s.mem (w.reg .candidate)=g)
    (repr : ∀ u v : Fin n, g.testBit (v.val+n*u.val)=adj u v)
    (small : g<2^(n+n*n+seedWidth n+1)) (cap : P.eval (n+n*n+seedWidth n+1) ≤ B)
    (size : seedWidth n+1 ≤ B) (endSize : (i*seedWidth n+seedWidth n).size ≤ B)
    (zero : s.mem (w.reg .zero)=0) (one : s.mem (w.reg .one)=1)
    (cursor : s.mem (w.reg .seedStart)=i*seedWidth n) (seed : s.mem (w.reg .seedWidth)=seedWidth n)
    (radix : s.mem (w.reg .radix)=2^(n+n*n+seedWidth n+1)) (hb : 2 ≤ B) :
    ∃ t k, Exec τ (fun b => b.Fits B) (prepareTrial w prepare) s t k ∧
      k ≤ 9*seedWidth n+10+J.eval B ∧
      Encoded w s t ((queryData adj (trialRank n τ.coins i)).getD []) (i*seedWidth n+seedWidth n) := by
  let sh := seedWidth n
  let start := i*sh
  let width := n+n*n+sh+1
  let rank := trialRank n τ.coins i
  let a := ((seedArgs w).run τ s).last
  have far (r : Reg) (j : ℕ) (h : j<14) : w.reg r≠j := by have := w.high r;omega
  have n1 : (1:ℕ).size ≤ B := one ▸ fit (w.reg .one)
  have ns : (i*seedWidth n).size ≤ B := cursor ▸ fit (w.reg .seedStart)
  have bytes : ((seedArgs w).run τ s).writeWidth ≤ B := by
    simp (disch := decide) [seedArgs,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,Function.update_apply,
      far,zero,one,cursor,seed,ns,endSize];omega
  have init : Exec τ (fun v => v.Fits B) (seedArgs w).cmd s a 3 := (seedArgs w).exec τ s B fit bytes
  have initRegs : a.mem 0=start+sh ∧ a.mem 1=start ∧ a.mem 2=1 := by
    simp (disch := decide) [a,start,sh,seedArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,far,zero,one,cursor,seed]
  have aHigh (j : ℕ) (h : 14≤j) : a.mem j=s.mem j := by
    simp (disch := omega) [a,seedArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
  obtain ⟨b,j,read,readTime,_,raw,bout,frame⟩ := TapeReader.readRank_exec .coin (τ:=τ) Fin.valEmbedding a start sh
    initRegs.1 initRegs.2.1 initRegs.2.2 (init.post fit) hb size
  change b.mem 4=(binaryRank sh fun i => τ.coins[start+i.val]?.getD false).val at raw
  change b.mem 4=rank at raw
  have bHigh (j : ℕ) (h : 14≤j) : b.mem j=s.mem j :=
    (frame j (by change j≠0;omega) (by change j≠3;omega) (by change j≠4;omega)).trans (aHigh j h)
  have bReg (r : Reg) := bHigh (w.reg r) (w.high r)
  let c := ((encodeArgs w).run τ b).last
  have no (r : Reg) (j : ℕ) (h : j≤3) := arg_low w r j h
  have no0 (r : Reg) : w.reg r≠cell w.args := by simpa using no r 0 (by decide)
  have rankSize : rank.size ≤ B := raw ▸ (read.post (init.post fit)) 4
  have nSize := dim ▸ fit (w.reg .n);have gSize := graph ▸ fit (w.reg .candidate)
  have radSize := radix ▸ fit (w.reg .radix)
  have cbytes : ((encodeArgs w).run τ b).writeWidth ≤ B := by
    simp (disch := decide) [encodeArgs,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,Function.update_apply,
      no,no0,bReg,zero,one,cursor,seed,raw,dim,graph,radix,rankSize,nSize,gSize,radSize,endSize]
  have args : Exec τ (fun v => v.Fits B) (encodeArgs w).cmd b c 5 := (encodeArgs w).exec τ b B (read.post (init.post fit)) cbytes
  have cm : c.mem=Function.update (Function.update (Function.update (Function.update
      (Function.update b.mem (cell (w.args+2)) rank) (cell w.args) n) (cell (w.args+1)) g)
      (cell (w.args+3)) (2^width)) (w.reg .seedStart) (start+sh) := by
    simp (disch := decide) [c,encodeArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      no,no0,bReg,zero,cursor,seed,raw,dim,graph,radix,width,start,sh]
  have av : c.mem (cell w.args)=n ∧ c.mem (cell (w.args+1))=g ∧ c.mem (cell (w.args+2))=rank ∧
      c.mem (cell (w.args+3))=2^width ∧ c.mem (w.reg .seedStart)=start+sh := by
    simp (disch := omega) [cm,Function.update_apply,cell,Layout.args,Layout.reg,Layout.slot,Reg.index]
  have nw : n<2^width := Nat.lt_of_lt_of_le (Nat.lt_two_pow_self (n:=n)) (Nat.pow_le_pow_right (by decide) (by dsimp [width];omega))
  have rsize : rank<2^sh := (binaryRank sh (fun b => τ.coins[start+b.val]?.getD false)).isLt
  have rword : rank<2^width := rsize.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [width];omega))
  obtain ⟨t,l,run,work,word,out,ret⟩ := enc width n g rank adj τ c B cap (args.post (read.post (init.post fit)))
    (by dsimp [width];omega) nw small rword repr av.1 av.2.1 av.2.2.1 av.2.2.2.1
  have fix (r : ℕ) (above : w.floor+128 ≤ r) (neq : cell r≠w.reg .seedStart) : c.mem (cell r)=s.mem (cell r) := by
    have sep (j : ℕ) (h : j≤3) : cell r≠cell (w.args+j) := by unfold cell Layout.args;omega
    have sep0 : cell r≠cell w.args := by simpa using sep 0 (by decide)
    simp (disch := decide) [cm,Function.update_apply,neq,sep,sep0,bHigh (cell r) (by unfold cell;omega)]
  refine ⟨t,_,init.seq (read.seq (args.seq run)),by omega,word,?_,out.trans bout,?_⟩
  · exact (ret (w.slot .seedStart) (by unfold Layout.slot;omega)).trans av.2.2.2.2
  · intro r hi neq;exact (ret _ (by omega)).trans (fix _ hi neq)

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word BinaryStack OuterMachine

structure Ready (w : Layout) (d t : Data) (x : List Bool) : Prop where
  length : t.bank.mem (w.reg .inputLen)=x.length
  input : ∀ i<x.length,t.port i=bitVal x[i]?
  high : ∀ i, 10 ≤ i → cell i≠w.reg .inputLen → t.bank.mem (cell i)=d.bank.mem (cell i)
  output : t.bank.out=d.bank.out
  epoch : t.epoch=d.epoch

theorem ready (w : Layout) (Q : Program) (τ : Tapes) (B : ℕ) (d : Data) (x : List Bool)
    (word : d.bank.mem 0=packed x) (zero : d.bank.mem (w.reg .zero)=0) (fit : d.bank.Fits B)
    (room : x.length+3 ≤ B) :
    ∃ t j, Eval Q τ B (loadPort w) d t j ∧ j ≤ 6+(x.length+1)*loadUnit B ∧ t.bank.Fits B ∧ Ready w d t x := by
  let a : Data := {d with bank := (initPort.run τ d.bank).last}
  have wval : (packed x).size ≤ B := word ▸ fit 0
  have bytes : (initPort.run τ d.bank).writeWidth ≤ B := by
    simp [initPort,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      cell,word,wval,packed_size,show (2:ℕ).size=2 by rfl];omega
  have run : Exec τ (fun v => v.Fits B) initPort.cmd d.bank a.bank 5 := initPort.exec τ d.bank B fit bytes
  have aFit := run.post fit
  have init : Constants a.bank ∧ a.bank.mem (cell 8)=packed x ∧ a.bank.mem (cell 9)=0 := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩ <;> simp [a,initPort,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,cell,word]
  have aHigh (i : ℕ) (h : 10 ≤ i) : a.bank.mem (cell i)=d.bank.mem (cell i) := by
    simp (disch := omega) [a,initPort,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,cell]
  have lengthSize : x.length.size ≤ B := (show x.length.size ≤ x.length from Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  obtain ⟨u,k,loop,steps,uFit,frame⟩ := load_loop Q τ B x 0 a init.2.1 init.2.2 init.1 aFit room (by simpa using lengthSize)
  let t : Data := {u with bank := u.bank.write (w.reg .inputLen) x.length}
  have H0 : 10 ≤ w.slot .zero := by unfold Layout.slot;omega
  have saved := (frame.high (w.slot .zero) H0).trans (aHigh _ H0)
  have uZero : u.bank.mem (w.reg .zero)=0 := saved.trans zero
  have cursor : u.bank.mem (cell 9)=x.length := by simpa using frame.cursor
  have tFit : t.bank.Fits B := Store.write_fits uFit _ lengthSize
  have eq : (Op.add (w.reg .inputLen) (cell 9) (w.reg .zero)).eval τ u.bank=t.bank := by simp [Op.eval,cursor,uZero,t]
  have write : Exec τ (fun v => v.Fits B) (.op (.add (w.reg .inputLen) (cell 9) (w.reg .zero))) u.bank t.bank 1 := by
    rw [←eq];exact .op _ _ (eq.symm ▸ tFit)
  refine ⟨t,_,(Eval.pure fit run).seq (loop.seq (Eval.pure uFit write)),by omega,tFit,by simp [t,Store.write],?_,?_,frame.output,frame.epoch⟩
  · intro i hi
    have h := frame.range i hi
    simpa [t,List.getElem?_eq_getElem hi,bitVal] using h
  · intro i hi diff
    change (u.bank.write (w.reg .inputLen) x.length).mem (cell i)=d.bank.mem (cell i)
    simp only [Store.write,Function.update_of_ne diff]
    exact (frame.high i hi).trans (aHigh i hi)

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word BinaryStack OuterMachine

def scoreWrites (w : Layout) : Finset ℕ :=
  {w.reg .accepted,w.reg .inputLen,w.reg .votes,w.reg .coinPos,w.reg .parity}

structure Scored (w : Layout) (d t : Data) (out : Bool) (N : ℕ) : Prop where
  result : t.bank.mem (w.reg .accepted)=out.toNat
  high : ∀ i, 10 ≤ i → cell i ∉ scoreWrites w → t.bank.mem (cell i)=d.bank.mem (cell i)
  output : t.bank.out=d.bank.out
  epoch : t.epoch=d.epoch+N

private theorem slot_big (w : Layout) (r : Reg) : 10 ≤ w.slot r := by unfold Layout.slot;omega
private theorem reg_ne {w : Layout} {r s : Reg} (h : r.index≠s.index) : w.reg r≠w.reg s := by
  simp [Layout.reg,Layout.slot,cell,h]

theorem score (w : Layout) (Q : Program) (τ : Tapes) (B T start r : ℕ) (d : Data) (x : List Bool)
    (f : ℕ → Bool) (prev : Bool) (fit : d.bank.Fits B) (room : x.length+3 ≤ B)
    (packedInput : d.bank.mem 0=packed x) (zero : d.bank.mem (w.reg .zero)=0)
    (one : d.bank.mem (w.reg .one)=1) (fuel : d.bank.mem (w.reg .span)=T)
    (base : d.bank.mem (w.reg .parityStart)=start) (half : d.bank.mem (w.reg .half)=r)
    (stop : d.bank.mem (w.reg .repeats)=2*r) (old : d.bank.mem (w.reg .accepted)=prev.toNat)
    (epoch : (d.epoch+2*r).size ≤ B) (cursor : (start+(2*r)*T).size ≤ B)
    (calls : ∀ j<2*r,Q.RunsIn (runTapes x (CoinWindow.window τ.coins (start+j*T) T)) T (some [f j])) :
    ∃ t j, Eval Q τ B (scoreTrial w) d t j ∧
      j ≤ 15+(x.length+1)*loadUnit B+2*r*(T+11) ∧ t.bank.Fits B ∧
      Scored w d t (prev || decide (r<tallyPrefix f (2*r))) (2*r) := by
  obtain ⟨a,k,load,loadTime,afit,port⟩ := ready w Q τ B d x packedInput zero fit room
  let b : Data := {a with bank := ((initVotes w).run τ a.bank).last}
  have aReg (s : Reg) (h : s.index≠Reg.inputLen.index) : a.bank.mem (w.reg s)=d.bank.mem (w.reg s) :=
    port.high (w.slot s) (slot_big w s) (reg_ne h)
  have az := (aReg .zero (by decide)).trans zero
  have startA := (aReg .parityStart (by decide)).trans base
  have startB : start.size ≤ B := base ▸ fit (w.reg .parityStart)
  have initWidth : ((initVotes w).run τ a.bank).writeWidth ≤ B := by
    simp [initVotes,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      reg_ne (w:=w) (by decide : Reg.parityStart.index≠Reg.votes.index),
      reg_ne (w:=w) (by decide : Reg.zero.index≠Reg.votes.index),az,startA,startB]
  have init : Exec τ (fun s => s.Fits B) (initVotes w).cmd a.bank b.bank 2 := (initVotes w).exec τ a.bank B afit initWidth
  have bfit := init.post afit
  have bMem : b.bank.mem=Function.update (Function.update a.bank.mem (w.reg .votes) 0) (w.reg .coinPos) start := by
    simp [b,initVotes,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      reg_ne (w:=w) (by decide : Reg.parityStart.index≠Reg.votes.index),
      reg_ne (w:=w) (by decide : Reg.zero.index≠Reg.votes.index),az,startA]
  have keep (i : ℕ) (h : i≠w.reg .votes) (g : i≠w.reg .coinPos) : b.bank.mem i=a.bank.mem i := by
    rw [bMem];simp [h,g]
  have bReg (s : Reg) (hi : s.index≠Reg.inputLen.index) (hv : s.index≠Reg.votes.index) (hc : s.index≠Reg.coinPos.index) :
      b.bank.mem (w.reg s)=d.bank.mem (w.reg s) := (keep _ (reg_ne hv) (reg_ne hc)).trans (aReg s hi)
  have len := (keep _ (reg_ne (by decide : Reg.inputLen.index≠Reg.votes.index))
    (reg_ne (by decide : Reg.inputLen.index≠Reg.coinPos.index))).trans port.length
  have pos : b.bank.mem (w.reg .coinPos)=start := by rw [bMem];simp
  have count : b.bank.mem (w.reg .votes)=0 := by rw [bMem];simp [reg_ne (w:=w) (by decide : Reg.votes.index≠Reg.coinPos.index)]
  have ep : b.epoch=d.epoch := port.epoch
  obtain ⟨u,j,loop,time,c⟩ := all_votes w Q τ B T start (2*r) x f b bfit (by rw [ep];exact epoch)
    ((bReg .zero (by decide) (by decide) (by decide)).trans zero)
    ((bReg .one (by decide) (by decide) (by decide)).trans one) len
    ((bReg .span (by decide) (by decide) (by decide)).trans fuel) pos
    ((bReg .repeats (by decide) (by decide) (by decide)).trans stop) count port.input calls cursor
  have saved (s : Reg) (hi : s.index≠Reg.inputLen.index) (hp : s.index≠Reg.parity.index)
      (hv : s.index≠Reg.votes.index) (hc : s.index≠Reg.coinPos.index) :=
    (c.frame _ (by unfold Layout.reg cell;omega) (reg_ne (w:=w) hp) (reg_ne (w:=w) hv) (reg_ne (w:=w) hc)).trans (bReg s hi hv hc)
  have halved := (saved .half (by decide) (by decide) (by decide) (by decide)).trans half
  have prevBit := (saved .accepted (by decide) (by decide) (by decide) (by decide)).trans old
  have frame (i : ℕ) (hi : 10 ≤ i) (free : cell i ∉ scoreWrites w) : u.bank.mem (cell i)=d.bank.mem (cell i) := by
    simp only [scoreWrites,Finset.mem_insert,Finset.mem_singleton,not_or] at free
    obtain ⟨_,hL,hV,hC,hP⟩ := free
    exact (c.frame _ (by unfold cell;omega) hP hV hC).trans ((keep _ hV hC).trans (port.high _ hi hL))
  have output : u.bank.out=d.bank.out := c.output.trans port.output
  have clock : u.epoch=d.epoch+2*r := c.epoch.trans (congrArg (fun a => a+2*r) ep)
  by_cases small : tallyPrefix f (2*r) ≤ r
  · have cmp : u.bank.mem (w.reg .votes) ≤ u.bank.mem (w.reg .half) := by rw [c.tally,halved];exact small
    have check : Eval Q τ B (test w .votes .half nop (lit w .accepted 1)) u u (1+0) := .yes c.fits cmp (.pure c.fits (.skip _))
    refine ⟨u,_,load.seq ((Eval.pure afit init).seq (loop.seq check)),by omega,c.fits,?_,frame,output,clock⟩
    simpa [show ¬r<tallyPrefix f (2*r) by omega] using prevBit
  · have cmp : ¬u.bank.mem (w.reg .votes) ≤ u.bank.mem (w.reg .half) := by rw [c.tally,halved];exact small
    let t : Data := {u with bank := u.bank.write (w.reg .accepted) 1}
    have wr := setWord Q τ B (w.reg .accepted) 1 u c.fits (by change 1≤B;omega)
    have check : Eval Q τ B (test w .votes .half nop (lit w .accepted 1)) u t (1+1+1) := .no c.fits cmp wr.1
    refine ⟨t,_,load.seq ((Eval.pure afit init).seq (loop.seq check)),by omega,wr.2,?_,?_,output,clock⟩
    · simp [t,Store.write,show r<tallyPrefix f (2*r) by omega]
    · intro i hi free
      have fresh : cell i≠w.reg .accepted := by intro eq;apply free;simp [scoreWrites,eq]
      simp [t,Store.write,fresh,frame i hi free]

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured Word BinaryStack OuterMachine

noncomputable def trialVal (Q : Program) (A k : ℕ) {n : ℕ} (adj : Fin n → Fin n → Bool) (coins : List Bool)
    (i : Fin (trials n)) :=
  let z := panelFromTape n (coinSpan A k n) coins
  verifiedQuery Q adj (majorityHalf n) _ (z.1 i) z.2
noncomputable section

def trialFee (J : Polynomial ℕ) (B n T : ℕ) :=
  9*seedWidth n+28+J.eval B+(120*(n+1)^4+1)*loadUnit B+2*majorityHalf n*(T+11)

def transient (w : Layout) : Finset ℕ := insert (w.reg .seedStart) (scoreWrites w)

theorem regApart (w : Layout) {r s : Reg} (h : r.index≠s.index) : w.reg r≠w.reg s := by
  simp [Layout.reg,Layout.slot,cell,h]

theorem slotLarge (w : Layout) (r : Reg) : w.floor+128 ≤ w.slot r := Nat.le_add_right _ _

structure TrialConfig (w : Layout) (d : Data) (A k n g : ℕ) : Prop where
  dim : d.bank.mem (w.reg .n)=n
  graph : d.bank.mem (w.reg .candidate)=g
  zero : d.bank.mem (w.reg .zero)=0
  one : d.bank.mem (w.reg .one)=1
  seed : d.bank.mem (w.reg .seedWidth)=seedWidth n
  radix : d.bank.mem (w.reg .radix)=2^(n+n*n+seedWidth n+1)
  fuel : d.bank.mem (w.reg .span)=coinSpan A k n
  base : d.bank.mem (w.reg .parityStart)=trials n*seedWidth n
  half : d.bank.mem (w.reg .half)=majorityHalf n
  repeats : d.bank.mem (w.reg .repeats)=2*majorityHalf n

structure TrialSpace (P : Polynomial ℕ) (B A k n : ℕ) : Prop where
  encoder : P.eval (n+n*n+seedWidth n+1) ≤ B
  seed : seedWidth n+1 ≤ B
  cursor : (trials n*seedWidth n).size ≤ B
  tape : (coinCount n (coinSpan A k n)).size ≤ B
  port : 120*(n+1)^4+3 ≤ B

structure TrialResult (w : Layout) (d t : Data) (n i : ℕ) (b : Bool) : Prop where
  answer : t.bank.mem (w.reg .accepted)=b.toNat
  cursor : t.bank.mem (w.reg .seedStart)=(i+1)*seedWidth n
  clock : t.epoch ≤ d.epoch+2*majorityHalf n
  output : t.bank.out=d.bank.out
  frame : ∀ r : Reg, w.reg r ∉ transient w → t.bank.mem (w.reg r)=d.bank.mem (w.reg r)

theorem trial_run (w : Layout) (prepare : Cmd) (P J : Polynomial ℕ) (enc : Encoder w prepare P J)
    (Q : Program) (A k : ℕ) (qt : QueryTime Q A k) {n g B : ℕ} (adj : Fin n → Fin n → Bool)
    (d : Data) (τ : Tapes) (i : Fin (trials n)) (prev : Bool) (fit : d.bank.Fits B)
    (config : TrialConfig w d A k n g) (sp : TrialSpace P B A k n)
    (repr : ∀ u v : Fin n, g.testBit (v.val+n*u.val)=adj u v)
    (small : g < 2^(n+n*n+seedWidth n+1)) (epoch : (d.epoch+2*majorityHalf n).size ≤ B)
    (atI : d.bank.mem (w.reg .seedStart)=i.val*seedWidth n)
    (old : d.bank.mem (w.reg .accepted)=prev.toNat) :
    ∃ t j, Eval Q τ B (trialBody w prepare) d t j ∧ j ≤ trialFee J B n (coinSpan A k n) ∧
      t.bank.Fits B ∧ TrialResult w d t n i.val (prev || trialVal Q A k adj τ.coins i) := by
  let T := coinSpan A k n
  let r := majorityHalf n
  let x := (queryData adj (trialRank n τ.coins i.val)).getD []
  have hb : 2 ≤ B := by have := sp.port;omega
  have nextSize : (i.val*seedWidth n+seedWidth n).size ≤ B := by
    rw [←Nat.succ_mul];exact (Nat.size_le_size (Nat.mul_le_mul_right _ i.isLt)).trans sp.cursor
  obtain ⟨s,j,ex,time,encoded⟩ := encode_trial w prepare P J enc n g i.val B adj τ d.bank fit config.dim config.graph
    repr small sp.encoder sp.seed nextSize config.zero config.one atI config.seed config.radix hb
  let a : Data := {d with bank := s}
  have first : Eval Q τ B (.pure (prepareTrial w prepare)) d a j := .pure fit ex
  have afit : a.bank.Fits B := ex.post fit
  have kept (v : Reg) (h : v.index≠Reg.seedStart.index) : a.bank.mem (w.reg v)=d.bank.mem (w.reg v) :=
    encoded.frame (w.slot v) (slotLarge ..) (regApart w h)
  have aframe (v : Reg) (h : w.reg v ∉ transient w) : a.bank.mem (w.reg v)=d.bank.mem (w.reg v) :=
    encoded.frame _ (slotLarge ..) (by intro eq;exact h (Finset.mem_insert.mpr (Or.inl eq)))
  have ao := (kept .one (by decide)).trans config.one
  have ac : a.bank.mem (w.reg .seedStart)=(i.val+1)*seedWidth n := by
    rw [Nat.succ_mul];exact encoded.cursor
  have v := trial_interface adj Q A k qt τ.coins i
  change (x=[] ∧ trialVal Q A k adj τ.coins i=false) ∨
    (0 < x.length ∧ x.length ≤ 120*(n+1)^4 ∧ ∃ f : ℕ → Bool, (∀ j < 2*r,
    Q.RunsIn (runTapes x (CoinWindow.window τ.coins (trials n*seedWidth n+j*T) T)) T (some [f j])) ∧
    decide (r<tallyPrefix f (2*r))=trialVal Q A k adj τ.coins i) at v
  have ax : a.bank.mem 0=packed x := encoded.word
  rcases v with ⟨nil,result⟩|⟨pos,size,f,runs,yes⟩
  · have cmp : a.bank.mem 0 ≤ a.bank.mem (w.reg .one) := by rw [ax,ao,nil];rfl
    have tail : Eval Q τ B (.branch 0 (w.reg .one) nop (scoreTrial w)) a a (1+0) :=
      .yes afit cmp (.pure afit (.skip _))
    refine ⟨a,_,first.seq tail,?_,afit,?_,ac,by dsimp [a];omega,encoded.output,aframe⟩
    · unfold trialFee;omega
    · rw [result,Bool.or_false];exact (kept .accepted (by decide)).trans old
  · have cmp : ¬ a.bank.mem 0 ≤ a.bank.mem (w.reg .one) := by
      rw [ax,ao]
      have big (u : List Bool) (h : 0 < u.length) : ¬ packed u ≤ 1 := by
        cases u with
        | nil => contradiction
        | cons b xs => rw [packed_cons];have := packed_pos xs;omega
      exact big x pos
    obtain ⟨t,l,scored,cost,tf,res⟩ := score w Q τ B T _ r a x f prev afit (by have := sp.port;omega)
      ax ((kept .zero (by decide)).trans config.zero) ao ((kept .span (by decide)).trans config.fuel)
      ((kept .parityStart (by decide)).trans config.base) ((kept .half (by decide)).trans config.half)
      ((kept .repeats (by decide)).trans config.repeats) ((kept .accepted (by decide)).trans old) epoch sp.tape runs
    have seedFree : w.reg .seedStart ∉ scoreWrites w := by
      simp only [scoreWrites,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨regApart w (by decide),regApart w (by decide),regApart w (by decide),regApart w (by decide),regApart w (by decide)⟩
    refine ⟨t,_,first.seq (.no afit cmp scored),?_,tf,?_,(res.high _ (by have := slotLarge w .seedStart;omega) seedFree).trans ac,
      res.epoch.le,res.output.trans encoded.output,?_⟩
    · have sz := Nat.mul_le_mul_right (loadUnit B) (Nat.succ_le_succ size)
      change (x.length+1)*loadUnit B ≤ (120*(n+1)^4+1)*loadUnit B at sz
      unfold trialFee;dsimp [T,r] at cost;omega
    · rw [←yes];exact res.result
    · intro v hv
      have hf : w.reg v ∉ scoreWrites w := fun h => hv (Finset.mem_insert_of_mem h)
      exact (res.high _ (by have := slotLarge w v;omega) hf).trans (aframe v hv)

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured OuterMachine

/-- The body can leave the loop counter unchanged. Only the outer increment writes it. -/
theorem index_run (w : Layout) (counter stop : Reg) (body : Code) {Q : Program} {τ : Tapes}
    {B N fee : ℕ} (I : ℕ → Data → Prop) (d : Data) (fit : d.bank.Fits B) (initial : I 0 d)
    (fields : ∀ i s, I i s → s.bank.mem (w.reg stop)=N ∧ s.bank.mem (w.reg .one)=1)
    (stable : ∀ i s v, I i s → I i {s with bank := s.bank.write (w.reg counter) v})
    (next : ∀ i < N, ∀ s, s.bank.Fits B → I i s → s.bank.mem (w.reg counter)=i →
      ∃ t j, Eval Q τ B body s t j ∧ j ≤ fee ∧ t.bank.Fits B ∧ I (i+1) t ∧ t.bank.mem (w.reg counter)=i) :
    ∃ t j, Eval Q τ B (indexLoop w counter stop body) d t j ∧ j ≤ 2+N*(fee+3) ∧ t.bank.Fits B ∧ I N t := by
  let I' := fun i (s : Data) => I i s ∧ s.bank.Fits B ∧ s.bank.mem (w.reg counter)=i
  have ns : N.size ≤ B := (fields 0 d initial).1 ▸ fit (w.reg stop)
  have shape (i s) (h : I' i s) := And.intro h.2.1 (And.intro (fields i s h.1).1 h.2.2)
  have step (i : ℕ) (hi : i < N) (s : Data) (h : I' i s) :
      ∃ t j, Eval Q τ B (.seq body (inc w counter)) s t j ∧ j ≤ fee+1 ∧ I' (i+1) t := by
    obtain ⟨t,j,ex,cap,good,inv,atI⟩ := next i hi s h.2.1 h.1 h.2.2
    have bump := stepCounter w counter Q τ B i t good (fields _ t inv).2 atI ((Nat.size_le_size hi).trans ns)
    exact ⟨_,_,ex.seq bump.1,by omega,stable _ t _ inv,bump.2,by simp [Store.write]⟩
  have init := setWord Q τ B (w.reg counter) 0 d fit (Nat.zero_le _)
  obtain ⟨t,j,loop,cap,post⟩ := counted (w.reg stop) (w.reg counter) (.seq body (inc w counter)) N (fee+1) I'
    shape step 0 (by omega) _ ⟨stable _ _ _ initial,init.2,by simp [Store.write]⟩
  refine ⟨t,_,init.1.seq loop,?_,post.2.1,post.1⟩
  change j ≤ (N-0)*((fee+1)+2)+1 at cap
  rw [Nat.sub_zero,show fee+1+2=fee+3 by omega] at cap;omega

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers TargetedSamplers.Structured OuterMachine
open Classical in
noncomputable def prefixYes {N : ℕ} (v : Fin N → Bool) (i : ℕ) :=
  decide (∃ j, j.val < i ∧ v j=true)

theorem prefix_zero {N : ℕ} (v : Fin N → Bool) : prefixYes v 0=false := by classical simp [prefixYes]
theorem prefix_step {N : ℕ} (v : Fin N → Bool) (i : Fin N) :
    prefixYes v (i.val+1)=(prefixYes v i.val || v i) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [prefixYes,decide_eq_true_eq,Bool.or_eq_true]
  constructor
  · rintro ⟨j,h,a⟩
    by_cases smaller : j.val < i.val
    · exact Or.inl ⟨j,smaller,a⟩
    · have e : j=i := Fin.ext (by omega);exact Or.inr (e ▸ a)
  · rintro (⟨j,h,a⟩|a)
    · exact ⟨j,by omega,a⟩
    · exact ⟨i,by omega,a⟩

theorem regEq (w : Layout) (r s : Reg) : (w.reg r=w.reg s) ↔ r.index=s.index := by
  simp [Layout.reg,Layout.slot,Word.cell]
def trialLoopWrites (w : Layout) := insert (w.reg .trial) (transient w)
def Saved (w : Layout) (changes : Finset ℕ) (d t : Data) :=
  ∀ r : Reg, w.reg r ∉ changes → t.bank.mem (w.reg r)=d.bank.mem (w.reg r)

private theorem config_saved {w : Layout} {d t : Data} {A k n g : ℕ} (c : TrialConfig w d A k n g)
    (f : Saved w (trialLoopWrites w) d t) : TrialConfig w t A k n g := by
  constructor <;> (apply Eq.trans (f _ (by simp [trialLoopWrites,transient,scoreWrites,regEq,Reg.index])) <;> first
    | exact c.dim | exact c.graph | exact c.zero | exact c.one | exact c.seed | exact c.radix
    | exact c.fuel | exact c.base | exact c.half | exact c.repeats)

structure PanelState (w : Layout) {n : ℕ} (v : Fin (trials n) → Bool) (d s : Data) (i : ℕ) : Prop where
  result : s.bank.mem (w.reg .accepted)=(prefixYes v i).toNat
  cursor : s.bank.mem (w.reg .seedStart)=i*seedWidth n
  epoch : s.epoch ≤ d.epoch+i*(2*majorityHalf n)
  output : s.bank.out=d.bank.out
  frame : Saved w (trialLoopWrites w) d s

theorem panel_run (w : Layout) (prepare : Cmd) (P J : Polynomial ℕ) (enc : Encoder w prepare P J)
    (Q : Program) (A k : ℕ) (qt : QueryTime Q A k) {n g B : ℕ} (adj : Fin n → Fin n → Bool)
    (d : Data) (τ : Tapes) (fit : d.bank.Fits B) (config : TrialConfig w d A k n g)
    (sp : TrialSpace P B A k n) (repr : ∀ u v : Fin n, g.testBit (v.val+n*u.val)=adj u v)
    (small : g < 2^(n+n*n+seedWidth n+1)) (ep : (d.epoch+trials n*(2*majorityHalf n)).size ≤ B)
    (num : d.bank.mem (w.reg .trials)=trials n) (start : d.bank.mem (w.reg .seedStart)=0)
    (clear : d.bank.mem (w.reg .accepted)=0) :
    ∃ t j, Eval Q τ B (indexLoop w .trial .trials (trialBody w prepare)) d t j ∧
      j ≤ 2+trials n*(trialFee J B n (coinSpan A k n)+3) ∧ t.bank.Fits B ∧
      t.bank.mem (w.reg .accepted)=(twoSided Q adj (panelFromTape n (coinSpan A k n) τ.coins)).toNat ∧
      t.epoch ≤ d.epoch+trials n*(2*majorityHalf n) ∧ t.bank.out=d.bank.out ∧ Saved w (trialLoopWrites w) d t := by
  let v := trialVal Q A k adj τ.coins
  let I := fun i s => PanelState w v d s i
  have base : I 0 d := ⟨by simpa [prefix_zero] using clear,by simpa using start,by simp,rfl,fun _ _ => rfl⟩
  have fields (i s) (h : I i s) : s.bank.mem (w.reg .trials)=trials n ∧ s.bank.mem (w.reg .one)=1 :=
    ⟨(h.frame _ (by simp [trialLoopWrites,transient,scoreWrites,regEq,Reg.index])).trans num,(config_saved config h.frame).one⟩
  have stable (i s m) (h : I i s) : I i {s with bank := s.bank.write (w.reg .trial) m} := by
    refine ⟨?_,?_,h.epoch,h.output,?_⟩
    · simpa [Store.write,regEq,Reg.index] using h.result
    · simpa [Store.write,regEq,Reg.index] using h.cursor
    · intro a free
      have ne : w.reg a≠w.reg .trial := fun eq => free (Finset.mem_insert.mpr (Or.inl eq))
      simpa [Store.write,ne] using h.frame a free
  have step (i : ℕ) (lt : i < trials n) (s : Data) (fits : s.bank.Fits B) (h : I i s)
      (ptr : s.bank.mem (w.reg .trial)=i) : ∃ t j, Eval Q τ B (trialBody w prepare) s t j ∧
        j ≤ trialFee J B n (coinSpan A k n) ∧ t.bank.Fits B ∧ I (i+1) t ∧ t.bank.mem (w.reg .trial)=i := by
    let ix : Fin (trials n) := ⟨i,lt⟩
    have lim := Nat.mul_le_mul_right (2*majorityHalf n) lt
    rw [Nat.succ_mul] at lim
    have epoch : (s.epoch+2*majorityHalf n).size ≤ B :=
      (Nat.size_le_size (by have := h.epoch;omega)).trans ep
    obtain ⟨t,j,run,cost,tf,p⟩ := trial_run w prepare P J enc Q A k qt adj s τ ix (prefixYes v i) fits
      (config_saved config h.frame) sp repr small epoch h.cursor h.result
    have ret : t.bank.mem (w.reg .accepted)=(prefixYes v (i+1)).toNat := by rw [prefix_step v ix];exact p.answer
    refine ⟨t,j,run,cost,tf,⟨ret,p.cursor,?_,p.output.trans h.output,?_⟩,?_⟩
    · rw [Nat.succ_mul];have := h.epoch;have := p.clock;omega
    · intro r free
      exact (p.frame r (fun mem => free (Finset.mem_insert_of_mem mem))).trans (h.frame r free)
    · exact (p.frame _ (by simp [transient,scoreWrites,regEq,Reg.index])).trans ptr
  obtain ⟨t,j,ex,cost,tf,h⟩ := index_run w .trial .trials (trialBody w prepare) I d fit base fields stable step
  refine ⟨t,j,ex,cost,tf,?_,h.epoch,h.output,h.frame⟩
  convert h.result using 2
  simp [prefixYes,twoSided,v,trialVal]

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured OuterMachine RegisterCode
noncomputable section

def parameterLines (A k : ℕ) : List Line := [
  ⟨.three,.const 3⟩,
  ⟨.four,.const 4⟩,
  ⟨.six,.const 6⟩,
  ⟨.eight,.const 8⟩,
  ⟨.fifteen,.const 15⟩,
  ⟨.fortyNine,.const 49⟩,
  ⟨.fifty,.const 50⟩,
  ⟨.nSq,.arith .mul .n .n⟩,
  ⟨.tmp,.arith .pow .two .nSq⟩,
  ⟨.graph,.arith .mod .graph .tmp⟩,
  ⟨.nMinus,.sub .n .one⟩,
  ⟨.maxWeight,.arith .mul .six .nMinus⟩,
  ⟨.maxTotalPlus,.arith .mul .nMinus .maxWeight⟩,
  ⟨.maxTotalPlus,.add .maxTotalPlus .one⟩,
  ⟨.threeN,.arith .mul .three .n⟩,
  ⟨.tmp,.arith .pow .fifty .nSq⟩,
  ⟨.tmp2,.arith .pow .maxWeight .threeN⟩,
  ⟨.drawCount,.arith .mul .tmp .tmp2⟩,
  ⟨.drawCount,.arith .mul .drawCount .maxTotalPlus⟩,
  ⟨.drawCount,.arith .mul .drawCount .nSq⟩,
  ⟨.seedWidth,.clog .drawCount⟩,
  ⟨.blocks,.arith .mul .six .nSq⟩,
  ⟨.blocks,.add .blocks .six⟩,
  ⟨.tmp,.arith .pow .fifty .n⟩,
  ⟨.tmp2,.arith .pow .fortyNine .n⟩,
  ⟨.tmp,.add .tmp .tmp2⟩,
  ⟨.tmp,.sub .tmp .one⟩,
  ⟨.trials,.arith .div .tmp .tmp2⟩,
  ⟨.trials,.arith .mul .trials .four⟩,
  ⟨.trials,.arith .mul .trials .nSq⟩,
  ⟨.trials,.arith .mul .trials .maxTotalPlus⟩,
  ⟨.trials,.arith .mul .trials .blocks⟩,
  ⟨.tmp,.add .trials .one⟩,
  ⟨.half,.clog .tmp⟩,
  ⟨.half,.add .half .blocks⟩,
  ⟨.half,.add .half .half⟩,
  ⟨.repeats,.add .half .half⟩,
  ⟨.parityStart,.arith .mul .trials .seedWidth⟩,
  ⟨.tmp,.arith .pow .fifteen .n⟩,
  ⟨.tmp2,.arith .pow .eight .n⟩,
  ⟨.tmp,.add .tmp .tmp2⟩,
  ⟨.tmp,.sub .tmp .one⟩,
  ⟨.span,.arith .div .tmp .tmp2⟩,
  ⟨.tmp,.arith .mul .nSq .three⟩,
  ⟨.tmp,.add .tmp .n⟩,
  ⟨.tmp,.add .tmp .maxWeight⟩,
  ⟨.tmp,.add .tmp .one⟩,
  ⟨.tmp2,.const k⟩,
  ⟨.tmp,.arith .pow .tmp .tmp2⟩,
  ⟨.span,.arith .mul .span .tmp⟩,
  ⟨.tmp2,.const A⟩,
  ⟨.span,.arith .mul .span .tmp2⟩,
  ⟨.fieldWidth,.add .n .nSq⟩,
  ⟨.fieldWidth,.add .fieldWidth .seedWidth⟩,
  ⟨.fieldWidth,.add .fieldWidth .one⟩,
  ⟨.radix,.arith .pow .two .fieldWidth⟩]

def startLimit (i : ℕ) : Limit :=
  ⟨8*Polynomial.X^2+8,if i=Reg.n.index ∨ i=Reg.zero.index ∨ i=Reg.one.index ∨ i=Reg.two.index
    then some (Polynomial.X+2) else none⟩
def scheduleBudget (A k : ℕ) := budget startLimit (parameterLines A k)

structure Parameters (w : Layout) (s : Data) (A k n : ℕ) : Prop where
  zero : s.bank.mem (w.reg .zero)=0
  one : s.bank.mem (w.reg .one)=1
  two : s.bank.mem (w.reg .two)=2
  dim : s.bank.mem (w.reg .n)=n
  nSq : s.bank.mem (w.reg .nSq)=n*n
  seed : s.bank.mem (w.reg .seedWidth)=seedWidth n
  radix : s.bank.mem (w.reg .radix)=2^(n+n*n+seedWidth n+1)
  span : s.bank.mem (w.reg .span)=coinSpan A k n
  parityStart : s.bank.mem (w.reg .parityStart)=trials n*seedWidth n
  half : s.bank.mem (w.reg .half)=majorityHalf n
  repeats : s.bank.mem (w.reg .repeats)=2*majorityHalf n
  trials : s.bank.mem (w.reg .trials)=trials n

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1400000 in
private theorem computed (A k n g : ℕ) (v : Values)
    (dim : v Reg.n.index=n) (z : v Reg.zero.index=0) (o : v Reg.one.index=1)
    (two : v Reg.two.index=2) (old : v Reg.graph.index=g) :
    let f := result v (parameterLines A k)
    f Reg.zero.index=0 ∧
    f Reg.one.index=1 ∧
    f Reg.two.index=2 ∧
    f Reg.n.index=n ∧
    f Reg.nSq.index=n*n ∧
    f Reg.seedWidth.index=seedWidth n ∧
    f Reg.radix.index=2^(n+n*n+seedWidth n+1) ∧
    f Reg.span.index=coinSpan A k n ∧
    f Reg.parityStart.index=trials n*seedWidth n ∧
    f Reg.half.index=majorityHalf n ∧
    f Reg.repeats.index=2*majorityHalf n ∧
    f Reg.trials.index=trials n ∧
    f Reg.graph.index=g%2^(n*n) := by
  dsimp only
  let a1 : ℕ := 3
  let a2 : ℕ := 4
  let a3 : ℕ := 6
  let a4 : ℕ := 8
  let a5 : ℕ := 15
  let a6 : ℕ := 49
  let a7 : ℕ := 50
  let a8 : ℕ := (v Reg.n.index)*(v Reg.n.index)
  let a9 : ℕ := (v Reg.two.index)^a8
  let a10 : ℕ := (v Reg.graph.index)%a9
  let a11 : ℕ := (v Reg.n.index)-(v Reg.one.index)
  let a12 : ℕ := a3*a11
  let a13 : ℕ := a11*a12
  let a14 : ℕ := a13+(v Reg.one.index)
  let a15 : ℕ := a1*(v Reg.n.index)
  let a16 : ℕ := a7^a8
  let a17 : ℕ := a12^a15
  let a18 : ℕ := a16*a17
  let a19 : ℕ := a18*a14
  let a20 : ℕ := a19*a8
  let a21 : ℕ := Nat.clog 2 a20
  let a22 : ℕ := a3*a8
  let a23 : ℕ := a22+a3
  let a24 : ℕ := a7^(v Reg.n.index)
  let a25 : ℕ := a6^(v Reg.n.index)
  let a26 : ℕ := a24+a25
  let a27 : ℕ := a26-(v Reg.one.index)
  let a28 : ℕ := a27/a25
  let a29 : ℕ := a28*a2
  let a30 : ℕ := a29*a8
  let a31 : ℕ := a30*a14
  let a32 : ℕ := a31*a23
  let a33 : ℕ := a32+(v Reg.one.index)
  let a34 : ℕ := Nat.clog 2 a33
  let a35 : ℕ := a34+a23
  let a36 : ℕ := a35+a35
  let a37 : ℕ := a36+a36
  let a38 : ℕ := a32*a21
  let a39 : ℕ := a5^(v Reg.n.index)
  let a40 : ℕ := a4^(v Reg.n.index)
  let a41 : ℕ := a39+a40
  let a42 : ℕ := a41-(v Reg.one.index)
  let a43 : ℕ := a42/a40
  let a44 : ℕ := a8*a1
  let a45 : ℕ := a44+(v Reg.n.index)
  let a46 : ℕ := a45+a12
  let a47 : ℕ := a46+(v Reg.one.index)
  let a48 : ℕ := k
  let a49 : ℕ := a47^a48
  let a50 : ℕ := a43*a49
  let a51 : ℕ := A
  let a52 : ℕ := a50*a51
  let a53 : ℕ := (v Reg.n.index)+a8
  let a54 : ℕ := a53+a21
  let a55 : ℕ := a54+(v Reg.one.index)
  let a56 : ℕ := (v Reg.two.index)^a55
  have raw := Schedule.raw_values n A k
  dsimp only at raw
  unfold Schedule.ceilPower at raw
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change (v Reg.zero.index)=0
    exact z
  · change (v Reg.one.index)=1
    exact o
  · change (v Reg.two.index)=2
    exact two
  · change (v Reg.n.index)=n
    exact dim
  · change a8=n*n
    dsimp only [a8]
    simp only [dim,z,o,two,old]
  · change a21=seedWidth n
    dsimp only [a1,a3,a7,a8,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21]
    simp only [dim,z,o,two,old]
    exact raw.2.2.1
  · change a56=2^(n+n*n+seedWidth n+1)
    dsimp only [a1,a3,a7,a8,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a53,a54,a55,a56]
    simp only [dim,z,o,two,old]
    rw [←raw.2.2.1]
  · change a52=coinSpan A k n
    dsimp only [a1,a3,a4,a5,a8,a11,a12,a39,a40,a41,a42,a43,a44,a45,a46,a47,a48,a49,a50,a51,a52]
    simp only [dim,z,o,two,old]
    exact raw.2.2.2
  · change a38=trials n*seedWidth n
    dsimp only [a1,a2,a3,a6,a7,a8,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,a32,a38]
    simp only [dim,z,o,two,old]
    rw [←raw.1,←raw.2.2.1]
  · change a36=majorityHalf n
    dsimp only [a2,a3,a6,a7,a8,a11,a12,a13,a14,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,a32,a33,a34,a35,a36]
    simp only [dim,z,o,two,old]
    simpa only [two_mul] using raw.2.1
  · change a37=2*majorityHalf n
    dsimp only [a2,a3,a6,a7,a8,a11,a12,a13,a14,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,a32,a33,a34,a35,a36,a37]
    simp only [dim,z,o,two,old]
    rw [←raw.2.1];simp only [two_mul]
  · change a32=trials n
    dsimp only [a2,a3,a6,a7,a8,a11,a12,a13,a14,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,a32]
    simp only [dim,z,o,two,old]
    exact raw.1
  · change a10=g%2^(n*n)
    dsimp only [a8,a9,a10]
    simp only [dim,z,o,two,old]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem compute_parameters (w : Layout) (Q : Program) (τ : Tapes) (A k n g B : ℕ) (d : Data)
    (fit : d.bank.Fits B) (hb : 2 ≤ B) (startWidth : ∀ i, (peek w d i).size ≤ 8*(n+1)^2+8)
    (dim : d.bank.mem (w.reg .n)=n) (z : d.bank.mem (w.reg .zero)=0)
    (o : d.bank.mem (w.reg .one)=1) (two : d.bank.mem (w.reg .two)=2)
    (graph : d.bank.mem (w.reg .graph)=g) (space : (scheduleBudget A k).space.eval (n+1) ≤ B) :
    ∃ t j, Eval Q τ B (code w (parameterLines A k)) d t j ∧ j ≤ (scheduleBudget A k).time.eval (n+1) ∧
      t.bank.Fits B ∧ Parameters w t A k n ∧ t.bank.mem (w.reg .graph)=g%2^(n*n) ∧
      t.bank.out=d.bank.out ∧ t.epoch=d.epoch := by
  let v := peek w d
  have en : EFacts (n+1) v startLimit := by
    intro i
    refine ⟨by simpa [startLimit,v] using startWidth i,?_⟩
    intro p eq
    change (if _ then some _ else none)=some p at eq
    split at eq
    · rename_i h;cases eq
      rcases h with h|h|h|h <;> subst i <;> simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
      · change d.bank.mem (w.reg .n) ≤ _;omega
      · change d.bank.mem (w.reg .zero) ≤ _;omega
      · change d.bank.mem (w.reg .one) ≤ _;omega
      · change d.bank.mem (w.reg .two) ≤ _;omega
    · contradiction
  have certified : (budget startLimit (parameterLines A k)).ok=true := by rfl
  obtain ⟨width,time⟩ := budget_sound _ _ _ _ en certified
  obtain ⟨t,j,ex,cost,tf,ev,out,ep⟩ := run (Q:=Q) (τ:=τ) w (parameterLines A k) v d rfl fit hb (width.trans space)
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12⟩ := computed A k n g v dim z o two graph
  have cell (r : Reg) : t.bank.mem (w.reg r)=result v (parameterLines A k) r.index := congrFun ev r.index
  exact ⟨t,j,ex,cost.trans time,tf,⟨(cell .zero).trans p0,(cell .one).trans p1,(cell .two).trans p2,(cell .n).trans p3,(cell .nSq).trans p4,(cell .seedWidth).trans p5,(cell .radix).trans p6,(cell .span).trans p7,(cell .parityStart).trans p8,(cell .half).trans p9,(cell .repeats).trans p10,(cell .trials).trans p11⟩,(cell .graph).trans p12,out,ep⟩

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram.RegisterCode
open TargetedSamplers TargetedSamplers.Structured OuterMachine

def Expr.reads : Expr → Finset ℕ
  | .const _ => ∅
  | .add a b | .sub a b | .arith _ a b => {a.index,b.index}
  | .clog a => {a.index}
def reads : List Line → Finset ℕ
  | [] => ∅
  | a::as => a.rhs.reads ∪ (reads as).erase a.dst.index

private theorem expr_agree (e : Expr) (v u : Values) (h : ∀ i ∈ e.reads,v i=u i) :
    e.val v=e.val u ∧ e.width v=e.width u ∧ e.fee v=e.fee u := by
  cases e with
  | const x => exact ⟨rfl,rfl,rfl⟩
  | add a b | sub a b | arith _ a b =>
    have l := h a.index (by simp [Expr.reads]);have r := h b.index (by simp [Expr.reads])
    simp [Expr.width,Expr.val,Expr.fee,l,r]
  | clog a => simp [Expr.width,Expr.val,Expr.fee,h a.index (by simp [Expr.reads])]

private theorem cost_agree (cs : List Line) (v u : Values) (h : ∀ i ∈ reads cs,v i=u i) :
    width v cs=width u cs ∧ fee v cs=fee u cs := by
  induction cs generalizing v u with
  | nil => exact ⟨rfl,rfl⟩
  | cons a as ih =>
    obtain ⟨e,w,t⟩ := expr_agree a.rhs v u (fun i mem => h i (Finset.mem_union_left _ mem))
    have fr (i : ℕ) (mem : i ∈ reads as) : a.put v i=a.put u i := by
      by_cases eq : i=a.dst.index
      · subst i;simpa [Line.put] using e
      · simpa [Line.put,eq] using h i (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨eq,mem⟩))
    obtain ⟨w',t'⟩ := ih _ _ fr
    simp only [width,fee,w,t,w',t',and_self]

theorem analyzed_run {Q : Program} {τ : Tapes} {B : ℕ} (w : Layout) (cs : List Line) (en : ℕ → Limit)
    (n : ℕ) (d : Data) (fit : d.bank.Fits B) (hb : 2 ≤ B) (ok : (budget en cs).ok=true)
    (inputs : ∀ i ∈ reads cs,(en i).Holds n (peek w d i))
    (room : (budget en cs).space.eval n ≤ B) :
    ∃ t j, Eval Q τ B (code w cs) d t j ∧ j ≤ (budget en cs).time.eval n ∧ t.bank.Fits B ∧
      peek w t=result (peek w d) cs ∧ t.bank.out=d.bank.out ∧ t.epoch=d.epoch := by
  classical
  let v := fun i => if i ∈ reads cs then peek w d i else 0
  have data : EFacts n v en := by
    intro i;by_cases mem : i ∈ reads cs
    · simpa [v,mem] using inputs i mem
    · simp [v,mem,Limit.Holds]
  obtain ⟨s,t⟩ := budget_sound en cs v n data ok
  obtain ⟨eqw,eqt⟩ := cost_agree cs (peek w d) v (by intro i mem;simp [v,mem])
  obtain ⟨p,j,ex,cost,f,vals,out,ep⟩ := run (Q:=Q) (τ:=τ) w cs _ d rfl fit hb (eqw ▸ s.trans room)
  exact ⟨p,j,ex,(cost.trans_eq eqt).trans t,f,vals,out,ep⟩

def writes (cs : List Line) := (cs.map (fun a => a.dst.index)).toFinset
theorem untouched (cs : List Line) (v : Values) (i : ℕ) (free : i ∉ writes cs) :
    result v cs i=v i := by
  induction cs generalizing v with
  | nil => rfl
  | cons a as ih =>
    have ne : i≠a.dst.index := by intro e;apply free;simp [writes,e]
    have rest : i ∉ writes as := by intro h;apply free;simpa [writes,ne] using h
    rw [result,ih _ rest];simp [Line.put,ne]

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram.RegisterCode

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured RegisterCode OuterMachine
noncomputable section

def coreRegs : Finset ℕ := {Reg.zero.index,Reg.one.index,Reg.two.index,Reg.n.index,Reg.nSq.index,Reg.seedWidth.index,Reg.radix.index,Reg.span.index,Reg.parityStart.index,Reg.half.index,Reg.repeats.index,Reg.trials.index}
theorem Parameters.transport {w : Layout} {s t : Data} {A k n : ℕ} (p : Parameters w s A k n)
    (keep : ∀ r : Reg, r.index ∈ coreRegs → t.bank.mem (w.reg r)=s.bank.mem (w.reg r)) :
    Parameters w t A k n :=
  ⟨(keep .zero (by decide)).trans p.zero,
    (keep .one (by decide)).trans p.one,
    (keep .two (by decide)).trans p.two,
    (keep .n (by decide)).trans p.dim,
    (keep .nSq (by decide)).trans p.nSq,
    (keep .seedWidth (by decide)).trans p.seed,
    (keep .radix (by decide)).trans p.radix,
    (keep .span (by decide)).trans p.span,
    (keep .parityStart (by decide)).trans p.parityStart,
    (keep .half (by decide)).trans p.half,
    (keep .repeats (by decide)).trans p.repeats,
    (keep .trials (by decide)).trans p.trials⟩

def Parameters.withGraph {w : Layout} {s : Data} {A k n g : ℕ} (p : Parameters w s A k n)
    (graph : s.bank.mem (w.reg .candidate)=g) : TrialConfig w s A k n g :=
  ⟨p.dim,graph,p.zero,p.one,p.seed,p.radix,p.span,p.parityStart,p.half,p.repeats⟩

def edgePrepare : List Line := [⟨.tmp,.arith .div .graph .mask⟩,⟨.tmp,.arith .mod .tmp .two⟩,
  ⟨.tmp,.arith .mul .tmp .mask⟩,⟨.candidate,.sub .graph .tmp⟩,⟨.accepted,.const 0⟩,⟨.seedStart,.const 0⟩]
def edgeFinish : List Line := [⟨.tmp,.sub .graph .candidate⟩,⟨.tmp,.arith .mul .tmp .accepted⟩,
  ⟨.graph,.sub .graph .tmp⟩,⟨.mask,.add .mask .mask⟩]
def processEdge (w : Layout) (prepare : Cmd) : Code := .seq (code w edgePrepare)
  (.seq (indexLoop w .trial .trials (trialBody w prepare)) (code w edgeFinish))

def digitLimit (_ : ℕ) : Limit := ⟨8*Polynomial.X^2+8,none⟩
def edgeSpace := (budget digitLimit edgePrepare).space+(budget digitLimit edgeFinish).space
def edgeTime := (budget digitLimit edgePrepare).time+(budget digitLimit edgeFinish).time

theorem digit_word {n x : ℕ} (h : x.size ≤ n*n+3) (i : ℕ) : (digitLimit i).Holds (n+1) x := by
  simp [digitLimit,Limit.Holds];nlinarith only [h,Nat.zero_le n]

private theorem subtract_digit (g i : ℕ) : g-g / 2^i % 2 * 2^i=GraphWords.erase g i := by
  unfold GraphWords.erase
  have digit := Nat.mod_lt (g/2^i) (by decide : 0 < 2)
  split <;> rename_i eq
  · simp [eq]
  · have one : g/2^i%2=1 := by omega
    simp [one]
theorem erase_le (g i : ℕ) : GraphWords.erase g i ≤ g := by
  unfold GraphWords.erase;split <;> first | exact Nat.sub_le .. | rfl

private theorem frameBlock {w : Layout} {s t : Data} {cs : List Line} (h : peek w t=result (peek w s) cs)
    (r : Reg) (clear : r.index ∉ writes cs) : t.bank.mem (w.reg r)=s.bank.mem (w.reg r) :=
  (congrFun h r.index).trans (untouched cs _ r.index clear)

structure EdgeState (w : Layout) (s : Data) (A k n i g : ℕ) : Prop where
  params : Parameters w s A k n
  word : s.bank.mem (w.reg .graph)=g
  mask : s.bank.mem (w.reg .mask)=2^i

noncomputable def pruneWord (Q : Program) (A k n : ℕ) (coins : List Bool) (g i : ℕ) :=
  let rem := GraphWords.erase g i
  if twoSided Q (GraphWords.graph n rem) (panelFromTape n (coinSpan A k n) coins) then rem else g

theorem pruneWord_le (Q : Program) (A k n : ℕ) (coins : List Bool) (g i : ℕ) : pruneWord Q A k n coins g i ≤ g := by
  unfold pruneWord;dsimp only;split <;> first | exact erase_le .. | rfl

set_option maxHeartbeats 1000000 in
theorem process_edge (w : Layout) (prepare : Cmd) (P J : Poly) (enc : Encoder w prepare P J)
    (Q : Program) (A k : ℕ) (qt : QueryTime Q A k) {n g B i : ℕ} (τ : Tapes) (d : Data)
    (fit : d.bank.Fits B) (st : EdgeState w d A k n i g) (gi : g < 2^(n*n)) (idx : i < n*n)
    (ep : (d.epoch+trials n*(2*majorityHalf n)).size ≤ B) (sp : TrialSpace P B A k n)
    (room : edgeSpace.eval (n+1) ≤ B) :
    ∃ t j, Eval Q τ B (processEdge w prepare) d t j ∧
      j ≤ edgeTime.eval (n+1)+2+trials n*(trialFee J B n (coinSpan A k n)+3) ∧
      t.bank.Fits B ∧ EdgeState w t A k n (i+1) (pruneWord Q A k n τ.coins g i) ∧
      t.epoch ≤ d.epoch+trials n*(2*majorityHalf n) ∧ t.bank.out=d.bank.out ∧
      t.bank.mem (w.reg .edge)=d.bank.mem (w.reg .edge) := by
  let g' := GraphWords.erase g i
  have gg : g' ≤ g := erase_le .. 
  have short := Nat.size_le.mpr gi
  have hb : 2 ≤ B := by have := sp.port;omega
  have gw := digit_word (n:=n) (by omega : g.size ≤ n*n+3)
  have mw := digit_word (n:=n) (by rw [Nat.size_pow];omega : (2^i).size ≤ n*n+3)
  have tw := digit_word (n:=n) (by change 2 ≤ n*n+3;omega : (2:ℕ).size ≤ n*n+3)
  have before : ∀ j ∈ reads edgePrepare,(digitLimit j).Holds (n+1) (peek w d j) := by
    rw [show reads edgePrepare={Reg.graph.index,Reg.mask.index,Reg.two.index} by decide]
    simp only [Finset.mem_insert,Finset.mem_singleton];rintro j (rfl|rfl|rfl)
    · change (digitLimit _).Holds (n+1) (d.bank.mem (w.reg .graph));rw [st.word];exact gw _
    · change (digitLimit _).Holds (n+1) (d.bank.mem (w.reg .mask));rw [st.mask];exact mw _
    · change (digitLimit _).Holds (n+1) (d.bank.mem (w.reg .two));rw [st.params.two];exact tw _
  unfold edgeSpace at room;rw [Polynomial.eval_add] at room
  obtain ⟨a,p1,ex1,fee1,af,am,ao,ae⟩ := analyzed_run (Q:=Q) (τ:=τ) w edgePrepare digitLimit (n+1) d fit hb
    (by rfl) before (by omega)
  have preserves (r : Reg) (h : r.index ∉ writes edgePrepare) := frameBlock am r h
  have pa := st.params.transport (fun r mem => preserves r (by
    have disj : Disjoint coreRegs (writes edgePrepare) := by decide
    exact Finset.disjoint_left.mp disj mem))
  have newGraph : a.bank.mem (w.reg .candidate)=g' := by
    apply (congrFun am Reg.candidate.index).trans
    change d.bank.mem (w.reg .graph)-d.bank.mem (w.reg .graph)/d.bank.mem (w.reg .mask)%d.bank.mem (w.reg .two)*d.bank.mem (w.reg .mask)=_
    rw [st.word,st.mask,st.params.two];exact subtract_digit .. 
  let adj := GraphWords.graph n g'
  have small : g' < 2^(n+n*n+seedWidth n+1) := (gg.trans_lt gi).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have ae' : (a.epoch+trials n*(2*majorityHalf n)).size ≤ B := ae ▸ ep
  obtain ⟨b,p2,ex2,fee2,bf,ans,clock,bo,bframe⟩ := panel_run w prepare P J enc Q A k qt adj a τ af
    (pa.withGraph newGraph) sp (fun _ _ => rfl) small ae' pa.trials (congrFun am Reg.seedStart.index) (congrFun am Reg.accepted.index)
  have savedB (r : Reg) (h : w.reg r ∉ trialLoopWrites w) := bframe r h
  have fixedB : ∀ r : Reg, r.index ∈ coreRegs → w.reg r ∉ trialLoopWrites w := by
    intro r h
    simp only [trialLoopWrites,transient,scoreWrites,Finset.mem_insert,Finset.mem_singleton,regEq,not_or]
    simp only [coreRegs,Finset.mem_insert,Finset.mem_singleton] at h
    simp [Reg.index] at h ⊢;omega
  have pb := pa.transport (fun r mem => savedB r (fixedB r mem))
  have getOld (r : Reg) (free : w.reg r ∉ trialLoopWrites w) (safe : r.index ∉ writes edgePrepare) :=
    (savedB r free).trans (preserves r safe)
  have graphB := (getOld .graph (by simp [trialLoopWrites,transient,scoreWrites,regEq,Reg.index]) (by decide)).trans st.word
  have maskB := (getOld .mask (by simp [trialLoopWrites,transient,scoreWrites,regEq,Reg.index]) (by decide)).trans st.mask
  have candB := (savedB .candidate (by simp [trialLoopWrites,transient,scoreWrites,regEq,Reg.index])).trans newGraph
  let yes := twoSided Q adj (panelFromTape n (coinSpan A k n) τ.coins)
  change b.bank.mem (w.reg .accepted)=yes.toNat at ans
  have after : ∀ j ∈ reads edgeFinish,(digitLimit j).Holds (n+1) (peek w b j) := by
    rw [show reads edgeFinish={Reg.graph.index,Reg.candidate.index,Reg.accepted.index,Reg.mask.index} by decide]
    simp only [Finset.mem_insert,Finset.mem_singleton];rintro j (rfl|rfl|rfl|rfl)
    · change (digitLimit _).Holds (n+1) (b.bank.mem (w.reg .graph));rw [graphB];exact gw _
    · change (digitLimit _).Holds (n+1) (b.bank.mem (w.reg .candidate));rw [candB];exact digit_word (by have := Nat.size_le_size gg;omega) _
    · change (digitLimit _).Holds (n+1) (b.bank.mem (w.reg .accepted));rw [ans];exact digit_word (by cases yes <;> simp <;> omega) _
    · change (digitLimit _).Holds (n+1) (b.bank.mem (w.reg .mask));rw [maskB];exact mw _
  obtain ⟨t,p3,ex3,fee3,tf,tm,ot,et⟩ := analyzed_run (Q:=Q) (τ:=τ) w edgeFinish digitLimit (n+1) b bf hb
    (by rfl) after (by omega)
  have finalP := pb.transport (fun r mem => frameBlock tm r (by
    have disj : Disjoint coreRegs (writes edgeFinish) := by decide
    exact Finset.disjoint_left.mp disj mem))
  refine ⟨t,_,ex1.seq (ex2.seq ex3),?_,tf,⟨finalP,?_,?_⟩,?_,ot.trans (bo.trans ao),?_⟩
  · unfold edgeTime;rw [Polynomial.eval_add];omega
  · apply (congrFun tm Reg.graph.index).trans
    change b.bank.mem (w.reg .graph)-(b.bank.mem (w.reg .graph)-b.bank.mem (w.reg .candidate))*b.bank.mem (w.reg .accepted)=_
    rw [graphB,candB,ans]
    change g-(g-g')*yes.toNat=if yes then g' else g
    cases yes <;> simp <;> omega
  · apply (congrFun tm Reg.mask.index).trans
    change b.bank.mem (w.reg .mask)+b.bank.mem (w.reg .mask)=_
    rw [maskB,pow_succ];omega
  · rw [et,←ae];exact clock
  · exact (frameBlock tm .edge (by decide)).trans (getOld .edge (by simp [trialLoopWrites,transient,scoreWrites,regEq,Reg.index]) (by decide))

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured OuterMachine RegisterCode

noncomputable def prefixWord (Q : Program) (A k n : ℕ) (c : List Bool) (g : ℕ) : ℕ → ℕ
  | 0 => g
  | i+1 => pruneWord Q A k n c (prefixWord Q A k n c g i) i

theorem prefix_le (Q : Program) (A k n : ℕ) (c : List Bool) (g i : ℕ) : prefixWord Q A k n c g i ≤ g := by
  induction i with
  | zero => rfl
  | succ i ih => exact (pruneWord_le ..).trans ih

theorem range_vals (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2;simp

theorem prefix_graph (Q : Program) (A k n : ℕ) (coins : List Bool) (g : ℕ) :
    edges (GraphWords.graph n (prefixWord Q A k n coins g (n*n))) =
      remaining Q (GraphWords.graph n g) (panelFromTape n (coinSpan A k n) coins) := by
  let z := panelFromTape n (coinSpan A k n) coins
  let step := pruneWord Q A k n coins
  have fold (i : ℕ) : prefixWord Q A k n coins g i=(List.range i).foldl step g := by
    induction i with
    | zero => rfl
    | succ i ih => simp [prefixWord,ih,List.range_succ,List.foldl_append,step]
  have list (ls : List (Fin (n*n))) (x : ℕ) :
      edges (GraphWords.graph n ((ls.map Fin.val).foldl step x)) =
      prune (fun _ G => twoSided Q (adjacency G) z) (edges (GraphWords.graph n x))
        (ls.map fun i => finProdFinEquiv.symm i) := by
    induction ls generalizing x with
    | nil => rfl
    | cons i is ih =>
      let p : Fin n × Fin n := finProdFinEquiv.symm i
      have ix : GraphWords.index p.1 p.2=i.val := by
        rw [GraphWords.index_eq];change (finProdFinEquiv (finProdFinEquiv.symm i)).val=_;exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
      have erased : GraphWords.graph n (GraphWords.erase x i.val)=adjacency ((edges (GraphWords.graph n x)).erase p) := by
        rw [←ix];exact GraphWords.erase_graph x p
      simp only [List.map_cons,List.foldl_cons,prune]
      rw [ih]
      apply congrArg (fun y => prune (fun _ G => twoSided Q (adjacency G) z) y (is.map fun i => finProdFinEquiv.symm i))
      change edges (GraphWords.graph n (if twoSided Q (GraphWords.graph n (GraphWords.erase x i.val)) z then _ else x))=_
      rw [erased]
      cases h : twoSided Q (adjacency ((edges (GraphWords.graph n x)).erase p)) z <;>
        simp [p] at h ⊢ <;> simp [h,erased,GraphWords.edges_adjacency,p] at *
  rw [fold,←range_vals,remaining,GraphWords.row_order];exact list _ _

structure EdgePrefix (w : Layout) (Q : Program) (A k n g : ℕ) (c : List Bool) (d s : Data) (i : ℕ) : Prop where
  current : EdgeState w s A k n i (prefixWord Q A k n c g i)
  epoch : s.epoch ≤ d.epoch+i*(trials n*(2*majorityHalf n))
  output : s.bank.out=d.bank.out

theorem prune_run (w : Layout) (prepare : Cmd) (P J : Poly) (enc : Encoder w prepare P J)
    (Q : Program) (A k : ℕ) (qt : QueryTime Q A k) {n g B : ℕ} (τ : Tapes) (d : Data)
    (fit : d.bank.Fits B) (base : EdgeState w d A k n 0 g) (gi : g < 2^(n*n))
    (ep : (d.epoch+n*n*(trials n*(2*majorityHalf n))).size ≤ B) (sp : TrialSpace P B A k n)
    (room : edgeSpace.eval (n+1) ≤ B) :
    ∃ t j, Eval Q τ B (indexLoop w .edge .nSq (processEdge w prepare)) d t j ∧
      j ≤ 2+n*n*(edgeTime.eval (n+1)+2+trials n*(trialFee J B n (coinSpan A k n)+3)+3) ∧
      t.bank.Fits B ∧ t.bank.mem (w.reg .graph)=prefixWord Q A k n τ.coins g (n*n) ∧
      Parameters w t A k n ∧ t.bank.out=d.bank.out := by
  let I := fun i s => EdgePrefix w Q A k n g τ.coins d s i
  have start : I 0 d := ⟨base,by simp,rfl⟩
  have fields (i : ℕ) (s : Data) (h : I i s) := And.intro h.current.params.nSq h.current.params.one
  have stable (i : ℕ) (s : Data) (v : ℕ) (h : I i s) : I i {s with bank := s.bank.write (w.reg .edge) v} := by
    refine ⟨⟨h.current.params.transport ?_,?_,?_⟩,h.epoch,h.output⟩
    · intro r mem
      have ne : r.index≠Reg.edge.index := by intro e;rw [e] at mem;exact (by decide : Reg.edge.index ∉ coreRegs) mem
      simp [Store.write,regEq,ne]
    · simpa [Store.write,regEq,Reg.index] using h.current.word
    · simpa [Store.write,regEq,Reg.index] using h.current.mask
  have next (i : ℕ) (lt : i < n*n) (s : Data) (good : s.bank.Fits B) (inv : I i s)
      (ptr : s.bank.mem (w.reg .edge)=i) : ∃ t j, Eval Q τ B (processEdge w prepare) s t j ∧
      j ≤ edgeTime.eval (n+1)+2+trials n*(trialFee J B n (coinSpan A k n)+3) ∧ t.bank.Fits B ∧
      I (i+1) t ∧ t.bank.mem (w.reg .edge)=i := by
    let u := trials n*(2*majorityHalf n)
    have lim := Nat.mul_le_mul_right u lt;rw [Nat.succ_mul] at lim
    have clock := inv.epoch
    have cap : (s.epoch+u).size ≤ B := by
      change s.epoch ≤ d.epoch+i*u at clock
      apply Nat.le_trans (Nat.size_le_size (show s.epoch+u ≤ d.epoch+n*n*u by omega)) ep
    obtain ⟨t,j,ex,cost,tf,p,c,out,pr⟩ := process_edge w prepare P J enc Q A k qt τ s good inv.current
      ((prefix_le ..).trans_lt gi) lt cap sp room
    exact ⟨t,j,ex,cost,tf,⟨p,by rw [Nat.succ_mul];omega,out.trans inv.output⟩,pr.trans ptr⟩
  obtain ⟨t,j,ex,cost,tf,h⟩ := index_run w .edge .nSq (processEdge w prepare) I d fit start fields stable next
  exact ⟨t,j,ex,cost,tf,h.current.word,h.current.params,h.output⟩

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open GraphWords

def firstCol (word row i : ℕ) := (List.range i).find? fun k => word.testBit (row+k)
theorem first_zero (word row : ℕ) : firstCol word row 0=none := rfl
theorem first_next (word row i : ℕ) :
    firstCol word row (i+1)=(firstCol word row i).or (if word.testBit (row+i) then some i else none) := by
  simp [firstCol,List.range_succ,List.find?_append]
theorem first_lt {word row i v : ℕ} (h : firstCol word row i=some v) : v < i :=
  List.mem_range.mp (List.mem_of_find?_eq_some h)

private theorem select_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    (l.map f).find? p=(l.find? (fun a => p (f a))).map f := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.find?_cons];split <;> simp [ih]

theorem full_row (n word : ℕ) (u : Fin n) :
    let R := edges (graph n word)
    let v := nextVertex R u
    let col := firstCol word (n*u.val) n
    col.getD u.val=v.val ∧ col.isSome=decide ((u,v)∈R) := by
  intro R v col
  let pred := fun b : Fin n => decide ((u,b) ∈ R)
  let o := (List.finRange n).find? pred
  have predicate (j : Fin n) : word.testBit (n*u.val+j.val)=pred j := by
    change _=adjacency (edges (graph n word)) u j
    rw [adjacency_edges];simp [graph,index,Nat.add_comm]
  have eq : col=o.map Fin.val := by
    change (List.range n).find? (fun k => word.testBit (n*u.val+k))=_
    rw [←range_vals,select_map]
    apply congrArg (Option.map Fin.val)
    congr 1;funext j;exact predicate j
  change col.getD u.val=(o.getD u).val ∧ col.isSome=pred (o.getD u)
  rw [eq]
  cases res : o with
  | some a =>
    have satis : pred a=true := List.find?_some res
    simp [satis]
  | none =>
    have off : pred u=false := by
      have all := List.find?_eq_none.mp res
      simpa using all u (by simp)
    simp [off]

theorem seen_le (n word : ℕ) (u : Fin n) (j : ℕ) :
    (tour (edges (graph n word)) u j).seen ≤ j*2^n := by
  induction j with
  | zero => simp [tour]
  | succ j ih =>
    let t := tour (edges (graph n word)) u j
    have e : tour (edges (graph n word)) u (j+1)=advance (edges (graph n word)) t := Function.iterate_succ_apply' ..
    rw [e,Nat.succ_mul]
    change (if t.seen.testBit t.vertex.val then t.seen else t.seen+2^t.vertex.val) ≤ _
    have lim := Nat.pow_le_pow_right (by decide : 0 < 2) t.vertex.isLt.le
    change t.seen ≤ j*2^n at ih
    split
    · exact ih.trans (Nat.le_add_right ..)
    · exact Nat.add_le_add ih lim

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured OuterMachine RegisterCode
noncomputable section

def rowNumeric : Finset ℕ := {Reg.row.index,Reg.col.index,Reg.cur.index,Reg.n.index,Reg.one.index,Reg.two.index,
  Reg.zero.index,Reg.found.index,Reg.next.index,Reg.valid.index}
def walkLimit (i : ℕ) : Limit := ⟨8*Polynomial.X^2+8,if i ∈ rowNumeric then some (8*Polynomial.X^2+8) else none⟩
def scanLines : List Line := [⟨.tmp,.add .row .col⟩,
  ⟨.tmp,.arith .pow .two .tmp⟩,
  ⟨.tmp,.arith .div .graph .tmp⟩,
  ⟨.tmp,.arith .mod .tmp .two⟩,
  ⟨.tmp2,.sub .one .found⟩,
  ⟨.tmp,.arith .mul .tmp .tmp2⟩,
  ⟨.found,.add .found .tmp⟩,
  ⟨.tmp2,.sub .one .tmp⟩,
  ⟨.next,.arith .mul .next .tmp2⟩,
  ⟨.tmp2,.arith .mul .col .tmp⟩,
  ⟨.next,.add .next .tmp2⟩]
def walkStart : List Line := [⟨.tmp,.arith .pow .two .cur⟩,
  ⟨.tmp2,.arith .div .seen .tmp⟩,
  ⟨.tmp2,.arith .mod .tmp2 .two⟩,
  ⟨.tmp2,.sub .one .tmp2⟩,
  ⟨.tmp,.arith .mul .tmp .tmp2⟩,
  ⟨.seen,.add .seen .tmp⟩,
  ⟨.valid,.arith .mul .valid .tmp2⟩,
  ⟨.next,.add .cur .zero⟩,
  ⟨.found,.const 0⟩,
  ⟨.row,.arith .mul .n .cur⟩]
def walkEnd : List Line := [⟨.valid,.arith .mul .valid .found⟩,
  ⟨.cur,.add .next .zero⟩]
def walkSpace := (budget walkLimit scanLines).space+(budget walkLimit walkStart).space+(budget walkLimit walkEnd).space
def scanTime := (budget walkLimit scanLines).time

theorem small_arg (r n x : ℕ) (h : x ≤ 8*(n+1)^2+8) : (walkLimit r).Holds (n+1) x := by
  constructor
  · simpa [walkLimit] using (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=x))).trans h
  · intro p eq;change (if _ then some _ else none)=some p at eq;split at eq
    · cases eq;simpa using h
    · contradiction

theorem word_arg (r n x : ℕ) (large : r ∉ rowNumeric) (h : x.size ≤ 8*(n+1)^2+8) :
    (walkLimit r).Holds (n+1) x := by simp [walkLimit,Limit.Holds,large,h]

structure RowInput (w : Layout) (d : Data) (n g u : ℕ) : Prop where
  graph : d.bank.mem (w.reg .graph)=g
  dim : d.bank.mem (w.reg .n)=n
  row : d.bank.mem (w.reg .row)=n*u
  one : d.bank.mem (w.reg .one)=1
  two : d.bank.mem (w.reg .two)=2

def rowWrites := insert Reg.col.index (writes scanLines)
structure RowPrefix (w : Layout) (d s : Data) (n g u i : ℕ) : Prop where
  found : s.bank.mem (w.reg .found)=(firstCol g (n*u) i).isSome.toNat
  next : s.bank.mem (w.reg .next)=(firstCol g (n*u) i).getD u
  epoch : s.epoch=d.epoch
  output : s.bank.out=d.bank.out
  saved : ∀ r : Reg,r.index ∉ rowWrites → s.bank.mem (w.reg r)=d.bank.mem (w.reg r)

set_option maxHeartbeats 850000 in
theorem scan_run (w : Layout) (Q : Program) (τ : Tapes) (B n g u : ℕ) (d : Data) (fit : d.bank.Fits B)
    (hb : 2 ≤ B) (room : walkSpace.eval (n+1) ≤ B) (input : RowInput w d n g u)
    (gu : g < 2^(n*n)) (hu : u < n) (clear : d.bank.mem (w.reg .found)=0) (init : d.bank.mem (w.reg .next)=u) :
    ∃ t j, Eval Q τ B (indexLoop w .col .n (code w scanLines)) d t j ∧
      j ≤ 2+n*(scanTime.eval (n+1)+3) ∧ t.bank.Fits B ∧ RowPrefix w d t n g u n := by
  let I := fun i s => RowPrefix w d s n g u i
  have base : I 0 d := ⟨clear,init,rfl,rfl,fun _ _ => rfl⟩
  have fields (i s) (inv : I i s) := And.intro ((inv.saved .n (by decide)).trans input.dim) ((inv.saved .one (by decide)).trans input.one)
  have stable (i s v) (h : I i s) : I i {s with bank := s.bank.write (w.reg .col) v} := by
    refine ⟨?_,?_,h.epoch,h.output,?_⟩
    · simpa [Store.write,regEq,Reg.index] using h.found
    · simpa [Store.write,regEq,Reg.index] using h.next
    · intro r free
      have ne : r.index≠Reg.col.index := fun e => free (Finset.mem_insert.mpr (Or.inl e))
      simpa [Store.write,regEq,ne] using h.saved r free
  have step (i : ℕ) (lt : i < n) (s : Data) (fits : s.bank.Fits B) (h : I i s) (ptr : s.bank.mem (w.reg .col)=i) :
      ∃ t j, Eval Q τ B (code w scanLines) s t j ∧ j ≤ scanTime.eval (n+1) ∧ t.bank.Fits B ∧
        I (i+1) t ∧ t.bank.mem (w.reg .col)=i := by
    let v := firstCol g (n*u) i
    let bit := g.testBit (n*u+i)
    have found : s.bank.mem (w.reg .found)=v.isSome.toNat := h.found
    have nx : s.bank.mem (w.reg .next)=v.getD u := h.next
    have row := (h.saved .row (by decide)).trans input.row
    have one := (h.saved .one (by decide)).trans input.one
    have two := (h.saved .two (by decide)).trans input.two
    have graph := (h.saved .graph (by decide)).trans input.graph
    have bound : v.getD u < n := by
      cases ev : v with
      | none => simpa using hu
      | some a => exact (first_lt ev).trans lt
    have unit : v.isSome.toNat ≤ 1 := by cases v <;> simp
    have square : n*u ≤ n*n := Nat.mul_le_mul_left _ hu.le
    have nw : n*n+n+3 ≤ 8*(n+1)^2+8 := by nlinarith
    have req : ∀ a ∈ reads scanLines,(walkLimit a).Holds (n+1) (peek w s a) := by
      rw [show reads scanLines={Reg.row.index,Reg.col.index,Reg.two.index,Reg.graph.index,
        Reg.one.index,Reg.found.index,Reg.next.index} by decide]
      simp only [Finset.mem_insert,Finset.mem_singleton];rintro a (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .row));rw [row];apply small_arg;omega
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .col));rw [ptr];apply small_arg;omega
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .two));rw [two];apply small_arg;omega
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .graph));rw [graph];apply word_arg _ _ _ (by decide);have := Nat.size_le.mpr gu;omega
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .one));rw [one];apply small_arg;omega
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .found));rw [found];apply small_arg;omega
      · change (walkLimit _).Holds _ (s.bank.mem (w.reg .next));rw [nx];apply small_arg;omega
    have cap : (budget walkLimit scanLines).space.eval (n+1) ≤ B := by unfold walkSpace at room;simp only [Polynomial.eval_add] at room;omega
    obtain ⟨t,j,ex,cost,tf,vals,out,ep⟩ := analyzed_run (Q:=Q) (τ:=τ) w scanLines walkLimit (n+1) s fits hb (by rfl) req cap
    let takeBit := g/2^(n*u+i)%2*(1-v.isSome.toNat)
    have flags : t.bank.mem (w.reg .found)=v.isSome.toNat+takeBit := by
      apply (congrFun vals Reg.found.index).trans
      change s.bank.mem (w.reg .found)+(s.bank.mem (w.reg .graph)/(s.bank.mem (w.reg .two)^(s.bank.mem (w.reg .row)+s.bank.mem (w.reg .col)))%s.bank.mem (w.reg .two))*(s.bank.mem (w.reg .one)-s.bank.mem (w.reg .found))=_
      rw [found,graph,two,row,ptr,one]
    have nextVal : t.bank.mem (w.reg .next)=v.getD u*(1-takeBit)+i*takeBit := by
      apply (congrFun vals Reg.next.index).trans
      let take' := s.bank.mem (w.reg .graph)/(s.bank.mem (w.reg .two)^(s.bank.mem (w.reg .row)+s.bank.mem (w.reg .col)))%s.bank.mem (w.reg .two)*(s.bank.mem (w.reg .one)-s.bank.mem (w.reg .found))
      change s.bank.mem (w.reg .next)*(s.bank.mem (w.reg .one)-take')+s.bank.mem (w.reg .col)*take'=_
      dsimp only [take'];rw [nx,graph,two,row,ptr,one,found]
    have law : firstCol g (n*u) (i+1)=v.or (if bit then some i else none) := first_next ..
    have digit : takeBit=bit.toNat*(1-v.isSome.toNat) := by rw [show bit.toNat=g/2^(n*u+i)%2 from Nat.toNat_testBit ..]
    have frame (r : Reg) (no : r.index ∉ writes scanLines) := (congrFun vals r.index).trans (untouched scanLines _ r.index no)
    refine ⟨t,j,ex,cost,tf,⟨?_,?_,ep.trans h.epoch,out.trans h.output,?_⟩,(frame .col (by decide)).trans ptr⟩
    · rw [flags,law,digit];cases v <;> cases bit <;> rfl
    · rw [nextVal,law,digit];cases v <;> cases bit <;> simp
    · intro r no;exact (frame r (fun m => no (Finset.mem_insert_of_mem m))).trans (h.saved r no)
  exact index_run w .col .n (code w scanLines) I d fit base fields stable step

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured RegisterCode OuterMachine GraphWords
noncomputable section

def tourKeys : Finset ℕ := {Reg.graph.index,Reg.n.index,Reg.zero.index,Reg.one.index,Reg.two.index,Reg.walk.index}
structure TourInput (w : Layout) (d : Data) (n g : ℕ) : Prop where
  graph : d.bank.mem (w.reg .graph)=g
  dim : d.bank.mem (w.reg .n)=n
  zero : d.bank.mem (w.reg .zero)=0
  one : d.bank.mem (w.reg .one)=1
  two : d.bank.mem (w.reg .two)=2
structure OrbitRegs {n : ℕ} (w : Layout) (d : Data) (p : Walk n) : Prop where
  cur : d.bank.mem (w.reg .cur)=p.vertex.val
  seen : d.bank.mem (w.reg .seen)=p.seen
  valid : d.bank.mem (w.reg .valid)=p.valid.toNat
def tourStep (w : Layout) := (code w walkStart).seq ((indexLoop w .col .n (code w scanLines)).seq (code w walkEnd))
def tourStepCost (n : ℕ) := (budget walkLimit walkStart).time.eval (n+1)+(2+n*(scanTime.eval (n+1)+3))+
  (budget walkLimit walkEnd).time.eval (n+1)

theorem bool_bound (a : Bool) : a.toNat ≤ 1 := by cases a <;> decide

set_option maxHeartbeats 850000 in
theorem tour_step (w : Layout) (Q : Program) (τ : Tapes) (B n g : ℕ) (p : Walk n) (d : Data)
    (fit : d.bank.Fits B) (hb : 2 ≤ B) (room : walkSpace.eval (n+1) ≤ B) (inp : TourInput w d n g)
    (run : OrbitRegs w d p) (gu : g < 2^(n*n)) (seenBound : p.seen ≤ n*2^n) :
    ∃ t j, Eval Q τ B (tourStep w) d t j ∧ j ≤ tourStepCost n ∧ t.bank.Fits B ∧
      OrbitRegs w t (advance (edges (graph n g)) p) ∧ t.bank.out=d.bank.out ∧ t.epoch=d.epoch ∧
      ∀ r : Reg, r.index ∈ tourKeys → t.bank.mem (w.reg r)=d.bank.mem (w.reg r) := by
  let u := p.vertex
  let bit := p.seen.testBit u.val
  let newSeen := if bit then p.seen else p.seen+2^u.val
  let R := edges (graph n g)
  let v := nextVertex R u
  let ok := p.valid && !bit
  have nu := u.isLt
  have vs := bool_bound p.valid
  have short := Nat.size_le_size seenBound
  have prod := ControlBounds.prod_width n (2^n)
  rw [Nat.size_pow] at prod
  have ns : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have bound : n*n+2*n+5 ≤ 8*(n+1)^2+8 := by nlinarith
  have cap := room;unfold walkSpace at cap;simp only [Polynomial.eval_add] at cap
  have inputs : ∀ i ∈ reads walkStart,(walkLimit i).Holds (n+1) (peek w d i) := by
    rw [show reads walkStart={Reg.two.index,Reg.cur.index,Reg.seen.index,Reg.one.index,Reg.valid.index,Reg.zero.index,Reg.n.index} by decide]
    simp only [Finset.mem_insert,Finset.mem_singleton];rintro i (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .two));rw [inp.two];apply small_arg;omega
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .cur));rw [run.cur];apply small_arg;change u.val ≤ _;omega
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .seen));rw [run.seen];apply word_arg _ _ _ (by decide);omega
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .one));rw [inp.one];apply small_arg;omega
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .valid));rw [run.valid];apply small_arg;omega
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .zero));rw [inp.zero];apply small_arg;omega
    · change (walkLimit _).Holds _ (d.bank.mem (w.reg .n));rw [inp.dim];apply small_arg;omega
  obtain ⟨a,j,ex,cost,af,am,ao,ae⟩ := analyzed_run (Q:=Q) (τ:=τ) w walkStart walkLimit (n+1) d fit hb (by rfl) inputs (by omega)
  have savedA (r : Reg) (no : r.index ∉ writes walkStart) := (congrFun am r.index).trans (untouched walkStart _ r.index no)
  let pow := d.bank.mem (w.reg .two)^d.bank.mem (w.reg .cur)
  let fresh := d.bank.mem (w.reg .one)-(d.bank.mem (w.reg .seen)/pow%d.bank.mem (w.reg .two))
  have power : pow=2^u.val := by dsimp [pow,u];rw [inp.two,run.cur]
  have digit : p.seen/2^u.val%2=bit.toNat := (Nat.toNat_testBit ..).symm
  have freshVal : fresh=1-bit.toNat := by dsimp [fresh];rw [inp.one,power,run.seen,inp.two,digit]
  have aSeen : a.bank.mem (w.reg .seen)=newSeen := by
    apply (congrFun am Reg.seen.index).trans
    change d.bank.mem (w.reg .seen)+pow*fresh=_
    rw [run.seen,power,freshVal];unfold newSeen;cases bit <;> simp
  have aValid : a.bank.mem (w.reg .valid)=ok.toNat := by
    apply (congrFun am Reg.valid.index).trans
    change d.bank.mem (w.reg .valid)*fresh=_
    rw [run.valid,freshVal];unfold ok;cases p.valid <;> cases bit <;> rfl
  have aNext : a.bank.mem (w.reg .next)=u.val := by
    apply (congrFun am Reg.next.index).trans
    change d.bank.mem (w.reg .cur)+d.bank.mem (w.reg .zero)=_
    rw [run.cur,inp.zero];rfl
  have aRow : a.bank.mem (w.reg .row)=n*u.val := by
    apply (congrFun am Reg.row.index).trans
    change d.bank.mem (w.reg .n)*d.bank.mem (w.reg .cur)=_
    rw [inp.dim,run.cur]
  have rin : RowInput w a n g u.val := ⟨(savedA .graph (by decide)).trans inp.graph,(savedA .n (by decide)).trans inp.dim,
    aRow,(savedA .one (by decide)).trans inp.one,(savedA .two (by decide)).trans inp.two⟩
  obtain ⟨b,k,loop,fee,bf,row⟩ := scan_run w Q τ B n g u.val a af hb room rin gu nu (congrFun am Reg.found.index) aNext
  obtain ⟨first,flag⟩ := full_row n g u
  have bn : b.bank.mem (w.reg .next)=v.val := row.next.trans first
  have bh : b.bank.mem (w.reg .found)=(decide ((u,v)∈R)).toNat := row.found.trans (congrArg Bool.toNat flag)
  have bv := (row.saved .valid (by decide)).trans aValid
  have bz := (row.saved .zero (by decide)).trans ((savedA .zero (by decide)).trans inp.zero)
  have endInputs : ∀ i ∈ reads walkEnd,(walkLimit i).Holds (n+1) (peek w b i) := by
    rw [show reads walkEnd={Reg.valid.index,Reg.found.index,Reg.next.index,Reg.zero.index} by decide]
    simp only [Finset.mem_insert,Finset.mem_singleton];rintro i (rfl|rfl|rfl|rfl)
    · change (walkLimit _).Holds _ (b.bank.mem (w.reg .valid));rw [bv];apply small_arg;have := bool_bound ok;omega
    · change (walkLimit _).Holds _ (b.bank.mem (w.reg .found));rw [bh];apply small_arg;have := bool_bound (decide ((u,v)∈R));omega
    · change (walkLimit _).Holds _ (b.bank.mem (w.reg .next));rw [bn];apply small_arg;have := v.isLt;omega
    · change (walkLimit _).Holds _ (b.bank.mem (w.reg .zero));rw [bz];apply small_arg;omega
  obtain ⟨t,l,fin,time,tf,tm,ot,et⟩ := analyzed_run (Q:=Q) (τ:=τ) w walkEnd walkLimit (n+1) b bf hb (by rfl) endInputs (by omega)
  have savedT (r : Reg) (no : r.index ∉ writes walkEnd) := (congrFun tm r.index).trans (untouched walkEnd _ r.index no)
  refine ⟨t,_,ex.seq (loop.seq fin),by unfold tourStepCost;omega,tf,⟨?_,?_,?_⟩,ot.trans (row.output.trans ao),et.trans (row.epoch.trans ae),?_⟩
  · apply (congrFun tm Reg.cur.index).trans;change b.bank.mem (w.reg .next)+b.bank.mem (w.reg .zero)=v.val;rw [bn,bz,Nat.add_zero]
  · exact (savedT .seen (by decide)).trans ((row.saved .seen (by decide)).trans aSeen)
  · apply (congrFun tm Reg.valid.index).trans
    change b.bank.mem (w.reg .valid)*b.bank.mem (w.reg .found)=(ok && decide ((u,v)∈R)).toNat
    rw [bv,bh];cases ok <;> cases decide ((u,v)∈R) <;> rfl
  · intro r key
    have x : Disjoint tourKeys (writes walkStart) := by decide
    have y : Disjoint tourKeys rowWrites := by decide
    have z : Disjoint tourKeys (writes walkEnd) := by decide
    exact (savedT r (Finset.disjoint_left.mp z key)).trans ((row.saved r (Finset.disjoint_left.mp y key)).trans (savedA r (Finset.disjoint_left.mp x key)))

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured RegisterCode OuterMachine GraphWords
noncomputable section

def clearOrbit : List Line := [⟨.cur,.const 0⟩,⟨.seen,.const 0⟩,⟨.valid,.const 1⟩]
def orbitCode (w : Layout) := (code w clearOrbit).seq ((indexLoop w .walk .n (tourStep w)).seq
  (test w .cur .zero nop (lit w .valid 0)))
def orbitCost (n : ℕ) := 8+n*(tourStepCost n+3)

theorem TourInput.transfer {w : Layout} {s t : Data} {n g : ℕ} (p : TourInput w s n g)
    (h : ∀ r : Reg,r.index ∈ tourKeys → r≠.walk → t.bank.mem (w.reg r)=s.bank.mem (w.reg r)) :
    TourInput w t n g :=
  ⟨(h .graph (by decide) (by decide)).trans p.graph,(h .n (by decide) (by decide)).trans p.dim,
    (h .zero (by decide) (by decide)).trans p.zero,(h .one (by decide) (by decide)).trans p.one,
    (h .two (by decide) (by decide)).trans p.two⟩

theorem orbit_run (w : Layout) (Q : Program) (τ : Tapes) (n g B : ℕ) (pos : 0 < n) (d : Data)
    (fit : d.bank.Fits B) (hb : 2 ≤ B) (room : walkSpace.eval (n+1) ≤ B) (inp : TourInput w d n g)
    (gu : g < 2^(n*n)) :
    ∃ t j, Eval Q τ B (orbitCode w) d t j ∧ j ≤ orbitCost n ∧ t.bank.Fits B ∧
      t.bank.mem (w.reg .valid)=(certify n (edges (graph n g))).toNat ∧ t.bank.out=d.bank.out := by
  cases n with
  | zero => omega
  | succ m =>
    let n := m+1
    let R := edges (graph n g)
    let p := tour R (0 : Fin n)
    have width0 : width (peek w d) clearOrbit=1 := by simp [clearOrbit,width,Expr.width,Expr.val]
    obtain ⟨a,j,init,cost,af,am,ao,_⟩ := run (Q:=Q) (τ:=τ) w clearOrbit _ d rfl fit hb (width0 ▸ (by omega : 1 ≤ B))
    change j ≤ 3 at cost
    have ai : TourInput w a n g := inp.transfer (fun r mem _ => (congrFun am r.index).trans (untouched clearOrbit _ r.index
      (Finset.disjoint_left.mp (by decide : Disjoint tourKeys (writes clearOrbit)) mem)))
    let I := fun i (s : Data) => TourInput w s n g ∧ OrbitRegs w s (p i) ∧ s.bank.out=d.bank.out
    have start : I 0 a := ⟨ai,⟨congrFun am Reg.cur.index,congrFun am Reg.seen.index,congrFun am Reg.valid.index⟩,ao⟩
    have fields (i s) (h : I i s) := And.intro h.1.dim h.1.one
    have stable (i s v) (h : I i s) : I i {s with bank := s.bank.write (w.reg .walk) v} := by
      refine ⟨?_,?_,h.2.2⟩
      · constructor <;> first
          | simpa [Store.write,regEq,Reg.index] using h.1.graph
          | simpa [Store.write,regEq,Reg.index] using h.1.dim
          | simpa [Store.write,regEq,Reg.index] using h.1.zero
          | simpa [Store.write,regEq,Reg.index] using h.1.one
          | simpa [Store.write,regEq,Reg.index] using h.1.two
      · constructor <;> first
          | simpa [Store.write,regEq,Reg.index] using h.2.1.cur
          | simpa [Store.write,regEq,Reg.index] using h.2.1.seen
          | simpa [Store.write,regEq,Reg.index] using h.2.1.valid
    have step (i : ℕ) (lt : i < n) (s : Data) (good : s.bank.Fits B) (h : I i s) (atI : s.bank.mem (w.reg .walk)=i) :
        ∃ t j, Eval Q τ B (tourStep w) s t j ∧ j ≤ tourStepCost n ∧ t.bank.Fits B ∧ I (i+1) t ∧ t.bank.mem (w.reg .walk)=i := by
      have lim := (seen_le n g (0 : Fin n) i).trans (Nat.mul_le_mul_right (2^n) lt.le)
      obtain ⟨t,k,ex,time,tf,tr,ot,_,frame⟩ := tour_step w Q τ B n g (p i) s good hb room h.1 h.2.1 gu lim
      have succ : p (i+1)=advance R (p i) := Function.iterate_succ_apply' ..
      exact ⟨t,k,ex,time,tf,⟨h.1.transfer (fun r key _ => frame r key),succ ▸ tr,ot.trans h.2.2⟩,(frame .walk (by decide)).trans atI⟩
    obtain ⟨s,k,loop,fee,sf,si⟩ := index_run w .walk .n (tourStep w) I a af start fields stable step
    have law : ((p n).valid && decide ((p n).vertex=0))=certify n R := certify_by_word m g
    have si_cur : s.bank.mem (w.reg .cur)=(p n).vertex.val := si.2.1.cur
    by_cases close : (p n).vertex=0
    · have adj : s.bank.mem (w.reg .cur) ≤ s.bank.mem (w.reg .zero) := by rw [si_cur,close,si.1.zero];rfl
      have chk : Eval Q τ B (test w .cur .zero nop (lit w .valid 0)) s s (1+0) := .yes sf adj (.pure sf (.skip _))
      refine ⟨s,_,init.seq (loop.seq chk),by change _ ≤ orbitCost n;unfold orbitCost;omega,sf,?_,si.2.2⟩
      rw [←law];simpa [close] using si.2.1.valid
    · have nonzero : (p n).vertex.val≠0 := fun h => close (Fin.ext h)
      have adj : ¬s.bank.mem (w.reg .cur) ≤ s.bank.mem (w.reg .zero) := by rw [si_cur,si.1.zero];omega
      have wr := setWord Q τ B (w.reg .valid) 0 s sf (Nat.zero_le _)
      have chk := Eval.no (c:=nop) sf adj wr.1
      refine ⟨_,_,init.seq (loop.seq chk),by change _ ≤ orbitCost n;unfold orbitCost;omega,wr.2,?_,si.2.2⟩
      rw [←law];simp [close,Store.write]

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured RegisterCode OuterMachine

structure Header (w : Layout) (s : Data) (n g : ℕ) : Prop where
  dim : s.bank.mem (w.reg .n)=n
  graph : s.bank.mem (w.reg .graph)=g
  zero : s.bank.mem (w.reg .zero)=0
  one : s.bank.mem (w.reg .one)=1
  two : s.bank.mem (w.reg .two)=2

def setup (w : Layout) : Fragment := Structured.sequence [
  .op (.const (w.reg .zero) 0),.op (.const (w.reg .one) 1),.op (.const (w.reg .two) 2),
  .op (.add (w.reg .n) 1 (w.reg .zero)),.op (.add (w.reg .graph) 4 (w.reg .zero))]
def prepCost (n : ℕ) := 10*n.size+4*n+9*(n*n)+17

private theorem extend_exec {τ : Tapes} {c : Cmd} {s t : Store} {j : ℕ} {a b : Store → Prop}
    (ex : Exec τ a c s t j) (sub : ∀ x,a x → b x) : Exec τ b c s t j := by
  induction ex with
  | skip => exact .skip _
  | op _ _ h => exact .op _ _ (sub _ h)
  | seq _ _ h1 h2 => exact h1.seq h2
  | yes h _ rest => exact .yes h rest
  | no h _ rest => exact .no h rest
  | done h => exact .done h
  | again h _ _ h1 h2 => exact .again h h1 h2

def Reader (c : Cmd) := ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (coins : List Bool) (b : ℕ) (s : Store),
  s.mem 0=0 → s.Fits b → 8*(n+1)^2 ≤ b →
  ∃ t k, Exec (runTapes (encodeDigraph n adj) coins) (fun u => u.Fits b) c s t k ∧
    k ≤ 10*n.size+4*n+9*(n*n)+12 ∧ t.mem 1=n ∧
    (∀ u v : Fin n, (t.mem 4).testBit (v.val+n*u.val)=adj u v) ∧ t.out=s.out ∧
    ∀ a ≥ 8, t.mem a=s.mem a

theorem bootstrap (w : Layout) (Q : Program) (c : Cmd) (get : Reader c) (n B : ℕ)
    (adj : Fin n → Fin n → Bool) (coins : List Bool) (room : 8*(n+1)^2+8 ≤ B) :
    ∃ (d : Data) (j g : ℕ), Eval Q (runTapes (encodeDigraph n adj) coins) B
      (.seq (.pure c) (.pure (setup w).cmd)) initial d j ∧ j ≤ prepCost n ∧ d.bank.Fits B ∧
      Header w d n g ∧ GraphWords.graph n g=adj ∧ d.bank.out=[] ∧ d.epoch=0 ∧
      (∀ i, (peek w d i).size ≤ 8*(n+1)^2+8) ∧ g.size ≤ 8*(n+1)^2 := by
  let h := 8*(n+1)^2
  let τ := runTapes (encodeDigraph n adj) coins
  have empty (k : ℕ) : initial.bank.Fits k := fun _ => Nat.zero_le _
  obtain ⟨s,k,parse,cost,dim,graph,out,_⟩ := get n adj coins h initial.bank rfl (empty _) le_rfl
  have small := parse.post (empty h)
  have hB : h ≤ B := by dsimp [h];omega
  have first := extend_exec parse (fun x fits a => (fits a).trans hB)
  have zero : (0:ℕ).size ≤ h := Nat.zero_le _
  have one : (1:ℕ).size ≤ h := by change 1 ≤ 8*(n+1)^2;nlinarith
  have two : (2:ℕ).size ≤ h := by change 2 ≤ 8*(n+1)^2;nlinarith
  let m := ((setup w).run τ s).last
  have far (r : Reg) (i : ℕ) (lo : i < 14) : i≠w.reg r := by have := w.high r;omega
  have wide : ((setup w).run τ s).writeWidth ≤ h := by
    simp (disch := decide) [setup,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,Function.update_apply,
      far,regEq,Reg.index,small 1,small 4,one,two]
    exact one
  have ex : Exec τ (fun st => st.Fits h) (setup w).cmd s m 5 := (setup w).exec τ s h small wide
  have hfit := ex.post small
  let d : Data := {initial with bank := m}
  have head : Header w d n (s.mem 4) := by
    constructor <;> simp (disch := decide) [d,m,setup,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      far,regEq,Reg.index,dim]
  refine ⟨d,_,s.mem 4,(Eval.pure (d:=initial) (empty B) first).seq
    (.pure (fun a => (small a).trans hB) (extend_exec ex (fun u z a => (z a).trans hB))),
    by unfold prepCost;omega,fun a => (hfit a).trans hB,head,funext (fun u => funext (graph u)),out,rfl,?_,small 4⟩
  intro i;exact (hfit _).trans (by dsimp [h];omega)

def shortCode (w : Layout) := test w .n .zero (lit w .valid 0) (arith w .mod .valid .graph .two)
def shortCost (B : ℕ) := B*(5*B+9)+15

theorem short_run (w : Layout) (Q : Program) (τ : Tapes) (n g B : ℕ) (adj : Fin n → Fin n → Bool)
    (d : Data) (h : Header w d n g) (small : n ≤ 1) (graph : GraphWords.graph n g=adj)
    (fit : d.bank.Fits B) (gs : g.size ≤ 8*(n+1)^2) (room : 8*(n+1)^2+8 ≤ B) :
    ∃ t j, Eval Q τ B (shortCode w) d t j ∧ j ≤ shortCost B ∧ t.bank.Fits B ∧
      t.bank.mem (w.reg .valid)=(smallCycleAnswer n adj).toNat ∧ t.bank.out=d.bank.out := by
  by_cases none : n=0
  · subst n
    have wr := setWord Q τ B (w.reg .valid) 0 d fit (Nat.zero_le _)
    exact ⟨_,_,.yes fit (by rw [h.dim,h.zero]) wr.1,by unfold shortCost;omega,wr.2,by simp [Store.write,smallCycleAnswer],rfl⟩
  · have one : n=1 := by omega
    subst n
    have lim : (2*g+2).size ≤ B := by
      have a := ControlBounds.prod_width 2 g;have b := ControlBounds.sum_width (2*g) 2
      change (2*g).size ≤ 2+g.size at a;change (2*g+2).size ≤ (2*g).size+2+1 at b;omega
    have cap : ((Word.Arithmetic.mod).value g 2).size ≤ B :=
      (Nat.size_le_size (Nat.mod_le g 2)).trans (by omega)
    have v1 : d.bank.mem (Word.cell (w.slot .graph))=g := h.graph
    have v2 : d.bank.mem (Word.cell (w.slot .two))=2 := h.two
    obtain ⟨u,k,ex,fee,ret,regs⟩ := Word.Arithmetic.call_exec (τ:=τ) .mod (w.slot .valid) (w.slot .graph) (w.slot .two) d.bank
      fit (by omega) (by rw [v1];exact lim) (by rw [v1,v2];exact cap)
    have neg : ¬ d.bank.mem (w.reg .n) ≤ d.bank.mem (w.reg .zero) := by rw [h.dim,h.zero];omega
    have bit : g.testBit 0=adj 0 0 := congrFun (congrFun graph 0) 0
    have result := regs (w.slot .valid);rw [if_pos rfl,v1,v2] at result
    have scale := Nat.mul_le_mul (show g.size ≤ B by omega) (show 5*g.size+9 ≤ 5*B+9 by omega)
    refine ⟨_,_,.no fit neg (.pure fit ex),?_,ex.post fit,?_,ret⟩
    · rw [v1,v2] at fee;change k ≤ g.size*(5*g.size+9)+7+4 at fee;unfold shortCost;omega
    · change u.mem (w.reg .valid)=(adj 0 0).toNat
      rw [←bit,Nat.toNat_testBit];simpa [Word.Arithmetic.value,Layout.reg] using result

end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured RegisterCode OuterMachine ControlBounds
noncomputable section

structure Room (P : Poly) (A k n B : ℕ) : Prop where
  parser : 8*(n+1)^2+8 ≤ B
  schedule : (scheduleBudget A k).space.eval (n+1) ≤ B
  edge : edgeSpace.eval (n+1) ≤ B
  walk : walkSpace.eval (n+1) ≤ B
  trial : TrialSpace P B A k n
  epoch : (n*n*(trials n*(2*majorityHalf n))).size ≤ B

theorem smallEval (p : Poly) : Small (fun n => p.eval (n+1)) := ⟨p,fun _ => le_rfl⟩
theorem explicitPoly (a e b : ℕ) : Small (fun n => a*(n+1)^e+b) :=
  ⟨Polynomial.C a*Polynomial.X^e+Polynomial.C b,by simp⟩

theorem choose_width (A k : ℕ) (P : Poly) : ∃ W : Poly, ∀ n, Room P A k n (W.eval (n+1)) := by
  have programs := (((explicitPoly 8 2 8).add (smallEval (scheduleBudget A k).space)).add (smallEval edgeSpace)).add (smallEval walkSpace)
  have buffers := ((programs.add (field_small.comp_polynomial P)).add (seed_small.add (small_const 1))).add seed_cursor_width
  have lim := ((buffers.add (tape_cursor_width A k)).add (explicitPoly 120 4 3)).add epoch_width
  obtain ⟨W,h⟩ := lim
  refine ⟨W,fun n => ?_⟩
  have bound := h n
  dsimp only at bound
  change 8*(n+1)^2+8+_+_+_+_+_+_+_+_+(n*n*trials n*(2*majorityHalf n)).size ≤ _ at bound
  constructor
  · omega
  · omega
  · omega
  · omega
  · constructor <;> omega
  · rw [←Nat.mul_assoc (n*n)];omega

def pruningFee (J : Poly) (B A k n : ℕ) :=
  2+n*n*(edgeTime.eval (n+1)+2+trials n*(trialFee J B n (coinSpan A k n)+3)+3)
def totalFee (J : Poly) (B A k n : ℕ) := prepCost n+shortCost B+(scheduleBudget A k).time.eval (n+1)+
  pruningFee J B A k n+orbitCost n+10

def Paid (w f : ℕ → ℕ) := ∃ p : Poly, ∀ n, f n ≤ w n*p.eval (n+1)
theorem Paid.small {f w : ℕ → ℕ} (small : Small f) (pos : ∀ n, 1 ≤ w n) : Paid w f := by
  obtain ⟨p,h⟩ := small;refine ⟨p,fun n => (h n).trans ?_⟩
  simpa using Nat.mul_le_mul_right (p.eval (n+1)) (pos n)
theorem Paid.add {w f g : ℕ → ℕ} (a : Paid w f) (b : Paid w g) : Paid w (fun n => f n+g n) := by
  obtain ⟨p,h⟩ := a;obtain ⟨q,j⟩ := b;refine ⟨p+q,fun n => ?_⟩
  rw [Polynomial.eval_add,Nat.mul_add];exact Nat.add_le_add (h n) (j n)
theorem Paid.times {w f : ℕ → ℕ} (a : Paid w f) (N : ℕ → ℕ) :
    Paid (fun n => (N n+1)*w n) (fun n => N n*f n) := by
  obtain ⟨p,h⟩ := a;refine ⟨p,fun n => ?_⟩
  rw [Nat.mul_assoc];exact Nat.mul_le_mul (Nat.le_succ _) (h n)

theorem choose_work (A k : ℕ) (W J : Poly) : ∃ p : Poly, ∀ n,
    totalFee J (W.eval (n+1)) A k n ≤ searchWork A k n*p.eval (n+1) := by
  let T := coinSpan A k
  let R := fun n => 2*majorityHalf n
  let g0 := fun n => seedWidth n+T n+1
  let g1 := fun n => (R n+1)*g0 n
  let g2 := fun n => (trials n+1)*g1 n
  let g3 := fun n => (n*n+1)*g2 n
  have p0 (n : ℕ) : 1 ≤ g0 n := Nat.succ_pos _
  have p1 (n : ℕ) : 1 ≤ g1 n := Nat.mul_pos (Nat.succ_pos _) (p0 n)
  have p2 (n : ℕ) : 1 ≤ g2 n := Nat.mul_pos (Nat.succ_pos _) (p1 n)
  have p3 (n : ℕ) : 1 ≤ g3 n := Nat.mul_pos (Nat.succ_pos _) (p2 n)
  have tap : Paid g0 T := ⟨1,fun n => by simp [g0];omega⟩
  have calls := (tap.add (Paid.small (small_const 11) p0)).times R
  let bank := fun n => W.eval (n+1)
  have load : Small (fun n => loadUnit (bank n)) :=
    (small_const 5).mul ((smallEval W).mul (((small_const 5).mul (smallEval W)).add (small_const 9)) |>.add (small_const 15)) |>.add (small_const 10)
  have preparation := (((((small_const 9).mul seed_small).add (small_const 28)).add ((smallEval W).comp_polynomial J)).add
    ((explicitPoly 120 4 1).mul load))
  have single : Paid g1 (fun n => trialFee J (bank n) n (T n)) := (Paid.small preparation p1).add calls
  have batch := (single.add (Paid.small (small_const 3) p1)).times trials
  have edge := (((Paid.small ((smallEval edgeTime).add (small_const 2)) p2).add batch).add (Paid.small (small_const 3) p2)).times (fun n => n*n)
  have pruning : Paid g3 (fun n => pruningFee J (bank n) A k n) := (Paid.small (small_const 2) p3).add edge
  have parser : Small prepCost := (((((small_const 10).mul small_dim.word).add ((small_const 4).mul small_dim)).add
    ((small_const 9).mul (small_dim.mul small_dim))).add (small_const 17))
  have short : Small (fun n => shortCost (bank n)) :=
    ((smallEval W).mul (((small_const 5).mul (smallEval W)).add (small_const 9))).add (small_const 15)
  have round : Small tourStepCost := ((smallEval (budget walkLimit walkStart).time).add
    ((small_const 2).add (small_dim.mul ((smallEval scanTime).add (small_const 3))))).add (smallEval (budget walkLimit walkEnd).time)
  have orbit : Small orbitCost := (small_const 8).add (small_dim.mul (round.add (small_const 3)))
  have full : Paid g3 (fun n => totalFee J (bank n) A k n) :=
    ((((Paid.small ((parser.add short).add (smallEval (scheduleBudget A k).time)) p3).add pruning).add
      (Paid.small orbit p3)).add (Paid.small (small_const 10) p3))
  obtain ⟨p,h⟩ := full
  exact ⟨p,fun n => by simpa only [g3,g2,g1,g0,T,R,bank,searchWork,Nat.mul_assoc] using h n⟩

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

namespace DirectedHamiltonicity.Main.CycleReduction.SearchProgram
open TargetedSamplers TargetedSamplers.Structured RegisterCode OuterMachine GraphWords
noncomputable section

def bigBranch (w : Layout) (prepare : Cmd) (A k : ℕ) :=
  (code w (parameterLines A k)).seq ((lit w .mask 1).seq ((indexLoop w .edge .nSq (processEdge w prepare)).seq (orbitCode w)))
def program (w : Layout) (readGraph prepare : Cmd) (A k : ℕ) :=
  ((Code.pure readGraph).seq (.pure (setup w).cmd)).seq
    ((test w .n .one (shortCode w) (bigBranch w prepare A k)).seq (.pure (.op (.output (w.reg .valid)))))

theorem big_run (w : Layout) (prepare : Cmd) (P J : Poly) (enc : Encoder w prepare P J) (Q : Program)
    (A k : ℕ) (qt : QueryTime Q A k) (n g B : ℕ) (adj : Fin n → Fin n → Bool) (τ : Tapes) (d : Data)
    (large : 1 < n) (fit : d.bank.Fits B) (h : Header w d n g) (original : graph n g=adj)
    (clock : d.epoch=0) (startWidth : ∀ i,(peek w d i).size ≤ 8*(n+1)^2+8) (space : Room P A k n B) :
    ∃ t j, Eval Q τ B (bigBranch w prepare A k) d t j ∧
      j ≤ (scheduleBudget A k).time.eval (n+1)+1+pruningFee J B A k n+orbitCost n ∧ t.bank.Fits B ∧
      t.bank.mem (w.reg .valid)=(answer Q A k adj τ.coins).toNat ∧ t.bank.out=d.bank.out := by
  have hb : 2 ≤ B := by have := space.parser;omega
  let g' := g%2^(n*n)
  have clip : graph n g'=adj := (clipped n g).trans original
  have size : g' < 2^(n*n) := Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨a,j,ex1,cost,af,params,am,ao,ae⟩ := compute_parameters w Q τ A k n g B d fit hb startWidth h.dim h.zero h.one h.two h.graph space.schedule
  have wr := setWord Q τ B (w.reg .mask) 1 a af (by change 1 ≤ B;omega)
  let b : Data := {a with bank := a.bank.write (w.reg .mask) 1}
  have s : EdgeState w b A k n 0 g' := by
    refine ⟨params.transport ?_,?_,?_⟩
    · intro r use
      have ne : r.index≠Reg.mask.index := by intro eq;rw [eq] at use;exact (by decide : Reg.mask.index ∉ coreRegs) use
      simp [b,Store.write,regEq,ne]
    · simpa [b,Store.write,regEq,Reg.index,g'] using am
    · simp [b,Store.write]
  have ep : (b.epoch+n*n*(trials n*(2*majorityHalf n))).size ≤ B := by
    change (a.epoch+_).size ≤ B;rw [ae,clock,Nat.zero_add];exact space.epoch
  obtain ⟨c,l,ex2,fee,cf,word,cp,co⟩ := prune_run w prepare P J enc Q A k qt τ b wr.2 s size ep space.trial space.edge
  let rem := prefixWord Q A k n τ.coins g' (n*n)
  have repr : edges (graph n rem)=remaining Q adj (panelFromTape n (coinSpan A k n) τ.coins) := by
    rw [←clip];exact prefix_graph ..
  obtain ⟨t,m,ex3,tim,tf,ans,out⟩ := orbit_run w Q τ n rem B (by omega) c cf hb space.walk
    ⟨word,cp.dim,cp.zero,cp.one,cp.two⟩ ((prefix_le ..).trans_lt size)
  refine ⟨t,_,ex1.seq (wr.1.seq (ex2.seq ex3)),?_,tf,?_,out.trans (co.trans ao)⟩
  · change l ≤ pruningFee J B A k n at fee;omega
  · unfold answer;rw [if_neg (by omega),←repr];exact ans

theorem controller (Q : Program) (A k : ℕ) (qt : QueryTime Q A k) : BoundedController Q A k := by
  obtain ⟨readGraph,read⟩ := read_cycle_graph_ram
  obtain ⟨w,prepare,P,J,enc⟩ := encoder_exists
  obtain ⟨W,space⟩ := choose_width A k P
  obtain ⟨H,bound⟩ := choose_work A k W J
  refine ⟨program w readGraph prepare A k,W,H,?_⟩
  intro n adj coins
  let B := W.eval (n+1)
  let τ := runTapes (encodeDigraph n adj) coins
  have room := space n
  obtain ⟨d,j,g,start,time,fit,h,graph,out,ep,ws,gs⟩ := bootstrap w Q readGraph read n B adj coins room.parser
  let bit := answer Q A k adj coins
  have dispatch : ∃ t l, Eval Q τ B (test w .n .one (shortCode w) (bigBranch w prepare A k)) d t l ∧
      j+l+1 ≤ totalFee J B A k n ∧ t.bank.Fits B ∧ t.bank.mem (w.reg .valid)=bit.toNat ∧ t.bank.out=[] := by
    by_cases small : n ≤ 1
    · obtain ⟨t,k,ex,cost,tf,word,last⟩ := short_run w Q τ n g B adj d h small graph fit gs room.parser
      exact ⟨t,_,.yes fit (by rw [h.dim,h.one];exact small) ex,by unfold totalFee;omega,tf,by simpa [bit,answer,small] using word,last.trans out⟩
    · obtain ⟨t,l,ex,cost,tf,word,last⟩ := big_run w prepare P J enc Q A k qt n g B adj τ d (by omega) fit h graph ep ws room
      refine ⟨t,_,.no fit (by rw [h.dim,h.one];exact small) ex,?_,tf,word,last.trans out⟩
      unfold totalFee;omega
  obtain ⟨t,l,branch,charge,tf,result,empty⟩ := dispatch
  let emit := Op.output (w.reg .valid)
  have stable : (emit.eval τ t.bank).Fits B := tf
  have done : Eval Q τ B (.pure (.op emit)) t {t with bank := emit.eval τ t.bank} 1 := .pure tf (.op _ _ stable)
  refine ⟨_,_,start.seq (branch.seq done),?_,?_⟩
  · change t.bank.out++[t.bank.mem (w.reg .valid)!=0]=[bit]
    rw [empty,result];cases bit <;> rfl
  · exact (by omega : j+(l+1) ≤ totalFee J B A k n).trans (bound n)

end
end DirectedHamiltonicity.Main.CycleReduction.SearchProgram

open TargetedSamplers DirectedHamiltonicity.Main.CycleReduction DirectedHamiltonicity.Main.CycleReduction.OuterMachine

/-- Execute the finite search in the bounded controller language, with measured query calls. -/
theorem solution (Q : Program) (A k : ℕ) :
    QueryTime Q A k → BoundedController Q A k := by
  exact DirectedHamiltonicity.Main.CycleReduction.SearchProgram.controller Q A k
