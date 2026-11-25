-- Prove2me | solution 1 for DetDLP.d2_terminal_greedy_correct
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:03:19.626537+00:00
-- url     : https://prove2.me/submissions/fdcfa881-120f-49d0-9ad8-35142cacd49f

import Theorems.Thm_DetDLP_d2_greedy_energy_descent
set_option autoImplicit false
namespace DetDLP.D2.Check
open AppendixD4 Greedy Finset
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace DetDLP_W1_Queries

def edges (G : Graph) := List.ofFn fun e => ((ends G e).1.val,(ends G e).2.val)
def hosts {G : Graph} {b : ℕ} (h : Fin b → Fin G.nV) := List.ofFn fun j => (h j).val

theorem sep (G : Graph) : ∀ e ∈ edges G, ∀ f ∈ edges G, e.1 ≠ f.2 := by
  intro e he f hf; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  have hs (i : Fin G.nE) : G.side (ends G i).1 = false ∧ G.side (ends G i).2 = true := by
    have hb := G.bipartite i
    cases h : G.side (G.endpoints i).1 <;> cases hh : G.side (G.endpoints i).2 <;> simp_all [ends]
  intro eq; have eq' : (ends G i).1 = (ends G j).2 := Fin.ext eq
  have h := (hs i).1; rw [eq',(hs j).2] at h; contradiction

private theorem ep_aux {α : Type} (xs : List α) (f g : α → ℕ) :
    (xs.flatMap fun x => [f x,g x]).length = 2*xs.length ∧
    ∀ j (hj : j < xs.length), (xs.flatMap fun x => [f x,g x]).getD (2*j) 0 = f xs[j] ∧
      (xs.flatMap fun x => [f x,g x]).getD (2*j+1) 0 = g xs[j] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    refine ⟨by simp [ih.1];omega,?_⟩; intro j hj; cases j with
    | zero => simp [List.getD]
    | succ j => simpa [Nat.mul_succ,List.getD_eq_getElem?_getD] using ih.2 j (by simpa using hj)

private theorem decode_edges (G : Graph) :
    let ep := (List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val]
    (List.range (ep.length / 2)).map (oriented (List.ofFn G.side) ep) = edges G := by
  intro ep
  have h := ep_aux (List.finRange G.nE) (fun e => (G.endpoints e).1.val) (fun e => (G.endpoints e).2.val)
  have hn : ep.length/2 = G.nE := by simp [ep,h.1]
  apply List.ext_getElem; · simp [hn,edges]
  intro j hj hj'; have hj'' : j < (List.finRange G.nE).length := by simpa [hn] using hj
  obtain ⟨hf,hg⟩ := h.2 j hj''
  simp only [List.getElem_finRange] at hf hg
  let i : Fin G.nE := ⟨j,by simpa using hj''⟩
  change ep.getD (2*j) 0 = (G.endpoints i).1.val at hf
  change ep.getD (2*j+1) 0 = (G.endpoints i).2.val at hg
  simp only [List.getElem_map,List.getElem_range,oriented,hf,hg,edges,List.getElem_ofFn]
  have side (z : Fin G.nV) : (List.ofFn G.side).getD z.val false = G.side z := by rw [List.getD_eq_getElem _ _ (by simpa using z.isLt)]; simp
  rw [side]; change _ = ((ends G i).1.val,(ends G i).2.val)
  cases hh : G.side (G.endpoints i).1 <;> simp [ends,hh]

theorem range_fin (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem run_eq (G : Graph) (a : ℕ) {b : ℕ} (h : Fin b → Fin G.nV) :
    let ks := (List.range a).map (64^·)
    let p := solve (List.range G.nV) (List.range (64^a)) ks (hosts h) (edges G)
    run (input G a h) = encodeNatListBin (ks.flatMap fun k => p.map fun g => g/k%64) := by
  have ha : a ≤ 64^a := by
    induction a with
    | zero => decide
    | succ a ih => rw [pow_succ]; have hp : 0 < 64^a := Nat.pow_pos (by decide : 0 < 64); omega
  simp only [run,input,third,second,lastField,first_cons,more_cons,id_eq,decode_count,List.length_replicate,
    Nat.min_eq_left ha,BipartiteMultigraph.encode,List.length_ofFn,w5_M6Sort.decode_encode,decode_edges,hosts]

def mx (vs : List ℕ) (es : List Edge) := maxOn vs (fun j => (es.filter (fun e => e.1 == j || e.2 == j)).length)
def tau (hs : List ℕ) := maxOn hs (fun j => hs.count j)
private theorem max_aux {α : Type} (l : List α) (f : α → ℕ) (s : ℕ) :
    let z := (l.map f).foldl max s
    s ≤ z ∧ (∀ x ∈ l, f x ≤ z) ∧ ∀ n, s ≤ n → (∀ x ∈ l, f x ≤ n) → z ≤ n := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h,h',hm⟩ := ih (max s (f x))
    exact ⟨(le_max_left ..).trans h,fun y hy => (List.mem_cons.mp hy).elim (fun eq => by subst y; exact (le_max_right ..).trans h) (h' y),
      fun n hsn hh => hm n (max_le hsn (hh x (by simp))) (fun y hy => hh y (by simp [hy]))⟩

theorem max_lower {α : Type} (l : List α) (f : α → ℕ) (x : α) (hx : x ∈ l) : f x ≤ maxOn l f := (max_aux l f 0).2.1 x hx
theorem max_upper {α : Type} (l : List α) (f : α → ℕ) (n : ℕ) (h : ∀ x ∈ l, f x ≤ n) : maxOn l f ≤ n := (max_aux l f 0).2.2 n (Nat.zero_le _) h

theorem port_len (G : Graph) (j : Fin G.nV) : ((edges G).filter (fun e => e.1 == j.val || e.2 == j.val)).length = G.deg j := by
  unfold edges BipartiteMultigraph.deg BipartiteMultigraph.ports
  rw [List.ofFn_eq_map,List.filter_map]; simp only [List.length_map]; congr 2
  funext e; apply Bool.eq_iff_iff.mpr; cases h : G.side (G.endpoints e).1 <;> simp [ends,h,Fin.ext_iff,or_comm]

theorem mx_eq (G : Graph) : mx (List.range G.nV) (edges G) = G.maxDeg := by
  apply le_antisymm
  · apply max_upper; intro j hj; let i : Fin G.nV := ⟨j,List.mem_range.mp hj⟩
    exact (port_len G i).le.trans (Finset.le_sup (f:=G.deg) (mem_univ i))
  · apply Finset.sup_le; intro i _; rw [←port_len]; exact max_lower (List.range G.nV) (fun j => ((edges G).filter (fun e => e.1 == j || e.2 == j)).length) i.val (by simp)

theorem count_host (G : Graph) {b : ℕ} (h : Fin b → Fin G.nV) (x : Fin b) :
    (hosts h).count (h x).val = (univ.filter fun y => h x = h y).card := by
  simp only [hosts,List.count_eq_length_filter,List.ofFn_eq_map,List.filter_map,List.length_map]
  have hh : ((List.finRange b).filter (fun z => (h z).val == (h x).val)).toFinset = univ.filter (fun y => h x = h y) := by
    ext y; simp only [List.mem_toFinset,List.mem_filter,List.mem_finRange,true_and,beq_iff_eq,mem_filter,mem_univ,Fin.ext_iff]; exact eq_comm
  rw [←hh,List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange _))]; rfl
end DetDLP.D2.Check
set_option autoImplicit false
namespace DetDLP.D2.Check
open Finset AppendixD4
def hist {m : ℕ} {γ : Type*} [DecidableEq γ] (f : Fin m → γ) (g : γ) : ℕ :=
  ∑ x, if f x = g then 1 else 0

private theorem hist_sum {m : ℕ} {γ : Type*} [DecidableEq γ] [Fintype γ] (f : Fin m → γ) :
    ∑ g, hist f g = m := by unfold hist; rw [sum_comm]; simp

theorem hist_collision {m : ℕ} {γ : Type*} [DecidableEq γ] [Fintype γ] (f : Fin m → γ) :
    ∑ g, hist f g^2 = ∑ x, ∑ y, if f x = f y then 1 else 0 := by
  have hp (g : γ) : hist f g^2 = ∑ x, if f x = g then hist f g else 0 := by
    calc
      _ = (∑ x,if f x = g then 1 else 0)*hist f g := by rw [pow_two]; rfl
      _ = _ := by rw [sum_mul]; simp [ite_mul]
  simp_rw [hp]; rw [sum_comm]; simp only [sum_ite_eq,mem_univ,if_true,hist]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  by_cases h : f x = f y <;> simp_all [eq_comm]

private theorem centered {γ : Type*} [Fintype γ] (X : γ → ℕ) (K M : ℕ)
    (hK : Fintype.card γ = K) (hM : ∑ i,X i = M) :
    ∑ i, ((K:ℤ)*(X i:ℤ)-M)^2 = (K:ℤ)*((K:ℤ)*(∑ i, (X i:ℤ)^2)-(M:ℤ)^2) := by
  have hs : (∑ i, (X i:ℤ)) = (M:ℤ) := by exact_mod_cast hM
  calc
    _ = ∑ i, ((K:ℤ)^2 * (X i:ℤ)^2 -(2*(K:ℤ)*M)*(X i:ℤ)+(M:ℤ)^2) := by
      apply sum_congr rfl; intros; ring
    _ = _ := by rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hs,sum_const,card_univ,hK,nsmul_eq_mul]; ring

private theorem center_bounds {γ : Type*} [Fintype γ] (X : γ → ℕ) (K M : ℕ)
    (hK : Fintype.card γ = K) (hM : ∑ i,X i = M) (hpos : 0 < K) :
    let V : ℤ := (K:ℤ)*(∑ i, (X i:ℤ)^2)-(M:ℤ)^2
    0 ≤ V ∧ ∀ i, ((K:ℤ)*(X i:ℤ)-M)^2 ≤ K*V := by
  intro V
  have hc := centered X K M hK hM
  change _ = (K:ℤ)*V at hc
  constructor
  · have h : 0 ≤ (K:ℤ)*V := hc ▸ sum_nonneg (fun _ _ => sq_nonneg _)
    have hk : 0 < (K:ℤ) := by exact_mod_cast hpos
    exact nonneg_of_mul_nonneg_right h hk
  · intro i; rw [← hc]; exact single_le_sum (f := fun j => ((K:ℤ)*(X j:ℤ)-M)^2) (fun _ _ => sq_nonneg _) (mem_univ i)

theorem caps (G : Graph) (a b τ W : ℕ) (hW : 0 < W) (hwτ : b ≠ 0 → W ≤ b*τ)
    (hm : 0 < G.nE*G.maxDeg) (hsize : (a+2)*(64^a)^4*G.maxDeg ≤ G.nE)
    (F : Fin G.nE → Fin (64^a) × Fin (64^a)) (D : Fin a → Fin b → Fin 64)
    (hL : let K := (64^a)^2; let v := G.nE*G.maxDeg
          64*K*(W*(∑ c,hist F c^2)+v*(∑ i,∑ g,hist (D i) g^2)) ≤
          64*W*G.nE^2 + v*a*K*b^2 + 64*K*W*v*(a+2)) :
    (∀ c, (64^a)^2*hist F c ≤ 2*G.nE) ∧
      ∀ i g, 32*hist (D i) g ≤ b+512*(a+2)*τ := by
  let K : ℕ := (64^a)^2
  let X := hist F
  let Y := fun i => hist (D i)
  let E : ℤ := K*(∑ c, (X c:ℤ)^2)-(G.nE:ℤ)^2
  let V (i : Fin a) : ℤ := 64*(∑ g, (Y i g:ℤ)^2)-(b:ℤ)^2
  let T := ∑ i, V i
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨hE,hX⟩ := center_bounds X K G.nE (by simp [K,pow_two]) (hist_sum F) hK
  change 0 ≤ E at hE
  change ∀ c, ((K:ℤ)*(X c:ℤ)-G.nE)^2 ≤ K*E at hX
  have hv (i : Fin a) := center_bounds (Y i) 64 b (by simp) (hist_sum _) (by decide)
  have hV (i : Fin a) : 0 ≤ V i := (hv i).1
  have hT : 0 ≤ T := sum_nonneg (fun i _ => hV i)
  have hY (i : Fin a) (g : Fin 64) : (64*(Y i g:ℤ)-b)^2 ≤ 64*T :=
    ((hv i).2 g).trans (mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hV j) (mem_univ i)) (by decide))
  have hve : T = 64*(∑ i, ∑ g, (Y i g:ℤ)^2)-(a:ℤ)*(b:ℤ)^2 := by
    dsimp only [T,V]; rw [sum_sub_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hraw : (64:ℤ)*K*((W:ℤ)*(∑ c,(X c:ℤ)^2) + ((G.nE:ℤ)*G.maxDeg)*(∑ i,∑ g,(Y i g:ℤ)^2)) ≤
      64*(W:ℤ)*(G.nE:ℤ)^2 + ((G.nE:ℤ)*G.maxDeg)*a*K*(b:ℤ)^2 + 64*K*W*((G.nE:ℤ)*G.maxDeg)*(a+2) := by exact_mod_cast hL
  let w : ℤ := W
  let v : ℤ := (G.nE:ℤ)*G.maxDeg
  have hw : 0 < w := by dsimp only [w]; exact_mod_cast hW
  have hpos : 0 < v := by dsimp only [v]; exact_mod_cast hm
  have kpos : 0 < (K:ℤ) := by exact_mod_cast hK
  have comb : 64*w*E + (K:ℤ)*v*T ≤ 64*(K:ℤ)*w*v*((a:ℤ)+2) := by
    dsimp only [E,w,v]; rw [hve]; nlinarith only [hraw]
  have hecap : E ≤ K*v*((a:ℤ)+2) := by
    apply le_of_mul_le_mul_left (a := 64*w) _ (by positivity)
    nlinarith only [comb,mul_nonneg (mul_nonneg kpos.le hpos.le) hT]
  have htcap : T ≤ 64*w*((a:ℤ)+2) := by
    apply le_of_mul_le_mul_left (a := (K:ℤ)*v) _ (by positivity)
    nlinarith only [comb,mul_nonneg (mul_nonneg (by decide : (0:ℤ) ≤ 64) hw.le) hE]
  constructor
  · intro c
    have hM : ((a:ℤ)+2)*(K:ℤ)^2*G.maxDeg ≤ G.nE := by
      have hK4 : K^2 = (64^a)^4 := by dsimp only [K]; ring
      exact_mod_cast (show (a+2)*K^2*G.maxDeg ≤ G.nE by rw [hK4]; exact hsize)
    have hx' := (hX c).trans (mul_le_mul_of_nonneg_left hecap kpos.le)
    have hbound := mul_le_mul_of_nonneg_left hM (show 0 ≤ (G.nE:ℤ) by positivity)
    have hnat : (K:ℤ)*(X c:ℤ) ≤ 2*G.nE := by
      by_contra! hi
      dsimp only [v] at hx'
      have hp : 0 < (K:ℤ)*(X c:ℤ) := lt_of_le_of_lt (by positivity : (0:ℤ) ≤ 2*G.nE) hi
      nlinarith only [hx',hbound,mul_pos (sub_pos.mpr hi) hp]
    exact_mod_cast hnat
  · intro i g
    by_cases bz : b = 0
    · subst b; simp [hist]
    have hwb : (W:ℤ) ≤ (b:ℤ)*τ := by exact_mod_cast hwτ bz
    have hyy := (hY i g).trans (mul_le_mul_of_nonneg_left htcap (by decide : (0:ℤ) ≤ 64))
    dsimp only [w] at hyy
    have hh : 32*(Y i g:ℤ) ≤ b+512*((a:ℤ)+2)*τ := by
      by_contra! hi
      have hz : 0 < 64*(Y i g:ℤ)-b+(b+1024*((a:ℤ)+2)*τ) := by nlinarith
      nlinarith only [hyy,mul_nonneg (sub_nonneg.mpr hwb) (show (0:ℤ) ≤ 4096*((a:ℤ)+2) by positivity),sq_nonneg ((b:ℤ)-1024*((a:ℤ)+2)*τ),
        mul_pos (show 0 < 64*(Y i g:ℤ)-b-(b+1024*((a:ℤ)+2)*τ) by linarith) hz]
    exact_mod_cast hh
end DetDLP.D2.Check
set_option autoImplicit false
namespace DetDLP.D2.Check
open AppendixD4 Greedy Finset
private theorem total_le {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) : total l f ≤ total l g := by
  induction l with | nil => rfl | cons x l ih => exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
private theorem total_const {α : Type} (l : List α) (c : ℕ) : total l (fun _ => c) = l.length*c := by simp [total]
private theorem total_add {α : Type} (l : List α) (f g : α → ℕ) : total l (fun x => f x + g x) = total l f + total l g := by induction l <;> simp_all [total] <;> omega
private theorem total_filter {α : Type} (l : List α) (P : α → Bool) (n : ℕ) : total l (fun x => if P x then n else 0) = (l.filter P).length*n := by induction l <;> simp_all [total,List.filter_cons] <;> split <;> simp_all [Nat.succ_mul,add_comm]
private theorem init_edge (G : Graph) (q : ℕ) (hq : 0 < q) : edgeCost [] q (edges G) ≤ G.nE^2+2*G.nE*G.maxDeg*q^2 := by
  let l := edges G
  have hn : l.length = G.nE := by simp [l,edges]
  let inc := fun j (f : Edge) => f.1 == j || f.2 == j
  have per (e : Edge) (he : e ∈ l) : total l (fun f => factor [] q 1 e.1 f.1 * factor [] q 1 e.2 f.2) ≤ G.nE+2*G.maxDeg*q^2 := by
    have he' := he; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he'
    let u := (ends G i).1; let v := (ends G i).2
    change total l (fun f => factor [] q 1 u.val f.1 * factor [] q 1 v.val f.2) ≤ _
    calc _ ≤ total l (fun f => 1 + ((if inc u.val f then q^2 else 0) + (if inc v.val f then q^2 else 0))) := by
           apply total_le; intro f _
           have inc1 (h : u.val = f.1) : inc u.val f = true := by simp [inc,h]
           have inc2 (h : v.val = f.2) : inc v.val f = true := by simp [inc,h]
           by_cases h : u.val = f.1 <;> by_cases h' : v.val = f.2 <;> simp only [factor,List.length_nil,Nat.not_lt_zero,false_and,if_false,h,h',ite_true,ite_false] <;> first | rw [if_pos (inc1 h),if_pos (inc2 h')] | rw [if_pos (inc1 h)] | rw [if_pos (inc2 h')] | skip
           all_goals simp only [inc,beq_self_eq_true,Bool.true_or,Bool.or_true,if_true]; (try split_ifs) <;> nlinarith [Nat.mul_le_mul_left q hq]
         _ ≤ _ := by rw [total_add,total_add,total_const,total_filter,total_filter,hn,port_len G u,port_len G v]; have hu := Finset.le_sup (f:=G.deg) (mem_univ u); have hv := Finset.le_sup (f:=G.deg) (mem_univ v); change G.deg u ≤ G.maxDeg at hu; change G.deg v ≤ G.maxDeg at hv; nlinarith only [Nat.mul_le_mul_right (q^2) hu,Nat.mul_le_mul_right (q^2) hv]
  calc _ ≤ total l (fun _ => G.nE+2*G.maxDeg*q^2) := total_le l _ _ per
       _ = _ := by rw [total_const,hn]; ring

private theorem init_leg {G : Graph} {b : ℕ} (host : Fin b → Fin G.nV) (a : ℕ) :
    legCost [] ((List.range a).map (64^·)) (hosts host) ≤ a*b*(b+64*tau (hosts host)) := by
  let l := hosts host
  have hn : l.length = b := by simp [l,hosts]
  have per (k u : ℕ) (hu : u ∈ l) : total l (fun v => factor [] 64 k u v) ≤ b+64*tau l := by
    calc _ ≤ total l (fun v => 1 + (if v == u then 64 else 0)) := by
           apply total_le; intro v _; by_cases h : u=v; simp [factor,h]; simp [factor,h]
         _ ≤ _ := by rw [total_add,total_const,total_filter,hn,←List.count_eq_length_filter]; have h := max_lower l (fun j => l.count j) u hu; change l.count u ≤ tau l at h; omega
  calc _ ≤ total ((List.range a).map (64^·)) (fun _ => b*(b+64*tau l)) := by
           apply total_le; intro k _; calc _ ≤ total l (fun _ => b+64*tau l) := total_le l _ _ (per k)
                                          _ = _ := by rw [total_const,hn]
       _ = _ := by simp [total_const,Nat.mul_assoc,l]

private theorem total_ofFn {α : Type} {n : ℕ} (xs : Fin n → α) (f : α → ℕ) : total (List.ofFn xs) f = ∑ i, f (xs i) := by simp [total,List.map_ofFn,List.sum_ofFn,Function.comp_def]

def cell {G : Graph} {q : ℕ} (L : Fin G.nV → Fin q) (i : Fin G.nE) := (L (ends G i).1,L (ends G i).2)
def digit {G : Graph} {a b : ℕ} (L : Fin G.nV → Fin (64^a)) (host : Fin b → Fin G.nV) (i : Fin a) (x : Fin b) := finFunctionFinEquiv.symm (L (host x)) i

theorem raw (G : Graph) (a b : ℕ) (host : Fin b → Fin G.nV) (p : List ℕ) (hl : p.length = G.nV)
    (L : Fin G.nV → Fin (64^a)) (hL : ∀ x, p.getD x.val 0 = (L x).val)
    (hd : let q := 64^a; let ks := (List.range a).map (64^·); let w := max 1 (b*tau (hosts host)); let v := G.nE*G.maxDeg
          energy p q (edges G) ks (hosts host) w v ≤ energy [] q (edges G) ks (hosts host) w v) :
    let K := (64^a)^2; let v := G.nE*G.maxDeg; let W := max 1 (b*tau (hosts host))
    64*K*(W*(∑ c,hist (cell L) c^2)+v*(∑ i,∑ g,hist (digit L host i) g^2)) ≤
          64*W*G.nE^2 + v*a*K*b^2 + 64*K*W*v*(a+2) := by
  intro K v W; let q := 64^a; let ks := (List.range a).map (64^·)
  have ff (r k : ℕ) (x y : Fin G.nV) : factor p r k x.val y.val = if (L x).val/k%r = (L y).val/k%r then r else 0 := by
    by_cases h : x = y
    · simp [factor,h]
    · simp only [factor,show x.val ≠ y.val from fun h' => h (Fin.ext h'),if_false,hl,Fin.is_lt,and_self,if_true,hL]
  have he : edgeCost p q (edges G) = K*(∑ c,hist (cell L) c^2) := by
    rw [hist_collision,mul_sum]; unfold edgeCost edges; rw [total_ofFn]; apply sum_congr rfl; intro e _; rw [total_ofFn,mul_sum]; apply sum_congr rfl; intro f _
    simp only [ff,q,Nat.div_one,Nat.mod_eq_of_lt (Fin.isLt _),cell,Prod.mk.injEq,Fin.val_inj]
    split_ifs <;> simp_all [K,q,pow_two]
  have hy : legCost p ks (hosts host) = 64*(∑ i,∑ g,hist (digit L host i) g^2) := by
    have hk : ks = List.ofFn (fun i : Fin a => 64^i.val) := by rw [List.ofFn_eq_map]; dsimp only [ks]; rw [range_fin a,List.map_map]; rfl
    simp_rw [hist_collision]; unfold legCost; rw [hk,total_ofFn,mul_sum]; apply sum_congr rfl; intro i _
    rw [hosts,total_ofFn,mul_sum]; apply sum_congr rfl; intro x _; rw [total_ofFn,mul_sum]; apply sum_congr rfl; intro y _
    rw [ff]; change (if _ then _ else _) = 64*(if _ then _ else _); simp only [Fin.ext_iff]; split_ifs <;> first | rfl | contradiction
  change 64*W*edgeCost p q _ + q*q*v*legCost p ks _ ≤ 64*W*edgeCost [] q _ + q*q*v*legCost [] ks _ at hd
  rw [he,hy] at hd
  have h1 := Nat.mul_le_mul_left (64*W) (init_edge G q (by dsimp [q];positivity))
  have h2 := Nat.mul_le_mul_left (q*q*v) (init_leg host a)
  have h3 := hd.trans (Nat.add_le_add h1 h2)
  have h4 := Nat.mul_le_mul_left (64*a*K*v) (le_max_right 1 (b*tau (hosts host)))
  dsimp only [K,v,q,W,ks] at *; nlinarith only [h3,h4]
end DetDLP.D2.Check
set_option autoImplicit false
open DetDLP DetDLP.D2 DetDLP.D2.Greedy DetDLP.D2.Check DetDLP.AppendixD4 Finset

theorem solution : D2.Correct Greedy.run := by
  intro G a b host τ hM hs hτ ht
  let q := 64^a
  let ks := (List.range a).map (64^·)
  let l := hosts host
  let t := tau l
  let W := max 1 (b*t)
  let p := solve (List.range G.nV) (List.range q) ks l (edges G)
  obtain ⟨hl,hb,hd⟩ := d2_greedy_energy_descent (List.range G.nV) a l (edges G) (sep G)
  change p.length = _ at hl; rw [List.length_range] at hl
  change ∀ x ∈ p, x < q at hb
  have hp (x : Fin G.nV) : x.val < p.length := hl.symm ▸ x.isLt
  let L : Fin G.nV → Fin q := fun x => ⟨p.getD x.val 0, hb _ (by rw [List.getD_eq_getElem _ _ (hp x)]; exact List.getElem_mem _)⟩
  have hL (x : Fin G.nV) : p.getD x.val 0 = (L x).val := rfl
  let E : (Fin a → Fin 64) ≃ Fin q := finFunctionFinEquiv
  let lbl : Label a G := fun i x => E.symm (L x) i
  have ht' : t ≤ τ := by
    apply max_upper; intro j hj; obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hj; exact (count_host G host x).le.trans (ht x)
  have hW : 0 < W := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hwτ (hb : b ≠ 0) : W ≤ b*τ := max_le (Nat.mul_pos (by omega) hτ) (Nat.mul_le_mul_left b ht')
  let e : Fin G.nE := ⟨0,hM⟩
  let v := (G.endpoints e).1
  have hv : e ∈ G.ports v := by simp [BipartiteMultigraph.ports,v,List.mem_finRange]
  have hΔ : 0 < G.maxDeg := (List.length_pos_of_mem hv).trans_le (Finset.le_sup (f:=G.deg) (mem_univ v))
  have hm := Nat.mul_pos hM hΔ
  have hn : (edges G).length = G.nE := by simp [edges]
  have hl' : l.length = b := by simp [l,hosts]
  change energy p q (edges G) ks l (max 1 (l.length*t)) ((edges G).length*mx (List.range G.nV) (edges G)) ≤ energy [] q (edges G) ks l (max 1 (l.length*t)) ((edges G).length*mx (List.range G.nV) (edges G)) at hd
  rw [hn,hl',mx_eq] at hd
  rw [Nat.mul_comm 4 a,pow_mul] at hs
  have hs' := (Nat.mul_le_mul_left ((a+2)*(64^a)^4) (le_max_right 1 G.maxDeg)).trans hs
  obtain ⟨hc,hy⟩ := caps G a b τ W hW hwτ hm hs' (cell L) (digit L host) (raw G a b host p hl L hL hd)
  refine ⟨lbl,?_,?_,?_⟩
  · rw [run_eq]; unfold output; congr 1
    change ((List.range a).map (64^·)).flatMap (fun k => p.map (fun g => g/k%64)) = _
    rw [range_fin a,List.map_map,List.flatMap_map]; apply List.flatMap_congr; intro i _
    apply List.ext_getElem; · simp [hl]
    intro j hj hj'; have hj'' : j < G.nV := by simpa [hl] using hj
    simp only [List.getElem_map,List.getElem_ofFn]; change p[j]/64^i.val%64 = p.getD j 0/64^i.val%64
    rw [List.getD_eq_getElem _ _ (by simpa [hl] using hj'')]
  · have hq : 1 ≤ 64^a := Nat.one_le_pow _ _ (by decide)
    have hpow : 2^a ≤ 64^a := Nat.pow_le_pow_left (by decide) _
    have small : (64^a)^4 ≤ G.nE := by
      calc (64^a)^4 ≤ (a+2)*(64^a)^4 := Nat.le_mul_of_pos_left _ (by omega)
           _ ≤ _ := (Nat.le_mul_of_pos_right _ (by omega : 0 < max 1 G.maxDeg)).trans hs
    have pad : 2^a*(64^a)^2 ≤ G.nE := by
      calc 2^a*(64^a)^2 ≤ (64^a)*(64^a)^2 := Nat.mul_le_mul_right _ hpow
           _ = (64^a)^3 := by ring
           _ ≤ (64^a)^4 := Nat.pow_le_pow_right hq (by decide)
           _ ≤ G.nE := small
    intro x y
    have h := hc (E x,E y)
    have same (e : Fin G.nE) : ((fun i => lbl i (ends G e).1) = x ∧ (fun i => lbl i (ends G e).2) = y) ↔ cell L e = (E x,E y) := by simp [cell,lbl,Equiv.symm_apply_eq]
    simp_rw [same]; rw [Finset.card_filter]; apply (Nat.le_div_iff_mul_le (by positivity)).2
    rw [Nat.mul_comm 2 a,pow_mul,Nat.add_mul]; rw [Nat.mul_comm] at h
    exact (Nat.add_le_add h pad).trans (by omega)
  · intro i g; rw [Finset.card_filter]; exact hy i g
