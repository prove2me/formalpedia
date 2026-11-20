-- Prove2me | solution 1 for DualSepClusterLP.denseAffineApproximation
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T14:51:31.405022+00:00
-- url     : https://prove2.me/submissions/1e765555-5d0b-490f-844a-3179f791dae0

import Definitions.Def_DualSepClusterLP_DenseTrials

section
namespace DualSepClusterLP.Dense
variable {ι : Type} (A : ι → ι → ℚ)

def errors (est : ι → ℚ) (keep : ι → Bool) : List ι → ℚ
  | [] => 0
  | i::xs => |est i-row A i (xs.filter keep)|+errors est keep xs

theorem value_shift (b c : ι → ℚ) (xs : List ι) :
    value A (fun i => b i+c i) xs = value A b xs + (xs.map c).sum := by
  induction xs with
  | nil => simp [value]
  | cons i xs ih => simp only [value,List.map_cons,List.sum_cons,ih]; ring

theorem hybrid (est : ι → ℚ) (keep : ι → Bool) (xs : List ι) (b : ι → ℚ) :
    value A b (greedy A est xs b) ≤ value A b (xs.filter keep)+errors A est keep xs := by
  induction xs generalizing b with
  | nil => simp [greedy,value,errors]
  | cons i xs ih =>
    let T := xs.filter keep
    have ha := le_abs_self (est i - row A i T)
    have hb := neg_le_abs (est i - row A i T)
    by_cases h : b i + est i ≤ 0
    · let v := fun j => b j+A i j
      let Y := greedy A est xs v
      have hs : value A v Y = value A b Y + row A i Y := value_shift A b (A i) Y
      have ht : value A v T = value A b T + row A i T := value_shift A b (A i) T
      have hh := ih v
      change value A v Y ≤ value A v T + errors A est keep xs at hh
      simp only [greedy,if_pos h,errors,List.filter_cons]
      cases hk : keep i <;> simp only [Bool.false_eq_true,if_false,if_true,value]
      · change b i + row A i Y + value A b Y ≤ value A b T + (|est i-row A i T|+_)
        linarith
      · change b i + row A i Y + value A b Y ≤ b i+row A i T+value A b T + (|est i-row A i T|+_)
        linarith [abs_nonneg (est i-row A i T)]
    · have hh := ih b
      change value A b (greedy A est xs b) ≤ value A b T + errors A est keep xs at hh
      simp only [greedy,if_neg h,errors,List.filter_cons]
      cases hk : keep i <;> simp only [Bool.false_eq_true,if_false,if_true,value]
      · change _ ≤ value A b T + (|est i-row A i T|+_)
        linarith [abs_nonneg (est i-row A i T)]
      · change _ ≤ b i + row A i T + value A b T + (|est i-row A i T|+_)
        linarith

theorem greedy_sublist (est : ι → ℚ) (xs : List ι) (b : ι → ℚ) :
    (greedy A est xs b).Sublist xs := by
  induction xs generalizing b with
  | nil => simp [greedy]
  | cons i xs ih =>
    rw [greedy]; split
    · exact (ih _).cons₂ _
    · exact (ih _).cons _

end DualSepClusterLP.Dense
end

section
namespace DualSepClusterLP.Dense
variable {p : ℕ} [Fact p.Prime]
abbrev Seed (p : ℕ) := ZMod p × ZMod p

def sample (s : Seed p) (x : ZMod p) := s.1*x+s.2

private def affinePair (u v : ZMod p) (hne : u≠v) : Seed p ≃ Seed p where
  toFun s := (sample s u,sample s v)
  invFun w := let a := (w.1-w.2)/(u-v); (a,w.1-a*u)
  left_inv := by
    intro s
    ext <;> simp only [sample] <;> field_simp [sub_ne_zero.mpr hne] <;> ring
  right_inv := by
    intro w
    ext <;> simp only [sample] <;> field_simp [sub_ne_zero.mpr hne] <;> ring

theorem sum_sample (u : ZMod p) (f : ZMod p → ℚ) :
    (∑ s : Seed p, f (sample s u)) = p*∑ x, f x := by
  rw [Fintype.sum_prod_type]
  have inner (a : ZMod p) : (∑ b, f (a*u+b)) = ∑ b, f b := Equiv.sum_comp (Equiv.addLeft (a*u)) f
  simp only [sample,inner,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]

theorem pair_sample (u v : ZMod p) (hne : u≠v) (f g : ZMod p → ℚ) :
    (∑ s : Seed p, f (sample s u)*g (sample s v)) = (∑ x, f x)*∑ x, g x := by
  calc
    _ = ∑ s : Seed p, f s.1*g s.2 := (affinePair u v hne).sum_comp (fun s => f s.1*g s.2)
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm

def avg (f : ZMod p → ℚ) := (∑ x, f x)/(p:ℚ)
def centered (f : ZMod p → ℚ) (x : ZMod p) := f x-avg f

theorem centered_sum (f : ZMod p → ℚ) : (∑ x,centered f x)=0 := by
  have hp : (p:ℚ)≠0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  simp only [centered,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,avg]
  field_simp <;> ring

theorem centered_sq (f : ZMod p → ℚ) (hf : ∀ i, |f i|≤1) :
    (∑ x, (centered f x)^2) ≤ p := by
  have hp : (0:ℚ)<p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hsum : (∑ x, f x) = (p:ℚ)*avg f := by unfold avg; field_simp
  have hh : (∑ x, (centered f x)^2) = (∑ x, (f x)^2) - p*(avg f)^2 := by
    simp only [centered,sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,
      Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,←Finset.mul_sum,hsum]
    ring
  have hsq : (∑ x, (f x)^2) ≤ ∑ _ : ZMod p,(1:ℚ) := by
    apply Finset.sum_le_sum
    intro i _
    have ha := (abs_le.mp (hf i)).1
    have hb := (abs_le.mp (hf i)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show (0:ℚ)≤1+f i by linarith)]
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,mul_one] at hsq
  rw [hh]
  linarith [mul_nonneg hp.le (sq_nonneg (avg f))]

def deviation {k : ℕ} (points : Fin k → ZMod p) (f : ZMod p → ℚ) (s : Seed p) :=
  ∑ i, centered f (sample s (points i))

theorem deviation_sq {k : ℕ} (points : Fin k → ZMod p) (hi : Function.Injective points)
    (f : ZMod p → ℚ) (hf : ∀ i, |f i|≤1) :
    (∑ s : Seed p,(deviation points f s)^2) ≤ k*p^2 := by
  let g := centered f
  have hterm (i j : Fin k) : (∑ s : Seed p, g (sample s (points i))*g (sample s (points j))) =
      if i=j then p*∑ x,(g x)^2 else 0 := by
    split
    · rename_i h; subst j
      simpa only [sq] using sum_sample (points i) (fun x => g x*g x)
    · rename_i h
      rw [pair_sample _ _ (fun e => h (hi e)) g g]
      simp [g,centered_sum]
  have hh : (∑ s : Seed p,(deviation points f s)^2) = ∑ i : Fin k, ∑ j : Fin k,
      ∑ s : Seed p, g (sample s (points i))*g (sample s (points j)) := by
    unfold deviation
    simp only [sq,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    simp only [g,mul_comm]
  rw [hh]
  simp only [hterm,Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have h := centered_sq f hf
  have hp : (0:ℚ)≤p := Nat.cast_nonneg _
  dsimp only [g]
  calc
    _ ≤ (k:ℚ)*((p:ℚ)*p) := by gcongr
    _ = _ := by ring

end DualSepClusterLP.Dense
end

section
namespace DualSepClusterLP.Dense
variable {p n k : ℕ} [Fact p.Prime]

theorem goodSeed (m : ℕ) {k : ℕ} (hk : k=m^2)
    (points : Fin k → ZMod p) (hi : Function.Injective points)
    (f : Fin n → ZMod p → ℚ) (hb : ∀ i u, |f i u|≤1) :
    ∃ s : Seed p, (∑ i, |deviation points (f i) s|) ≤ (n:ℚ)*m := by
  let v (s : Seed p) := ∑ i, (deviation points (f i) s)^2
  have hsum : (∑ s, v s) ≤ (n:ℚ)*k*p^2 := by
    unfold v
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ : Fin n, (k:ℚ)*p^2 := Finset.sum_le_sum (fun i _ => deviation_sq points hi (f i) (hb i))
      _ = _ := by simp [mul_assoc]
  have hs : ∃ s, v s ≤ (n:ℚ)*k := by
    by_contra! h
    have bad := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Seed p))) Finset.univ_nonempty (fun i _ => h i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,ZMod.card,nsmul_eq_mul,Nat.cast_mul] at bad
    nlinarith
  obtain ⟨s,hs⟩ := hs
  refine ⟨s,?_⟩
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun _ => (1:ℚ)) (fun i => |deviation points (f i) s|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,sq_abs] at hc
  change _ ≤ (n:ℚ)*v s at hc
  have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α:=ℚ) n)
  have hkn : (k:ℚ) = (m:ℚ)^2 := by exact_mod_cast hk
  rw [hkn] at hh
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℚ) n) (Nat.cast_nonneg (α:=ℚ) m)]

def points {p k : ℕ} (i : Fin k) : ZMod p := (i.val : ZMod p)

theorem points_inj (h : k≤p) : Function.Injective (points (p:=p) (k:=k)) := by
  intro i j e
  have eq := congrArg ZMod.val e
  simpa only [points, ZMod.val_natCast_of_lt (i.isLt.trans_le h),ZMod.val_natCast_of_lt (j.isLt.trans_le h),
    Fin.val_inj] using eq

def estimate (points : Fin k → ZMod p) (f : ZMod p → ℚ) (s : Seed p) : ℚ :=
  p/(k:ℚ)*∑ i, f (sample s (points i))

theorem estimate_error (points : Fin k → ZMod p) (f : ZMod p → ℚ) (s : Seed p)
    (hk : 0<k) : estimate points f s-(∑ u,f u) = p/(k:ℚ)*deviation points f s := by
  have hp : (p:ℚ)≠0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hk' : (k:ℚ)≠0 := by exact_mod_cast hk.ne'
  simp only [estimate,deviation,centered,avg,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem goodEstimator {k : ℕ} (m : ℕ) (hm : 0 < m) (hk : k=m^2) (hkp : k≤p)
    (f : Fin n → ZMod p → ℚ) (hb : ∀ i u, |f i u|≤1) :
    ∃ s : Seed p,
      (∑ i, |estimate (points (k:=k)) (f i) s-(∑ u, f i u)|) ≤ (n:ℚ)*p/m := by
  have hk' : 0<k := by rw [hk]; positivity
  obtain ⟨s,hs⟩ := goodSeed m hk (points (p:=p)) (points_inj hkp) f hb
  refine ⟨s,?_⟩
  simp only [estimate_error _ _ _ hk',abs_mul,abs_of_nonneg (show (0:ℚ)≤p/(k:ℚ) by positivity),←Finset.mul_sum]
  calc
    _ ≤ (p/(k:ℚ))*((n:ℚ)*m) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [hk]; push_cast; field_simp

end DualSepClusterLP.Dense
end

section
namespace DualSepClusterLP.Dense
variable {n p : ℕ}

def future (A : Fin n → Fin n → ℚ) (keep : Fin n → Bool) (i j : Fin n) : ℚ :=
  if i<j ∧ keep j then A i j else 0

private theorem list_errors {ι : Type} (A : ι → ι → ℚ) (est F : ι → ℚ) (keep : ι → Bool) (xs : List ι)
    (h : ∀ pre i suf, xs = pre ++ i::suf → row A i (suf.filter keep)=F i) :
    errors A est keep xs = (xs.map (fun i => |est i-F i|)).sum := by
  induction xs with
  | nil => simp [errors]
  | cons x xs ih =>
    simp only [errors,List.map_cons,List.sum_cons,h [] x xs rfl]
    rw [ih (fun pre i suf he => h (x::pre) i suf (by simp [he]))]

private theorem suffix_row (A : Fin n → Fin n → ℚ) (keep : Fin n → Bool)
    (pre : List (Fin n)) (i : Fin n) (suf : List (Fin n))
    (eq : List.finRange n = pre++i::suf) :
    row A i (suf.filter keep) = ∑ j, future A keep i j := by
  have sorted : (pre++i::suf).Pairwise (· < ·) := by
    rw [←eq]; exact List.pairwise_lt_finRange n
  obtain ⟨_,hs,hps⟩ := List.pairwise_append.mp sorted
  have hp (x) (hx : x∈pre) : x < i := hps _ hx _ (by simp)
  have ht (x) (hx : x∈suf) : i < x := (List.pairwise_cons.mp hs).1 _ hx
  have pp : (pre.map (future A keep i)).sum=0 := by
    have eqv : pre.map (future A keep i) = pre.map (fun _ => (0:ℚ)) := by
      apply List.map_congr_left
      intro x hx
      simp [future,not_lt_of_ge (hp x hx).le]
    simp [eqv]
  have ss : (suf.map (future A keep i)).sum = ((suf.filter keep).map (A i)).sum := by
    clear hp hps eq sorted hs
    induction suf with
    | nil => simp
    | cons x xs ih =>
      have hx := ht x (by simp)
      have hxs (j) (hj : j∈xs) := ht j (by simp [hj])
      simp only [List.map_cons,List.sum_cons,List.filter_cons]
      cases he : keep x <;> simp [future,hx,he,ih hxs]
  rw [← List.sum_ofFn,List.ofFn_eq_map,eq,List.map_append,List.sum_append,pp,List.map_cons,List.sum_cons]
  simp [future,ss,row]

theorem finite_errors (A : Fin n → Fin n → ℚ) (est : Fin n → ℚ) (keep : Fin n → Bool) :
    errors A est keep (List.finRange n) = ∑ i, |est i - ∑ j, future A keep i j| := by
  rw [list_errors A est _ keep _ (suffix_row A keep),←List.ofFn_eq_map,List.sum_ofFn]

def pad (f : Fin n → ℚ) (i : ZMod p) : ℚ := if h : i.val<n then f ⟨i.val,h⟩ else 0

theorem pad_sum [Fact p.Prime] (hp : n≤p) (f : Fin n → ℚ) :
    (∑ i : ZMod p,pad f i) = ∑ i, f i := by
  let pts : Fin n → ZMod p := fun i => (i.val : ZMod p)
  have hv (i : Fin n) : (pts i).val=i.val := ZMod.val_natCast_of_lt (i.isLt.trans_le hp)
  have hi : Function.Injective pts := by
    intro i j h
    exact Fin.ext ((hv i).symm.trans ((congrArg ZMod.val h).trans (hv j)))
  have he (u : ZMod p) : pad f u = ∑ i, if pts i=u then f i else 0 := by
    by_cases h : u.val<n
    · let i : Fin n := ⟨u.val,h⟩
      have hiu : pts i=u := ZMod.natCast_zmod_val u
      rw [Fintype.sum_eq_single i (by intro j hj; simp [←hiu,hi.eq_iff,hj])]
      simp [pad,h,hiu,i]
    · have no (i : Fin n) : pts i≠u := by
        intro e
        have hh := (congrArg ZMod.val e).symm.trans (hv i)
        exact h (hh ▸ i.isLt)
      simp [pad,h,no]
  simp only [he]
  rw [Finset.sum_comm]
  simp

end DualSepClusterLP.Dense
end

section
namespace DualSepClusterLP.Dense
variable {ι : Type} [DecidableEq ι]

private theorem finList {n : ℕ} (f : Fin n → ℚ) :
    ((List.finRange n).map f).sum = ∑ i,f i := by rw [←List.ofFn_eq_map,List.sum_ofFn]

private theorem natRange (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem <;> simp

private theorem full (U : List ι) : (List.finRange U.length).map U.get=U := by
  apply List.ext_getElem <;> simp

theorem value_map {α : Type} (A : ι → ι → ℚ) (b : ι → ℚ) (f : α → ι) (xs : List α) :
    value A b (xs.map f) = value (fun i j => A (f i) (f j)) (fun i => b (f i)) xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [value,row,List.map_map,Function.comp_def,ih]

private theorem greedy_map {α : Type} (A : ι → ι → ℚ) (est : ι → ℚ) (b : ι → ℚ)
    (f : α → ι) (xs : List α) :
    greedy A est (xs.map f) b = (greedy (fun i j => A (f i) (f j)) (fun i => est (f i))
      xs (fun i => b (f i))).map f := by
  induction xs generalizing b with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons,greedy]; split <;> simp [ih]

private theorem point_mod {p : ℕ} [Fact p.Prime] (s : Seed p) (l : ℕ) :
    (sample s (l:ZMod p)).val = (s.1.val*l+s.2.val)%p := by
  rw [←ZMod.val_natCast]
  congr 1
  simp [sample]

private theorem cast_bounds {n p : ℕ} (hn : p≤2*n) (m : ℕ) :
    (n:ℚ)*p/m ≤ 2*n^2/m := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h : (p:ℚ)≤2*(n:ℚ) := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)]

set_option maxHeartbeats 1000000 in
theorem large_spec (U : List ι) (hu : U.Nodup) (A : ι → ι → ℚ) (b : ι → ℚ)
    (keep : ι → Bool) (hA : ∀ i∈U, ∀ j∈U, |A i j|≤1) (m : ℕ) (hm : 0 < m)
    (large : m^2<U.length) :
    ∃ p a d : ℕ, ∃ bits : List Bool, 0<p ∧ p≤2*U.length ∧ a < p ∧ d < p ∧ bits.length=m^2 ∧
      value A b (greedy A (rawEstimate A U (m^2) p a d bits) U b) ≤
        value A b (U.filter keep) + 2*(U.length:ℚ)^2/m := by
  let n := U.length
  have hn : n≠0 := by dsimp [n]; omega
  obtain ⟨p,pp,hnp,hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  letI : Fact p.Prime := ⟨pp⟩
  let D (i j : Fin n) := A (U.get i) (U.get j)
  let B (i : Fin n) := b (U.get i)
  let K (i : Fin n) := keep (U.get i)
  let R (i : Fin n) := pad (p:=p) (future D K i)
  have bound (i : Fin n) (u : ZMod p) : |R i u|≤1 := by
    dsimp only [R,pad]
    split
    · unfold future; split
      · exact hA _ (List.get_mem ..) _ (List.get_mem ..)
      · norm_num
    · norm_num
  obtain ⟨s,hs⟩ := goodEstimator m hm rfl (large.le.trans hnp.le) R bound
  let idx (l : ℕ) := (s.1.val*l+s.2.val)%p
  let bits := List.ofFn (fun l : Fin (m^2) => U[idx l.val]?.elim false keep)
  let est := rawEstimate A U (m^2) p s.1.val s.2.val bits
  have he (i : Fin n) : est (U.get i) = estimate (points (k:=m^2)) (R i) s := by
    unfold est rawEstimate estimate
    rw [← natRange (m^2),List.map_map,finList]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have heq : (sample s (points l)).val = idx l.val := point_mod s _
    simp only [Function.comp_apply]
    change (if U.idxOf (U.get i) < idx l.val ∧ bits[l.val]?.getD false then
      U[idx l.val]?.elim 0 (A (U.get i)) else 0) = _
    have hii : U.idxOf (U.get i)=i.val := hu.idxOf_getElem i.val i.isLt
    simp only [R,pad,heq,bits,List.getElem?_ofFn,l.isLt,dif_pos,Option.getD_some,hii]
    by_cases h : idx l.val < U.length
    · simp [h,n,D,K,future,Fin.lt_def]
    · have hn' : ¬ idx l.val < n := h
      simp [hn',h,List.getElem?_eq_none (by omega : U.length≤idx l.val)]
  have hx : errors D (fun i => est (U.get i)) K (List.finRange n) ≤ (n:ℚ)*p/m := by
    rw [finite_errors]
    simpa only [he,R,pad_sum hnp.le] using hs
  have hg := hybrid D (fun i => est (U.get i)) K (List.finRange n) B
  refine ⟨p,s.1.val,s.2.val,bits,pp.pos,hpn,ZMod.val_lt _,ZMod.val_lt _,List.length_ofFn,?_⟩
  have hh : value A b (greedy A est U b) = value D B (greedy D (fun i => est (U.get i)) (List.finRange n) B) := by
    conv_lhs => arg 3; arg 3; rw [←full U]
    rw [greedy_map,value_map]
  have hv : value A b (U.filter keep) = value D B ((List.finRange n).filter K) := by
    conv_lhs => arg 3; arg 2; rw [←full U]
    rw [List.filter_map,value_map]
    rfl
  change value A b (greedy A est U b) ≤ _
  rw [hh,hv]
  have hbnd := hx.trans (cast_bounds hpn m)
  exact hg.trans (add_le_add (le_refl _) hbnd)

theorem small_spec (U : List ι) (hu : U.Nodup) (keep : ι → Bool) :
    ∃ bits : List Bool, bits.length=U.length ∧ small U bits=U.filter keep := by
  refine ⟨U.map keep,List.length_map _,?_⟩
  apply List.filter_congr
  intro i hi
  obtain ⟨j,rfl⟩ := List.get_of_mem hi
  simp [hu.idxOf_getElem j.val j.isLt]

end DualSepClusterLP.Dense
end

open DualSepClusterLP.Dense

theorem solution {ι : Type} [DecidableEq ι] (U : List ι) (hu : U.Nodup) (A : ι → ι → ℚ) (b : ι → ℚ)
    (keep : ι → Bool) (hA : ∀ i∈U, ∀ j∈U, |A i j|≤1) (m : ℕ) (hm : 0 < m)
    (large : m^2<U.length) :
    ∃ p a d : ℕ, ∃ bits : List Bool, 0<p ∧ p≤2*U.length ∧ a < p ∧ d < p ∧ bits.length=m^2 ∧
      value A b (greedy A (rawEstimate A U (m^2) p a d bits) U b) ≤
        value A b (U.filter keep) + 2*(U.length:ℚ)^2/m :=
  large_spec U hu A b keep hA m hm large
