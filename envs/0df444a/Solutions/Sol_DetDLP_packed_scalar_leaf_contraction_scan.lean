-- Prove2me | solution 1 for DetDLP.packed_scalar_leaf_contraction_scan
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:05:07.3978+00:00
-- url     : https://prove2.me/submissions/ce0d09dd-0e50-4938-a300-2f8ec803f9a5

import Definitions.Def_DetDLP_BTN

section

namespace DetDLP.PackedLeafContraction
open Finset Polynomial
variable {ell : ℕ} (G : BipartiteMultigraph)
abbrev table (ell : ℕ) := (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ
noncomputable def entry (a : Fin ell→ℕ) : ℕ[X] := ∑ i,monomial i.val (a i)
noncomputable def Z (A : table G ell) : ℕ[X] :=
  ∑ x : Fin G.nE→Bool,∏ v,entry (A v (fun j => x ((G.ports v).get j)))
def pack (b : ℕ) (a : Fin ell→ℕ) : ℕ := Nat.ofDigits b (List.ofFn a)
theorem pack_sum (b : ℕ) (a : Fin ell→ℕ) : pack b a=∑ i,a i*b^i.val := by
  induction ell with
  | zero => simp [pack]
  | succ n ih =>
    unfold pack
    rw [List.ofFn_succ, Nat.ofDigits, Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one, Fin.val_succ, pow_succ]
    have h := ih (fun i => a i.succ)
    unfold pack at h; rw [h]
    rw [mul_comm b,Finset.sum_mul]
    congr 1; apply sum_congr rfl; intro i _; ring

theorem eval_entry (b : ℕ) (a : Fin ell→ℕ) : (entry a).eval b=pack b a := by
  rw [entry,eval_finsetSum,pack_sum]; simp [eval_monomial]
def acc (b : ℕ) (A : table G ell) : ℕ :=
  ∑ x : Fin G.nE→Bool,∏ v,pack b (A v (fun j => x ((G.ports v).get j)))
def width (P ell : ℕ) := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P

theorem eval_acc (A : table G ell) (b : ℕ) : (Z G A).eval b=acc G b A := by
  simp [Z,acc,eval_finsetSum,eval_prod,eval_entry]

theorem mass (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) :
    acc G 1 A<2^(width G P ell) := by
  let W := P+Nat.clog 2 ell
  have loc (v : Fin G.nV) (t : Fin (G.deg v)→Bool) : (entry (A v t)).eval 1 ≤2^W := by
    rw [entry,eval_finsetSum]; simp only [eval_monomial,one_pow,mul_one]
    calc
      _ ≤ ∑ _ : Fin ell,2^P := sum_le_sum fun i _ => (ha v t i).le
      _ = ell*(2^P) := by simp
      _ ≤ (2^(Nat.clog 2 ell))*(2^P) := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
      _ = _ := by rw [mul_comm,← pow_add]
  have term (x : Fin G.nE→Bool) : (∏ v,(entry (A v (fun j => x ((G.ports v).get j)))).eval 1) ≤ (2^W)^G.nV := by
    calc
      _ ≤ ∏ _ : Fin G.nV,2^W := prod_le_prod' (fun v _ => loc v _)
      _ = _ := by simp
  unfold acc
  simp_rw [← eval_entry]
  calc
    _ ≤ ∑ _ : Fin G.nE→Bool,(2^W)^G.nV := sum_le_sum fun x _ => term x
    _ = 2^G.nE*(2^W)^G.nV := by simp
    _ = 2^(G.nE+G.nV*W) := by rw [pow_add 2 G.nE, Nat.mul_comm G.nV W,pow_mul]
    _ < 2^(width G P ell) := Nat.pow_lt_pow_right (by decide) (by unfold width; dsimp [W]; omega)

theorem coeff_le_mass (f : ℕ[X]) (j : ℕ) : f.coeff j≤f.eval 1 := by
  by_cases h : j∈f.support
  · have e := congrArg (Polynomial.eval 1) f.as_sum_support_C_mul_X_pow
    simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,one_pow,mul_one] at e
    rw [e]; exact single_le_sum (fun _ _ => Nat.zero_le _) h
  · rw [notMem_support_iff.mp h]; omega

theorem eval_digits (f : ℕ[X]) (b : ℕ) (d : ℕ) (hd : f.natDegree<d) :
    f.eval b=Nat.ofDigits b ((List.range d).map f.coeff) := by
  rw [eval_eq_sum_range' hd]
  induction d with
  | zero => simp
  | succ d _ =>
    have H : ∀ n, (∑ j∈range n,f.coeff j*b^j) = Nat.ofDigits b ((List.range n).map f.coeff) := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ,List.range_succ,List.map_append,Nat.ofDigits_append,ih]
        simp [Nat.ofDigits,mul_comm]
    exact H _

theorem digit (f : ℕ[X]) (b : ℕ) (hb : 1<b) (small : ∀ i,f.coeff i<b) (j : ℕ) :
    f.eval b/b^j%b=f.coeff j := by
  let d := max (f.natDegree+1) (j+1)
  have hd : f.natDegree<d := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hj : j<d := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let l := (List.range d).map f.coeff
  have hsmall : ∀ v∈l,v<b := by intro v hv; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv; exact small i
  rw [eval_digits f b d hd,Nat.ofDigits_div_pow_eq_ofDigits_drop j (by omega) l hsmall]
  have he : l.drop j=f.coeff j :: l.drop (j+1) := by
    rw [List.drop_eq_getElem_cons (by simpa [l] using hj)]
    simp [l]
  rw [he,Nat.ofDigits,Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (small j)

theorem exact_coefficients (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) (j : ℕ) :
    let b := 2^(width G P ell)
    acc G b A / b^j % b = (Z G A).coeff j := by
  intro b; rw [← eval_acc]
  have mh := mass G P A ha
  rw [← eval_acc] at mh
  apply digit _ _ (one_lt_pow₀ (by decide) (show width G P ell≠0 by unfold width; omega))
  exact fun i => (coeff_le_mass _ i).trans_lt mh

end DetDLP.PackedLeafContraction
end

section

namespace DetDLP.PackedLeafScan
open Finset Polynomial PackedLeafContraction
def bits (n k : ℕ) (j : Fin n) := k.testBit j.val
theorem bijective (n : ℕ) : Function.Bijective (fun k : Fin (2^n) => bits n k.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp⟩
  intro x y h; apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j<n
  · exact congrFun h ⟨j,hj⟩
  · have hp := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_of_not_gt hj)
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hp),Nat.testBit_eq_false_of_lt (y.isLt.trans_le hp)]
variable {ell : ℕ} (G : BipartiteMultigraph)
def term (A : table G ell) (b k : ℕ) :=
  ∏ v,pack b (A v (fun i => bits G.nE k ((G.ports v).get i)))

def scan (A : table G ell) (b : ℕ) : ℕ→ℕ→ℕ→ℕ
  | 0,_,acc => acc
  | n+1,k,acc => scan A b n (k+1) (acc+term G A b k)

theorem scan_eq (A : table G ell) (b n k c : ℕ) :
    scan G A b n k c=c+∑ i∈range n,term G A b (k+i) := by
  induction n generalizing k c with
  | zero => simp [scan]
  | succ n ih =>
    rw [scan,ih,sum_range_succ']
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem full (A : table G ell) (b : ℕ) : scan G A b (2^G.nE) 0 0=acc G b A := by
  simp only [scan_eq,zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (Equiv.ofBijective _ (bijective G.nE)) _ _ (fun _ => rfl)

theorem int_poly (A : table G ell) : (Z G A).map (Nat.castRingHom ℤ)=
    BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ)) := by
  simp [Z,BTNContract,entry,Polynomial.map_prod,Polynomial.map_sum]

theorem word (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) :
    let W := width G P ell
    let b := 2^W
    let total := scan G A b (2^G.nE) 0 0
    let F := BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ))
    encodeNatListBin (List.ofFn fun i : Fin ell => total/b^i.val%b%(2^P)) =
      encodeNatListBin (List.ofFn fun i : Fin ell => (F.coeff i.val:ZMod (2^P)).val) := by
  intro W b total F
  apply congrArg encodeNatListBin; apply congrArg List.ofFn
  funext i
  change scan G A b (2^G.nE) 0 0/b^i.val%b%(2^P)=_
  rw [full,exact_coefficients G P A ha i.val]
  dsimp only [F]
  rw [← int_poly G A,coeff_map]
  simp [ZMod.val_natCast]

theorem product_bound (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P)
    (k : ℕ) (vs : Finset (Fin G.nV)) :
    let W := width G P ell
    let b := 2^W
    (∏ v∈vs,pack b (A v (fun i => bits G.nE k ((G.ports v).get i)))) ≤ b^(ell*G.nV) := by
  intro W b
  have hB : 1<b := one_lt_pow₀ (by decide) (by unfold W width; omega)
  have cap : 2^P≤b := Nat.pow_le_pow_right (by decide) (by unfold W width; omega)
  calc
    _ ≤ ∏ _v∈vs,b^ell := by
      apply prod_le_prod'; intro v _
      unfold pack
      apply le_of_lt
      simpa only [List.length_ofFn] using Nat.ofDigits_lt_base_pow_length hB (l:=List.ofFn
        (A v (fun i => bits G.nE k ((G.ports v).get i)))) (by
        intro z hz; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz; exact (ha _ _ j).trans_le cap)
    _ = b^(ell*vs.card) := by simp [pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by simpa using vs.card_le_univ))

theorem prefix_size (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) (n : ℕ) (hn : n≤2^G.nE) :
    (scan G A (2^(width G P ell)) n 0 0).size≤G.nE+width G P ell*(ell*G.nV)+1 := by
  let W := width G P ell
  let b := 2^W
  have bound (k : ℕ) : term G A b k≤b^(ell*G.nV) := product_bound G P A ha k univ
  have H : scan G A b n 0 0≤2^(G.nE+W*(ell*G.nV)) := by
    simp only [scan_eq,zero_add]
    calc
      _ ≤ ∑ _∈range n,b^(ell*G.nV) := sum_le_sum fun k _ => bound k
      _ = n*(b^(ell*G.nV)) := by simp
      _ ≤ 2^G.nE*(b^(ell*G.nV)) := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [pow_add 2 G.nE,pow_mul 2 W]
  apply Nat.size_le.mpr
  exact H.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
end DetDLP.PackedLeafScan
end

open DetDLP Finset

theorem solution {ell : ℕ} (G : BipartiteMultigraph) (P : ℕ)
    (A : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ) (ha : ∀ v t i,A v t i<2^P) :
    let W := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P
    let b := 2^W
    let factor (k : ℕ) (v : Fin G.nV) := Nat.ofDigits b (List.ofFn
      (A v (fun j => k.testBit ((G.ports v).get j).val)))
    let total (n : ℕ) := ∑ k∈range n,∏ v,factor k v
    let F := BTNContract G (fun v t => ∑ i : Fin ell,Polynomial.monomial i.val (A v t i:ℤ))
    (encodeNatListBin (List.ofFn fun i : Fin ell => total (2^G.nE)/b^i.val%b%(2^P)) =
      encodeNatListBin (List.ofFn fun i : Fin ell => (F.coeff i.val:ZMod (2^P)).val)) ∧
    (∀ n,n≤2^G.nE→(total n).size≤G.nE+W*(ell*G.nV)+1) ∧
    (∀ k (vs : Finset (Fin G.nV)),(∏ v∈vs,factor k v)≤b^(ell*G.nV)) := by
  intro W b factor total F
  have scan (n : ℕ) : PackedLeafScan.scan G A b n 0 0=total n := by
    rw [PackedLeafScan.scan_eq]; simp only [zero_add]; rfl
  constructor
  · rw [← scan]; exact PackedLeafScan.word G P A ha
  constructor
  · intro n hn; rw [← scan]; exact PackedLeafScan.prefix_size G P A ha n hn
  · exact PackedLeafScan.product_bound G P A ha
