-- Prove2me | solution 1 for DetDLP.bordered_column_hermite_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:58:41.901155+00:00
-- url     : https://prove2.me/submissions/c3041ae5-2e39-4403-810a-d77363504c80

import Definitions.Def_DetDLP_BorderedHermite
import Theorems.Thm_DetDLP_bordered_update_bit_program
import Theorems.Thm_DetDLP_bordered_update_computed_correctly
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CompileSpace_compile_word_answer_space

namespace DetDLP.CosetTapeBounds

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem frame_length (xs : List Bool) : (Encoding.frame xs).length = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x l ih => change (Encoding.frame l).length+1+1 = _; rw [ih]; simp; omega

theorem list_length {α : Type*} (f : α → List Bool) (xs : List α) :
    (Encoding.encodeList f xs).length = 1+(xs.map (fun x => 2*(f x).length+2)).sum := by
  induction xs with
  | nil => rfl
  | cons x l ih => simp [Encoding.encodeList,frame_length,ih]; omega

private theorem list_bound {α : Type*} (f : α → List Bool) (xs : List α) (d : ℕ)
    (h : ∀ x ∈ xs,(f x).length ≤ d) :
    (Encoding.encodeList f xs).length ≤ 1+xs.length*(2*d+2) := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x l ih =>
    have hi := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    change ((Encoding.frame (f x) ++ Encoding.encodeList f l).length+1) ≤ _
    rw [List.length_append,frame_length]
    calc
      _ ≤ (2*d+1)+(1+l.length*(2*d+2))+1 := by omega
      _ = _ := by simp only [List.length_cons]; ring

theorem count_bound (m k : ℕ) (hk : k ≤ m) : (countWord k).length ≤ bitLen m+1 := by
  rw [countWord]; split
  · simp
  · rw [Nat.size_eq_bits_len,Nat.size_le,bitLen,pow_succ]
    have := Nat.le_pow_clog (b := 2) (by decide) m
    have hp : 0 < 2^Nat.clog 2 m := by positivity
    omega

private theorem count_dim (n : ℕ) : (countWord n).length ≤ n+1 := by
  rw [countWord]; split
  · simp
  · rw [Nat.size_eq_bits_len,Nat.size_le]
    have h (k : ℕ) : k < 2^(k+1) := by
      induction k with
      | zero => decide
      | succ k ih => rw [pow_succ]; omega
    exact h n

theorem rep_bound {n m : ℕ} (x : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hx : ∀ i,x i ≤ m) (hB : ∀ i j, |B i j| ≤ (m:ℤ)) :
    (encodeCosetRep x B).length ≤ 9+2*(n*(2*(bitLen m+1)+2))+2*((n*n)*(2*(bitLen m+2)+2)) := by
  let vs := List.ofFn x
  let bs := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => B i j
  have hv : (encodeNatListBin vs).length ≤ 1+n*(2*(bitLen m+1)+2) := by
    refine (list_bound countWord vs (bitLen m+1) ?_).trans_eq ?_
    · intro v hv; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv; exact count_bound _ _ (hx i)
    · simp [vs]
  have hb : (Encoding.encodeList encodeIntBin bs).length ≤ 1+n*n*(2*(bitLen m+2)+2) := by
    refine (list_bound encodeIntBin bs (bitLen m+2) ?_).trans_eq ?_
    · intro z hz
      obtain ⟨i,_,hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
      change (countWord (B i j).natAbs).length+1 ≤ _
      have ha : (B i j).natAbs ≤ m := by rw [← Nat.cast_le (α := ℤ),Int.natCast_natAbs]; exact hB i j
      have := count_bound m _ ha; omega
    · simp [bs,List.length_flatMap,Fin.sum_univ_def]
  change (Encoding.encodeList id [encodeNatListBin vs,Encoding.encodeList encodeIntBin bs]).length ≤ _
  rw [list_length]; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,id_eq]; omega

/-- Bit length of the actual framed word on the input tape. -/
theorem input_bound {n m : ℕ} (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ)
    (hx : ∀ i,x i ≤ m) (ha : ∀ i,a i ≤ m) (hc : c ≤ m) (hB : ∀ i j, |B i j| ≤ (m:ℤ)) :
    (encodeCosetUpdateInput m x B a c).length ≤ 100*(n+bitLen m+2)^3 := by
  have hrep := rep_bound x B hx hB
  have hm := count_bound m m le_rfl
  have hn := count_dim n
  have hcw := count_bound m c hc
  have hw : (encodeNatListBin (List.ofFn a)).length ≤ 1+n*(2*(bitLen m+1)+2) := by
    refine (list_bound countWord (List.ofFn a) (bitLen m+1) ?_).trans_eq ?_
    · intro z hz; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact count_bound _ _ (ha i)
    · simp
  unfold encodeCosetUpdateInput; rw [list_length]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,id_eq]
  nlinarith only [hrep,hm,hn,hcw,hw,Nat.zero_le (n^3),Nat.zero_le ((bitLen m)^3),
    Nat.zero_le (n^2*bitLen m),Nat.zero_le (n*(bitLen m)^2),Nat.zero_le (n*bitLen m),
    Nat.zero_le (n^2),Nat.zero_le ((bitLen m)^2),Nat.zero_le n,Nat.zero_le (bitLen m)]

end DetDLP.CosetTapeBounds


namespace DetDLP.BitTracePolynomial
open OAI.Algorithms.SubexponentialSAT

private theorem instr_grows {r s l : ℕ} (op : BitProgram.Instr r s l) (a : BitProgram.Cfg r s l) (i : Fin s) :
    ((BitProgram.execInstr op a).stacks i).length ≤ (a.stacks i).length+1 := by
  cases op <;> simp [BitProgram.execInstr,Function.update_apply] <;>
    split_ifs <;> simp_all <;> omega

theorem trace_grows {r s l : ℕ} {p : BitProgram.Program r s l} {a b : BitProgram.Cfg r s l}
    {k : ℕ} (h : BitProgram.Trace p k a b) (i : Fin s) :
    (b.stacks i).length ≤ (a.stacks i).length+k := by
  induction h with
  | refl => simp
  | @cons k a c b hs tr ih =>
    obtain ⟨lab,_,he⟩ := Option.map_eq_some_iff.mp hs
    subst c
    have := instr_grows (p.code lab) a i
    omega

theorem initial_grows {r s l : ℕ} {p : BitProgram.Program r s l} {b : BitProgram.Cfg r s l}
    {k : ℕ} {input : List Bool} (h : BitProgram.Trace p k (BitProgram.initial p input) b) (i : Fin s) :
    (b.stacks i).length ≤ input.length+k := by
  apply (trace_grows h i).trans
  simp [BitProgram.initial]; split_ifs <;> simp

theorem absorb_cost (s k u t I : ℕ) (hu : 1 ≤ u)
    (ht : t ≤ (u+2)^k) (hI : I ≤ 100*(u+2)^3) :
    let K := (s+1)*(2*k+300)
    7*t ≤ K*(u+1)^K ∧ s*(I+t+I+15) ≤ K*(u+1)^K := by
  intro K
  have hk : 2*k ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s]
  have hc : 6 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  have hb : u+2 ≤ (u+1)^2 := by nlinarith only [hu,Nat.zero_le (u^2)]
  have comp (j : ℕ) (hj : 2*j ≤ K) : (u+2)^j ≤ (u+1)^K := by
    calc
      _ ≤ ((u+1)^2)^j := Nat.pow_le_pow_left hb _
      _ = (u+1)^(2*j) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hj
  let X := (u+1)^K
  have hT : t ≤ X := ht.trans (comp k hk)
  have hIn : I ≤ 100*X := hI.trans (Nat.mul_le_mul_left _ (comp 3 hc))
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hk7 : 7 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  have hsc : s*216 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  refine ⟨Nat.mul_le_mul hk7 hT,?_⟩
  calc
    s*(I+t+I+15) ≤ s*(216*X) := Nat.mul_le_mul_left _ (by omega)
    _ = (s*216)*X := by ring
    _ ≤ K*X := Nat.mul_le_mul_right _ hsc

end DetDLP.BitTracePolynomial

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (m N : ℕ) [NeZero m], 2 ≤ m → 1 ≤ N →
      ∀ (x : Fin N → ZMod m) (B : Matrix (Fin N) (Fin N) ℤ)
        (a : Fin N → ZMod m) (c : ZMod m), (∀ i j, |B i j| ≤ (m:ℤ)) →
      (∀ v : Fin N → ℤ, (fun i => (m:ℤ)*v i) ∈ latticeSpan B) →
      let f := fun y : Fin N → ℤ => ∑ i, ((a i).val : ℤ)*y i
      let r : ℤ := (c - ∑ i, a i*x i).val
      ∃ (d : ℤ) (u : Fin N → ℤ) (D : Matrix (Fin N) (Fin N) ℤ),
        0 < d ∧ IsColumnHNF D ∧
        (∀ (z : ℤ) (y : Fin N → ℤ),
          (∃ (q : ℤ) (t : Fin N → ℤ), z = (m : ℤ)*q + f y ∧ y = B.mulVec t) ↔
          (∃ (s : ℤ) (v : Fin N → ℤ), z = d*s ∧ y = fun i => s*u i + D.mulVec v i)) ∧
        RunsWithin M out
          (encodeCosetUpdateInput m (fun i => (x i).val) B (fun i => (a i).val) c.val)
          (encodeCosetRep (fun i => (x i+(((r/d)*u i : ℤ) : ZMod m)).val) D)
          (polyBound K (N + bitLen m)) (polyBound K (N + bitLen m)) := by
  obtain ⟨r,s,l,p,out,k,hp⟩ := bordered_update_bit_program
  let K := (s+1)*(2*k+300)
  refine ⟨GuardedCompiler.primitive p,out,K,?_⟩
  intro m n inst hm hn x B a c hb hgrid f rhs
  let input := encodeCosetUpdateInput m (fun i => (x i).val) B (fun i => (a i).val) c.val
  let res := BorderedHermite.update m (Vector.ofFn fun i => (x i).val)
    (Vector.ofFn fun j => Vector.ofFn fun i => B i j) (Vector.ofFn fun i => (a i).val) c.val
  let D : Matrix (Fin n) (Fin n) ℤ := fun i j => (res.2.get j).get i
  obtain ⟨d,u,hd,hhnf,hslice,hrep⟩ :=
    bordered_update_computed_correctly (by omega : 0 < m) x B a c hgrid
  obtain ⟨t,final,tr,hhalt,hword,hy,ht⟩ := hp m n hm hn _ _ B c.val
    (fun i => (x i).val_lt) (fun i => (a i).val_lt) c.val_lt hb
  change BitProgram.Trace p t (BitProgram.initial p input) final at tr
  change final.stacks out = encodeCosetRep res.1.get D at hword
  have bound (j : ℕ) (g : BitProgram.Cfg r s l) (hj : j ≤ t)
      (hg : BitProgram.Trace p j (BitProgram.initial p input) g) (i : Fin s) :
      (g.stacks i).length ≤ input.length+t :=
    (BitTracePolynomial.initial_grows hg i).trans (Nat.add_le_add_left hj _)
  obtain ⟨time,hTime,last,hTrace,hstop,hanswerTape,_,hspace⟩ :=
    CompileSpace.compile_word_answer_space p out tr hhalt hword hy bound
  have hsz := CosetTapeBounds.input_bound (m := m) (fun i => (x i).val) (fun i => (a i).val)
    B c.val (fun i => (x i).val_lt.le) (fun i => (a i).val_lt.le) c.val_lt.le hb
  change input.length ≤ 100*(n+bitLen m+2)^3 at hsz
  have hcost := BitTracePolynomial.absorb_cost s k (n+bitLen m) t input.length (by omega) ht hsz
  change 7*t ≤ K*((n+bitLen m)+1)^K ∧ s*(input.length+t+input.length+15) ≤ K*((n+bitLen m)+1)^K at hcost
  refine ⟨d,u,D,hd,hhnf,hslice,time,last,hTrace,⟨true,hstop⟩,?_,?_,?_⟩
  · have hre : res.1.get = (fun i => (x i+(((rhs/d)*u i : ℤ) : ZMod m)).val) := funext hrep
    rw [hre] at hanswerTape
    exact hanswerTape
  · unfold polyBound
    exact_mod_cast hTime.trans hcost.1
  · intro j g hj hg
    unfold polyBound
    exact_mod_cast (hspace j g hj hg).trans hcost.2
