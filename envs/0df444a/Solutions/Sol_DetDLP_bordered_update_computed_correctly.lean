-- Prove2me | solution 1 for DetDLP.bordered_update_computed_correctly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:51:18.086488+00:00
-- url     : https://prove2.me/submissions/bf50e5d3-5b93-4c66-a38d-1f6d42bdaaa3

import Definitions.Def_DetDLP_BorderedHermite
import Theorems.Thm_DetDLP_column_elimination_certificate

namespace DetDLP.BorderedHermite
open Finset

private def lin {n : ℕ} (a : Fin n → ℤ) (y : Fin n → ℤ) := ∑ i, a i*y i

private theorem lin_mulVec {n : ℕ} (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) (t : Fin n → ℤ) :
    lin a (B.mulVec t) = ∑ j, lin a (B.col j)*t j := by
  simp [lin,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul,Matrix.col_apply,mul_assoc]
  exact Finset.sum_comm

private def block {n : ℕ} (p : ℤ) (f u : Fin n → ℤ) (D : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  Fin.cases (Fin.cases p f) (fun i => Fin.cases (u i) (D i))

private theorem block_action {n : ℕ} (p s : ℤ) (f u t : Fin n → ℤ) (D : Matrix (Fin n) (Fin n) ℤ) :
    (block p f u D).mulVec (Fin.cons s t) =
      Fin.cons (p*s+∑ j,f j*t j) (fun i => u i*s+D.mulVec t i) := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [block,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

private def gen {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : AddSubgroup (Fin n → ℤ) where
  carrier := latticeSpan B
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨t,rfl⟩ ⟨u,rfl⟩; exact ⟨t+u,(B.mulVec_add ..).symm⟩
  neg_mem' := by rintro _ ⟨t,rfl⟩; exact ⟨-t, (Matrix.mulVec_neg t B).symm⟩

private theorem col_mem {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : B.col j ∈ gen B :=
  ⟨Pi.single j 1,by rw [Matrix.mulVec_single_one]⟩

private theorem le_of_cols {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : AddSubgroup (Fin n → ℤ))
    (h : ∀ j, B.col j ∈ H) : gen B ≤ H := by
  rintro v ⟨t,rfl⟩
  have he : B.mulVec t = ∑ j, t j • B.col j := by
    ext i; simp [Matrix.mulVec,dotProduct,Finset.sum_apply,Matrix.col_apply,mul_comm]
  rw [he]; exact H.sum_mem (fun j _ => H.zsmul_mem (h j) _)

private def bcolumns {n : ℕ} (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) : Array (Column (n+1)) :=
  Array.ofFn fun j => Vector.ofFn (Fin.cons (lin a (B.col j)) (B.col j))

private def bmatrix {n : ℕ} (m : ℤ) (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) :=
  block m (fun j => lin a (B.col j)) 0 B

private theorem bcol_zero {n : ℕ} (m : ℤ) (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) :
    (bmatrix m a B).col 0 = Pi.single 0 m := by
  ext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp [bmatrix,block,Matrix.col_apply,Pi.single_apply]

private theorem bcol_succ {n : ℕ} (m : ℤ) (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    (bmatrix m a B).col j.succ = Fin.cons (lin a (B.col j)) (B.col j) := by
  ext i; refine Fin.cases ?_ (fun l => ?_) i <;> simp [bmatrix,block,Matrix.col_apply]

private theorem bmem {n : ℕ} (m : ℤ) (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (z : ℤ) (y : Fin n → ℤ) :
    Fin.cons z y ∈ gen (bmatrix m a B) ↔
      ∃ (q : ℤ) (t : Fin n → ℤ), z = m*q+lin a y ∧ y = B.mulVec t := by
  constructor
  · rintro ⟨x,hx⟩
    have he : Fin.cons (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
    rw [← he] at hx
    dsimp only [bmatrix] at hx
    rw [block_action] at hx
    have hy : y = B.mulVec (Fin.tail x) := by
      funext i; simpa using congrFun hx i.succ
    refine ⟨x 0,Fin.tail x,?_,hy⟩
    rw [hy,lin_mulVec]; simpa using congrFun hx 0
  · rintro ⟨q,t,hz,rfl⟩
    refine ⟨Fin.cons q t,?_⟩
    rw [bmatrix,block_action,hz,lin_mulVec]
    simp

private theorem bgrid {n : ℕ} {m : ℤ} (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hmB : ∀ v : Fin n → ℤ, (fun i => m*v i) ∈ latticeSpan B) (j : Fin (n+1)) :
    (Pi.single j m : Fin (n+1) → ℤ) ∈ gen (bmatrix m a B) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [← bcol_zero m a B]; exact col_mem _ _
  · have he : (Pi.single k.succ m : Fin (n+1) → ℤ) =
        Fin.cons 0 (fun i : Fin n => m*(Pi.single k 1 : Fin n → ℤ) i) := by
      ext i; refine Fin.cases ?_ (fun z => ?_) i <;> simp [Pi.single_apply,mul_ite]
    rw [he,bmem]
    obtain ⟨t,ht⟩ := hmB (Pi.single k 1)
    refine ⟨-a k,t,?_,ht⟩
    simp [lin,Pi.single_apply,mul_ite]; ring

private theorem bspan_eq {n : ℕ} {m : ℤ} (hm : 0 < m) (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hmB : ∀ v : Fin n → ℤ, (fun i => m*v i) ∈ latticeSpan B) :
    let cols := bcolumns a B
    let out := normalForm m cols
    gen (asMatrix out) = gen (bmatrix m a B) := by
  intro cols out
  obtain ⟨hs,_,hc⟩ := column_elimination_certificate hm cols
  change out.size = n+1 at hs
  have omem (H : AddSubgroup (Fin (n+1) → ℤ)) :
      (∀ c ∈ out,c.get ∈ H) ↔ ∀ j : Fin (n+1), (asMatrix out).col j ∈ H := by
    constructor
    · intro h j
      have hj : j.val < out.size := by rw [hs]; exact j.isLt
      have he : (asMatrix out).col j = (out[j.val]'hj).get := by ext; simp [asMatrix,Matrix.col_apply,hj]
      rw [he]; exact h _ (Array.getElem_mem ..)
    · intro h c hmem
      obtain ⟨k,hk,rfl⟩ := Array.mem_iff_getElem.mp hmem
      let j : Fin (n+1) := ⟨k,hs ▸ hk⟩
      have he : (asMatrix out).col j = (out[k]'hk).get := by ext; simp [asMatrix,Matrix.col_apply,j,hk]
      rw [← he]; exact h j
  have imem (H : AddSubgroup (Fin (n+1) → ℤ)) :
      (∀ c ∈ cols,c.get ∈ H) ↔ ∀ j : Fin n, (bmatrix m a B).col j.succ ∈ H := by
    have he (g : Fin (n+1) → ℤ) : (Vector.ofFn g).get = g := by funext i; simp
    simp [cols,bcolumns,Array.mem_ofFn,bcol_succ,he]
  apply le_antisymm
  · apply le_of_cols
    apply (omem _).mp
    exact (hc _).mpr ⟨(imem _).mpr (fun j => col_mem _ _),bgrid a B hmB⟩
  · apply le_of_cols
    obtain ⟨ht,hg⟩ := (hc _).mp ((omem _).mpr (fun j => col_mem _ j))
    exact Fin.cases (by rw [bcol_zero]; exact hg 0) ((imem _).mp ht)

private theorem output_slice {n : ℕ} {m : ℤ} (hm : 0 < m) (a : Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hmB : ∀ v : Fin n → ℤ, (fun i => m*v i) ∈ latticeSpan B) :
    let O := asMatrix (normalForm m (bcolumns a B))
    let D : Matrix (Fin n) (Fin n) ℤ := fun i j => O i.succ j.succ
    let u := fun i : Fin n => O i.succ 0
    0 < O 0 0 ∧ IsColumnHNF D ∧ ∀ z y,
        (∃ (q : ℤ) (t : Fin n → ℤ), z = m*q + lin a y ∧ y = B.mulVec t) ↔
          ∃ (s : ℤ) (v : Fin n → ℤ), z = O 0 0*s ∧ y = fun i => s*u i+D.mulVec v i := by
  intro O D u
  obtain ⟨_,hO,_⟩ := column_elimination_certificate hm (bcolumns a B)
  change IsColumnHNF O at hO
  have ho : O = block (O 0 0) 0 u D := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [block,u,D,hO.1 0 _ (Fin.succ_pos _)]
  refine ⟨hO.2.1 0,⟨fun i j h => hO.1 _ _ (Nat.succ_lt_succ h),fun i => hO.2.1 _,
    fun i j h => hO.2.2 _ _ (Nat.succ_lt_succ h)⟩,fun z y => ?_⟩
  rw [← bmem,← bspan_eq hm a B hmB]
  change Fin.cons z y ∈ gen O ↔ _
  constructor
  · rintro ⟨x,hx⟩
    rw [ho,← Fin.cons_self_tail x,block_action] at hx
    refine ⟨x 0,Fin.tail x,by simpa using congrFun hx 0,?_⟩
    ext i
    simpa [mul_comm] using congrFun hx i.succ
  · rintro ⟨s,v,rfl,rfl⟩
    refine ⟨Fin.cons s v,?_⟩
    change _ = O.mulVec _
    conv_rhs => rw [ho,block_action]
    simp [mul_comm]
private theorem fold_dot {n} (f : Fin n → ℤ) :
    (List.finRange n).foldl (fun s i => s+f i) 0 = ∑ i, f i := by
  have aux (l : List (Fin n)) (z : ℤ) : l.foldl (fun s i => s+f i) z = z + (l.map f).sum := by
    induction l generalizing z with
    | nil => simp
    | cons x l ih => simp [ih,add_assoc]
  rw [aux]; simp [Fin.sum_univ_def]

private theorem zval {m : ℕ} [NeZero m] (z : ℤ) : (z % m).toNat = (z : ZMod m).val := by
  exact congrArg Int.toNat (ZMod.val_intCast (n := m) z).symm |>.trans (Int.toNat_natCast _)

theorem update_certificate {m n : ℕ} [NeZero m] (hm : 0 < m) (x : Fin n → ZMod m)
    (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ZMod m) (c : ZMod m)
    (hmB : ∀ v : Fin n → ℤ, (fun i => (m:ℤ)*v i) ∈ latticeSpan B) :
    let res := update m (Vector.ofFn fun i => (x i).val)
      (Vector.ofFn fun j => Vector.ofFn fun i => B i j)
      (Vector.ofFn fun i => (a i).val) c.val
    let D : Matrix (Fin n) (Fin n) ℤ := fun i j => (res.2.get j).get i
    let r : ℤ := (c-∑ i,a i*x i).val
    ∃ (d : ℤ) (u : Fin n → ℤ), 0 < d ∧ IsColumnHNF D ∧
      (∀ (z : ℤ) (y : Fin n → ℤ),
        (∃ (q : ℤ) (t : Fin n → ℤ), z=(m:ℤ)*q+∑ i,((a i).val:ℤ)*y i ∧ y=B.mulVec t) ↔
          (∃ (s : ℤ) (v : Fin n → ℤ), z=d*s ∧ y=fun i => s*u i+D.mulVec v i)) ∧
      ∀ i, res.1.get i = (x i + (((r/d)*u i : ℤ) : ZMod m)).val := by
  intro res D r
  let A := fun i : Fin n => ((a i).val : ℤ)
  let C := bcolumns A B
  let O := asMatrix (normalForm (m:ℤ) C)
  let f (v : Column n) := (List.finRange n).foldl (fun s i => s+A i*v.get i) 0
  have ef (v : Column n) : f v = lin A v.get := fold_dot _
  have hcols : ((Vector.ofFn fun j => Vector.ofFn fun i => B i j).toArray.map fun col =>
      Vector.ofFn (Fin.cases (f col) fun i => col.get i)) = C := by
    unfold C bcolumns
    simp only [Vector.toArray_ofFn,Array.map_ofFn]
    congr 1; funext j
    dsimp only [Function.comp_apply]
    apply congrArg Vector.ofFn
    funext i
    refine Fin.cases ?_ (fun l => ?_) i <;> simp [ef,lin,Matrix.col_apply]
  have hu : res =
      (Vector.ofFn (fun i : Fin n => ((((x i).val:ℤ)+(r/O 0 0)*O i.succ 0)%(m:ℤ)).toNat),
       Vector.ofFn fun j : Fin n => Vector.ofFn fun i : Fin n => O i.succ j.succ) := by
    have hr : (((c.val:ℤ)-lin A (fun i => ((x i).val:ℤ))) % (m:ℤ)) = r := by
      rw [← ZMod.val_intCast]; simp [r,lin,A]
    let output (cols : Array (Column (n+1))) (z : ℤ) :=
      let T := asMatrix (normalForm (m:ℤ) cols)
      (Vector.ofFn (fun i : Fin n => ((((x i).val:ℤ)+(z/T 0 0)*T i.succ 0)%(m:ℤ)).toNat),
       Vector.ofFn fun j : Fin n => Vector.ofFn fun i : Fin n => T i.succ j.succ)
    let X := Vector.ofFn (fun i : Fin n => (x i).val)
    have hx (i : Fin n) : (X.map Int.ofNat).get i = (x i).val := by simp [X,Vector.map_ofFn]
    have hr' : (((c.val:ℤ) - f (X.map Int.ofNat)) % (m:ℤ)) = r := by
      simpa only [ef,lin,hx] using hr
    let rawcols := (Vector.ofFn fun j => Vector.ofFn fun i => B i j).toArray.map fun col =>
        Vector.ofFn (Fin.cases (f col) fun i => col.get i)
    simp only [res,update,get_ofFn]
    change output rawcols (((c.val:ℤ) - f (X.map Int.ofNat)) % (m:ℤ)) = output C r
    exact congrArg₂ output hcols hr'
  have hD : D = (fun i j => O i.succ j.succ) := by
    ext i j; simp [D,hu]
  obtain ⟨hp,hd,hs⟩ := output_slice (show 0 < (m:ℤ) by exact_mod_cast hm) A B hmB
  refine ⟨O 0 0,fun i => O i.succ 0,hp,hD ▸ hd,?_,?_⟩
  · rw [hD]; exact hs
  · intro i
    rw [hu]; simp [zval]
end DetDLP.BorderedHermite

open DetDLP DetDLP.BorderedHermite

theorem solution {m n : ℕ} [NeZero m] (hm : 0 < m) (x : Fin n → ZMod m)
    (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ZMod m) (c : ZMod m)
    (hmB : ∀ v : Fin n → ℤ, (fun i => (m:ℤ)*v i) ∈ latticeSpan B) :
    let res := update m (Vector.ofFn fun i => (x i).val)
      (Vector.ofFn fun j => Vector.ofFn fun i => B i j)
      (Vector.ofFn fun i => (a i).val) c.val
    let D : Matrix (Fin n) (Fin n) ℤ := fun i j => (res.2.get j).get i
    let r : ℤ := (c-∑ i,a i*x i).val
    ∃ (d : ℤ) (u : Fin n → ℤ), 0 < d ∧ IsColumnHNF D ∧
      (∀ (z : ℤ) (y : Fin n → ℤ),
        (∃ (q : ℤ) (t : Fin n → ℤ), z=(m:ℤ)*q+∑ i,((a i).val:ℤ)*y i ∧ y=B.mulVec t) ↔
          (∃ (s : ℤ) (v : Fin n → ℤ), z=d*s ∧ y=fun i => s*u i+D.mulVec v i)) ∧
      ∀ i, res.1.get i = (x i + (((r/d)*u i : ℤ) : ZMod m)).val := by
  exact update_certificate hm x B a c hmB
