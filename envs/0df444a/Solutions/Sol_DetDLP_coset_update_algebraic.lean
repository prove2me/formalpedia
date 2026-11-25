-- Prove2me | solution 1 for DetDLP.coset_update_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:25:04.123455+00:00
-- url     : https://prove2.me/submissions/2848a3b7-82b4-431a-bc59-79c887cd671b

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset
open DetDLP Finset

namespace DetDLP.Coset
variable {m N : ℕ} [NeZero m]

private def cols (B : Matrix (Fin N) (Fin N) ℤ) :
    (Fin N → ℤ) →+ (Fin N → ZMod m) where
  toFun t i := (B.mulVec t i : ℤ)
  map_zero' := by ext; simp
  map_add' s t := by ext; simp [Matrix.mulVec_add]

private def dot (a : Fin N → ZMod m) : (Fin N → ZMod m) →+ ZMod m where
  toFun v := ∑ i, a i * v i
  map_zero' := by simp
  map_add' s t := by simp [mul_add,Finset.sum_add_distrib]

private def coeff (a : Fin N → ZMod m) (B : Matrix (Fin N) (Fin N) ℤ) (j : Fin N) : ℤ :=
  ∑ i, ((a i).val : ℤ)*B i j

private theorem dot_cols (a : Fin N → ZMod m) (B : Matrix (Fin N) (Fin N) ℤ) (t : Fin N → ℤ) :
    dot a (cols B t) = ((∑ j, coeff a B j*t j : ℤ) : ZMod m) := by
  simp [dot,cols,coeff,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm

private theorem fold_dvd (s : Finset (Fin N)) (c : Fin N → ℤ) :
    let d := s.fold Nat.gcd m (fun j => (c j).natAbs)
    d ∣ m ∧ ∀ j ∈ s, d ∣ (c j).natAbs := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.fold_insert hj]
    dsimp only at ih ⊢
    refine ⟨(Nat.gcd_dvd_right ..).trans ih.1,?_⟩
    intro i hi
    rcases mem_insert.mp hi with rfl|hi
    · exact Nat.gcd_dvd_left .. 
    · exact (Nat.gcd_dvd_right ..).trans (ih.2 i hi)

private theorem fold_mem (S : AddSubgroup (ZMod m)) (s : Finset (Fin N)) (c : Fin N → ℤ)
    (hc : ∀ i, ((c i : ℤ) : ZMod m) ∈ S) :
    ((s.fold Nat.gcd m (fun i => (c i).natAbs) : ℕ) : ZMod m) ∈ S := by
  induction s using Finset.induction_on with
  | empty => simpa using S.zero_mem
  | insert i s hi ih =>
    rw [Finset.fold_insert hi]
    let d := s.fold Nat.gcd m (fun i => (c i).natAbs)
    let k := (c i).natAbs
    have hk : (k : ZMod m) ∈ S := by
      rcases h : c i with u|u
      · simpa [k,h] using hc i
      · simpa [k,h,Int.natAbs_negSucc] using S.neg_mem (hc i)
    have e := congrArg (fun z : ℤ => (z : ZMod m)) (Nat.gcd_eq_gcd_ab k d)
    push_cast at e
    change ((k.gcd d : ℕ) : ZMod m) ∈ S
    rw [e]
    simpa [zsmul_eq_mul,mul_comm] using S.add_mem (S.zsmul_mem hk (Nat.gcdA k d)) (S.zsmul_mem ih (Nat.gcdB k d))

private theorem range_dot_cols (a : Fin N → ZMod m) (B : Matrix (Fin N) (Fin N) ℤ) :
    let D := Finset.univ.fold Nat.gcd m (fun j => (coeff a B j).natAbs)
    ((dot a).comp (cols B)).range = AddSubgroup.zmultiples (D : ZMod m) := by
  intro D
  let f := (dot a).comp (cols B)
  have hd := (fold_dvd (m := m) univ (coeff a B)).2
  apply le_antisymm
  · rintro v ⟨t,rfl⟩
    change dot a (cols B t) ∈ _
    rw [dot_cols,Int.cast_sum]
    apply AddSubgroup.sum_mem
    intro j _
    have hc : (D : ℤ) ∣ coeff a B j := by
      exact_mod_cast (Int.natCast_dvd.mpr (hd j (mem_univ j)))
    obtain ⟨w,hw⟩ := hc
    refine ⟨w * t j,?_⟩
    simp [hw,zsmul_eq_mul]
    ring
  · apply AddSubgroup.zmultiples_le.mpr
    apply fold_mem
    intro j
    refine ⟨Pi.single j 1,?_⟩
    change dot a (cols B (Pi.single j 1)) = _
    rw [dot_cols]
    simp [Pi.single_apply,mul_ite]
end DetDLP.Coset

namespace DetDLP.Coset

theorem affine_fiber_count {V W : Type*} [AddCommGroup V] [Finite V] [AddCommGroup W]
    (H : AddSubgroup V) (A : Set V) (x0 : V) (L : V →+ W) (c : W)
    (hA : ∀ x, x ∈ A ↔ x-x0 ∈ H) (hF : ({x ∈ A | L x = c} : Set V).Nonempty) :
    Nat.card {x ∈ A | L x = c} * Nat.card (L.comp H.subtype).range = Nat.card A := by
  classical
  let e : H ≃ A := {
    toFun v := ⟨(v : V)+x0, (hA _).mpr (by simpa using v.property)⟩
    invFun v := ⟨(v : V)-x0,(hA _).mp v.property⟩
    left_inv v := Subtype.ext (by simp)
    right_inv v := Subtype.ext (by simp) }
  let l := L.comp H.subtype
  let d := c-L x0
  let f : (l ⁻¹' ({d} : Set W)) ≃ {x ∈ A | L x = c} := {
    toFun z := ⟨((e z.val : A) : V), (e z.val).property, by
      have hz : l z.val = d := z.property
      change L ((z.val : V)+x0) = c
      rw [map_add]
      exact (eq_sub_iff_add_eq.mp hz)⟩
    invFun z := ⟨e.symm ⟨z.val,z.property.1⟩, by
      change L ((z.val : V)-x0) = c-L x0
      rw [map_sub,z.property.2]⟩
    left_inv z := by apply Subtype.ext; exact e.symm_apply_apply z.val
    right_inv z := by
      apply Subtype.ext
      change ((z.val : V)-x0) + x0 = z.val
      simp }
  obtain ⟨z,hz⟩ := hF
  let t := f.symm ⟨z,hz⟩
  have ht : l t.val = d := t.property
  have hk : Nat.card (l ⁻¹' ({d} : Set W)) = Nat.card l.ker := by
    rw [← ht]; exact Nat.card_congr (l.fiberEquivKer t.val)
  rw [← Nat.card_congr f, hk, ← Nat.card_congr e]
  change Nat.card l.ker * Nat.card l.range = Nat.card H
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
end DetDLP.Coset

namespace DetDLP.Coset
open Finset

theorem cardinal_halving {m N : ℕ} [NeZero m] (hm : 2 ≤ m) (x0 : Fin N → ZMod m)
    (B : Matrix (Fin N) (Fin N) ℤ) (a : Fin N → ZMod m) (c : ZMod m) :
    let A := affineCoset m x0 B
    let A' := {x ∈ A | ∑ i, a i*x i = c}
    A'.Nonempty →
    let d := univ.fold Nat.gcd m (fun j => (coeff a B j).natAbs)
    Nat.card A' * m = Nat.card A * d ∧
      ((∑ i, a i*x0 i) ≠ c → d < m ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  intro A A' hnon d
  let F := cols (m := m) B
  let H := F.range
  let L := dot a
  have hmem (x : Fin N → ZMod m) : x ∈ A ↔ x-x0 ∈ H := by
    constructor
    · rintro ⟨t,ht⟩
      refine ⟨t,?_⟩
      ext i
      change ((B.mulVec t i : ℤ) : ZMod m) = x i - x0 i
      rw [ht i]; abel
    · rintro ⟨t,ht⟩
      exact ⟨t,fun i => by
        have e := congrFun ht i
        change ((B.mulVec t i : ℤ) : ZMod m) = x i - x0 i at e
        rw [e]; abel⟩
  have hidx := affine_fiber_count H A x0 L c hmem hnon
  have hrange : (L.comp H.subtype).range = (L.comp F).range := by
    rw [AddMonoidHom.range_comp, AddSubgroup.range_subtype, AddMonoidHom.range_comp]
  rw [hrange,range_dot_cols] at hidx
  have hdvd : d ∣ m := (fold_dvd (m := m) univ (coeff a B)).1
  have hcard : Nat.card (AddSubgroup.zmultiples (d : ZMod m)) = m/d := by
    rw [Nat.card_zmultiples,ZMod.addOrderOf_coe d (NeZero.ne _), Nat.gcd_eq_right hdvd]
  change Nat.card A' * Nat.card (AddSubgroup.zmultiples (d : ZMod m)) = Nat.card A at hidx
  rw [hcard] at hidx
  constructor
  · rw [← hidx,Nat.mul_assoc,Nat.div_mul_cancel hdvd]
  · intro hbad
    have hx0 : x0 ∈ A := (hmem x0).mpr (by simpa using H.zero_mem)
    have hproper : A' ⊂ A := by
      refine ⟨(fun x hx => hx.1),fun h => hbad ((h hx0).2)⟩
    have hlt : Nat.card A' < Nat.card A := Set.ncard_lt_ncard hproper
    have hquot : 2 ≤ m/d := by
      by_contra! hyp
      have hle : Nat.card A' * (m/d) ≤ Nat.card A' * 1 := Nat.mul_le_mul_left _ (by omega)
      omega
    refine ⟨?_,?_⟩
    · have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      by_contra! hyp
      have he : m = d := by omega
      rw [← he,Nat.div_self (by omega)] at hquot
      omega
    · rw [← hidx,Nat.mul_comm 2]
      exact Nat.mul_le_mul_left _ hquot
end DetDLP.Coset


namespace DetDLP.Hermite

private theorem reduce_rows {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ)
    (htri : ∀ i j, i < j → B i j = 0) (hpos : ∀ i, 0 < B i i)
    (v : Fin N → ℤ) (s : ℕ) :
    ∃ t : Fin N → ℤ, (∀ i : Fin N, i.val < s → B.mulVec t i = 0) ∧
      ∀ i : Fin N, s ≤ i.val → 0 ≤ v i - B.mulVec t i ∧ v i - B.mulVec t i < B i i := by
  classical
  have H (k : ℕ) : ∃ t : Fin N → ℤ, (∀ i : Fin N, i.val < s → B.mulVec t i = 0) ∧
      ∀ i : Fin N, s ≤ i.val → i.val < k →
        0 ≤ v i - B.mulVec t i ∧ v i - B.mulVec t i < B i i := by
    induction k with
    | zero => exact ⟨0,by simp,by simp⟩
    | succ k ih =>
      obtain ⟨t,ht,hrt⟩ := ih
      by_cases h : s ≤ k ∧ k < N
      · let j : Fin N := ⟨k,h.2⟩
        let q := (v j - B.mulVec t j) / B j j
        let t' := t + Pi.single j q
        have addrow (i : Fin N) : B.mulVec t' i = B.mulVec t i + B i j*q := by
          rw [show t' = t + Pi.single j q from rfl,Matrix.mulVec_add]
          simp [Matrix.mulVec_single, Matrix.col_apply,mul_comm]
        have past (i : Fin N) (hi : i.val < k) : B.mulVec t' i = B.mulVec t i := by
          rw [addrow,htri i j hi,zero_mul,add_zero]
        refine ⟨t',fun i hi => (past i (lt_of_lt_of_le hi h.1)).trans (ht i hi),?_⟩
        intro i hs hi
        by_cases he : i.val = k
        · have heq : i = j := Fin.ext he
          subst i
          rw [addrow]
          have hm : v j - (B.mulVec t j + B j j*q) = (v j - B.mulVec t j) % B j j := by
            rw [Int.emod_def]; dsimp [q]; ring
          rw [hm]
          exact ⟨Int.emod_nonneg _ (hpos j).ne',Int.emod_lt_of_pos _ (hpos j)⟩
        · have hk : i.val < k := by omega
          rw [past i hk]; exact hrt i hs hk
      · refine ⟨t,ht,fun i hs hi => hrt i hs ?_⟩
        have := i.isLt
        omega
  obtain ⟨t,ht,hr⟩ := H N
  exact ⟨t,ht,fun i hs => hr i hs i.isLt⟩

private theorem mulVec_mem {N : ℕ} (L : AddSubgroup (Fin N → ℤ))
    (B : Matrix (Fin N) (Fin N) ℤ) (h : ∀ j, (fun i => B i j) ∈ L)
    (t : Fin N → ℤ) : B.mulVec t ∈ L := by
  have he : B.mulVec t = ∑ j, t j • (fun i => B i j) := by
    ext i
    simp [Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]
  rw [he]
  exact L.sum_mem fun j _ => L.zsmul_mem (h j) (t j)

private theorem basis {N m : ℕ} (hm : 0 < m) (L : AddSubgroup (Fin N → ℤ))
    (hL : ∀ v : Fin N → ℤ, (fun i => (m : ℤ)*v i) ∈ L) :
    ∃ B : Matrix (Fin N) (Fin N) ℤ, IsColumnHNF B ∧ latticeSpan B = (L : Set (Fin N → ℤ)) := by
  classical
  let P (i : Fin N) (n : ℕ) := 0 < n ∧ ∃ v ∈ L, (∀ j < i, v j = 0) ∧ v i = (n : ℤ)
  have hex (i : Fin N) : ∃ n, P i n := by
    refine ⟨m,hm,_,hL (Pi.single i 1),?_,?_⟩
    · intro j hj; simp [Pi.single_apply,hj.ne]
    · simp
  let d (i : Fin N) := Nat.find (hex i)
  have spec (i : Fin N) : P i (d i) := Nat.find_spec _
  choose w hw hz hp using fun i => (spec i).2
  let B₀ : Matrix (Fin N) (Fin N) ℤ := fun i j => w j i
  have hbtri : ∀ i j, i < j → B₀ i j = 0 := fun i j hij => hz j i hij
  have hbpos (i : Fin N) : 0 < B₀ i i := by
    change 0 < w i i
    rw [hp]; exact_mod_cast (spec i).1
  choose t hpre hred using fun j : Fin N => reduce_rows B₀ hbtri hbpos (w j) (j.val+1)
  let B : Matrix (Fin N) (Fin N) ℤ := fun i j => w j i - B₀.mulVec (t j) i
  have same (i j : Fin N) (h : i ≤ j) : B i j = w j i := by
    dsimp [B]; rw [hpre j i (Nat.lt_succ_of_le h),sub_zero]
  have diag (i : Fin N) : B i i = (d i : ℤ) := (same i i le_rfl).trans (hp i)
  have cols (j : Fin N) : (fun i => B i j) ∈ L :=
    L.sub_mem (hw j) (mulVec_mem L B₀ hw (t j))
  have hH : IsColumnHNF B := by
    refine ⟨fun i j h => (same i j h.le).trans (hz j i h),fun i => ?_,?_⟩
    · rw [diag]; exact_mod_cast (spec i).1
    · intro i j hij
      have hh := hred j i (show j.val + 1 ≤ i.val from hij)
      change 0 ≤ B i j ∧ B i j < w i i at hh
      simpa only [same i i le_rfl] using hh
  refine ⟨B,hH,Set.ext fun v => ⟨?_,?_⟩⟩
  · rintro ⟨a,rfl⟩; exact mulVec_mem L B cols a
  · intro hv
    obtain ⟨a,_,ha⟩ := reduce_rows B hH.1 hH.2.1 v 0
    let z := v-B.mulVec a
    have hzm : z ∈ L := L.sub_mem hv (mulVec_mem L B cols a)
    have zero (i : Fin N) : z i = 0 := by
      induction i using WellFoundedLT.induction with
      | ind i ih =>
        have hb := ha i (Nat.zero_le _)
        change 0 ≤ z i ∧ z i < B i i at hb
        rw [diag] at hb
        by_contra e
        have hp' : P i (z i).toNat := ⟨by omega,z,hzm,ih,by omega⟩
        have hl : d i ≤ (z i).toNat := Nat.find_min' (hex i) hp'
        omega
    exact ⟨a,funext fun i => sub_eq_zero.mp (zero i)⟩

end DetDLP.Hermite

namespace DetDLP
private theorem det_divides_of_span {m N : ℕ} (D : Matrix (Fin N) (Fin N) ℤ)
    (h : ∀ v : Fin N → ℤ, (fun i => (m:ℤ)*v i) ∈ latticeSpan D) :
    D.det ∣ (m:ℤ)^N := by
  classical
  have hv (j : Fin N) := h (Pi.single j 1)
  choose w hw using hv
  let W : Matrix (Fin N) (Fin N) ℤ := fun i j => w j i
  have hprod : D * W = (m:ℤ) • (1 : Matrix (Fin N) (Fin N) ℤ) := by
    ext i j
    change D.mulVec (w j) i = _
    rw [← hw j]
    simp [Pi.single_apply,Matrix.one_apply,eq_comm]
  have hh := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hh
  exact ⟨W.det,hh.symm⟩

end DetDLP

namespace DetDLP.Coset

private def intMat {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : (Fin N → ℤ) →+ (Fin N → ℤ) where
  toFun := B.mulVec
  map_zero' := by simp
  map_add' := Matrix.mulVec_add B

private def castVec (m N : ℕ) : (Fin N → ℤ) →+ (Fin N → ZMod m) where
  toFun y i := y i
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

private theorem affine_mem {m N : ℕ} [NeZero m] (B : Matrix (Fin N) (Fin N) ℤ)
    (x o : Fin N → ZMod m) : x ∈ affineCoset m o B ↔
      ∃ t : Fin N → ℤ, x = o + castVec m N (intMat B t) :=
  ⟨fun ⟨t,ht⟩ => ⟨t,funext ht⟩,fun ⟨t,ht⟩ => ⟨t,congrFun ht⟩⟩

private theorem basis_fiber {m N : ℕ} [NeZero m] (hm : 0 < m)
    (x0 : Fin N → ZMod m) (B : Matrix (Fin N) (Fin N) ℤ)
    (a : Fin N → ZMod m) (c : ZMod m) (hB : IsModularLatticeBasis m B)
    (hnon : ({x ∈ affineCoset m x0 B | dot a x = c} : Set (Fin N → ZMod m)).Nonempty) :
    ∃ x1 D, IsModularLatticeBasis m D ∧
      affineCoset m x1 D = {x ∈ affineCoset m x0 B | dot a x = c} := by
  classical
  let cv := castVec m N
  let F := intMat B
  let H := F.range ⊓ ((dot a).comp cv).ker
  have grid (v : Fin N → ℤ) : (fun i => (m:ℤ)*v i) ∈ H := by
    obtain ⟨t,ht⟩ := hB.2.1 v
    refine ⟨⟨t,ht.symm⟩,?_⟩
    have he : cv (fun i => (m:ℤ)*v i) = 0 := by ext; simp [cv,castVec]
    change dot a (cv _) = 0
    rw [he,map_zero]
  obtain ⟨D,hD,hspan⟩ := Hermite.basis hm H grid
  have hDi (v : Fin N → ℤ) : (fun i => (m:ℤ)*v i) ∈ latticeSpan D := by
    rw [hspan]; exact grid v
  obtain ⟨x1,hx,h1⟩ := hnon
  obtain ⟨t1,ht1⟩ := (affine_mem B x1 x0).mp hx
  refine ⟨x1,D,⟨hD,hDi,det_divides_of_span D hDi⟩,?_⟩
  ext x
  rw [affine_mem]
  change (∃ t, x = x1+cv (intMat D t)) ↔ x ∈ affineCoset m x0 B ∧ dot a x = c
  rw [affine_mem]
  constructor
  · rintro ⟨t,ht⟩
    let y := intMat D t
    have hy : y ∈ H := by
      change y ∈ (H : Set _)
      rw [← hspan]; exact ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := hy.1
    have he : x = x1+cv y := ht
    refine ⟨⟨t1+s,?_⟩,?_⟩
    · change x = x0+cv (F (t1+s))
      rw [he,ht1,map_add,map_add,hs]; abel
    · change dot a x = c
      have hz : dot a (cv y) = 0 := hy.2
      rw [he,map_add,hz,add_zero]; exact h1
  · rintro ⟨⟨t,ht⟩,hc⟩
    let y := F (t-t1)
    have he : x = x1+cv y := by
      rw [ht,ht1]
      dsimp only [y]
      rw [map_sub,map_sub]
      abel
    have hy : y ∈ H := by
      refine ⟨⟨t-t1,rfl⟩,?_⟩
      change dot a (cv y) = 0
      rw [he,map_add,h1] at hc
      exact add_eq_left.mp hc
    have hy' : y ∈ latticeSpan D := by rw [hspan]; exact hy
    obtain ⟨q,hq⟩ := hy'
    refine ⟨q,?_⟩
    change x = x1 + cv (D.mulVec q)
    rw [← hq]; exact he
end DetDLP.Coset

theorem solution :
    ∀ (Mlab N : ℕ) [NeZero Mlab], 2 ≤ Mlab → 1 ≤ N →
        ∀ (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ)
          (a : Fin N → ZMod Mlab) (c0 : ZMod Mlab),
          IsModularLatticeBasis Mlab B →
          let A := affineCoset Mlab x0 B
          let A' := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
          A'.Nonempty →
          let gstar : ℕ :=
            Finset.univ.fold Nat.gcd Mlab
              (fun j : Fin N => Int.natAbs (∑ i : Fin N, ((a i).val : ℤ) * B i j))
          ∃ (x0' : Fin N → ZMod Mlab) (B' : Matrix (Fin N) (Fin N) ℤ),
            IsModularLatticeBasis Mlab B' ∧
            affineCoset Mlab x0' B' = A' ∧
            Nat.card A' * Mlab = Nat.card A * gstar ∧
            ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  intro m N inst hm hN x B a c hB A A' hnon d
  obtain ⟨x1,D,hD,hF⟩ := Coset.basis_fiber (by omega) x B a c hB hnon
  obtain ⟨hcard,hhalf⟩ := Coset.cardinal_halving hm x B a c hnon
  exact ⟨x1,D,hD,hF,hcard,hhalf⟩
