-- Prove2me | solution 1 for DetDLP.lemma_4_4_coset_update_halving
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:35:19.456879+00:00
-- url     : https://prove2.me/submissions/a2dbd0d8-1774-44c9-b024-73a9e33018c4

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset
import Theorems.Thm_DetDLP_coset_intersection_hnf_machine
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

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
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
            RunsWithin M out
              (encodeCosetUpdateInput Mlab (fun i => (x0 i).val) B (fun i => (a i).val) c0.val)
              (encodeCosetRep (fun i => (x0' i).val) B')
              (polyBound K (N + bitLen Mlab))
              (polyBound K (N + bitLen Mlab)) ∧
            ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  obtain ⟨M, out, K, run⟩ := DetDLP.coset_intersection_hnf_machine
  refine ⟨M, out, K, ?_⟩
  intro m N hNe hm hN x0 B a c hB A A' hnon d
  obtain ⟨x1, B1, hb1, hset, hrun⟩ := run m N hm hN x0 B a c hB hnon
  obtain ⟨hcard, hhalf⟩ := DetDLP.Coset.cardinal_halving hm x0 B a c hnon
  exact ⟨x1,B1,hb1,hset,hcard,hrun,hhalf⟩
