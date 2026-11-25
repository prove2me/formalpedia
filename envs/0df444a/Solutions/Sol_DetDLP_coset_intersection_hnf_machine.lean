-- Prove2me | solution 1 for DetDLP.coset_intersection_hnf_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:19:51.000917+00:00
-- url     : https://prove2.me/submissions/8c31a4f0-72e3-41e0-b0e9-78e811edf357

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

import Theorems.Thm_DetDLP_bordered_column_hermite_machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

private theorem entry_bound {N m : ℕ} (hm : 0 < m) (B : Matrix (Fin N) (Fin N) ℤ)
    (hB : IsModularLatticeBasis m B) : ∀ i j, |B i j| ≤ m := by
  classical
  have hrow (i : Fin N) (t : Fin N → ℤ) (h : ∀ j < i, t j = 0) :
      B.mulVec t i = B i i * t i := by
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hl|hr
      · simp [h j hl]
      · simp [hB.1.1 i j hr]
    · simp
  have hdiag (i : Fin N) : B i i ≤ m := by
    obtain ⟨t,ht⟩ := hB.2.1 (Pi.single i 1)
    have zeros (j : Fin N) : j < i → t j = 0 := by
      induction j using WellFoundedLT.induction with
      | ind j ih =>
        intro hj
        have e := congrFun ht j
        change (m:ℤ)*(Pi.single i 1 : Fin N → ℤ) j = B.mulVec t j at e
        rw [hrow j t (fun k hk => ih k hk (hk.trans hj))] at e
        have hzero : (Pi.single i 1 : Fin N → ℤ) j = 0 := by simp [Pi.single_apply,hj.ne]
        rw [hzero,mul_zero] at e
        exact (mul_eq_zero.mp e.symm).resolve_left (hB.1.2.1 j).ne'
    have e := congrFun ht i
    change (m:ℤ)*(Pi.single i 1 : Fin N → ℤ) i = B.mulVec t i at e
    rw [hrow i t zeros] at e
    simp at e
    exact Int.le_of_dvd (by exact_mod_cast hm) ⟨t i,e⟩
  intro i j
  rcases lt_trichotomy i j with hl|he|hr
  · simp [hB.1.1 i j hl]
  · subst j
    rw [abs_of_pos (hB.1.2.1 i)]
    exact hdiag i
  · obtain ⟨hlo,hhi⟩ := hB.1.2.2 i j hr
    rw [abs_of_nonneg hlo]
    exact hhi.le.trans (hdiag i)

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
open DetDLP
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
          ∃ (x0' : Fin N → ZMod Mlab) (B' : Matrix (Fin N) (Fin N) ℤ),
            IsModularLatticeBasis Mlab B' ∧
            affineCoset Mlab x0' B' = A' ∧
            RunsWithin M out
              (encodeCosetUpdateInput Mlab (fun i => (x0 i).val) B (fun i => (a i).val) c0.val)
              (encodeCosetRep (fun i => (x0' i).val) B')
              (polyBound K (N + bitLen Mlab))
              (polyBound K (N + bitLen Mlab)) := by
  classical
  obtain ⟨M,out,K,H⟩ := bordered_column_hermite_machine
  refine ⟨M,out,K,?_⟩
  intro m N inst hm hN x B a c hB A A' hnon
  let f (y : Fin N → ℤ) := ∑ i, ((a i).val : ℤ)*y i
  let r : ℤ := (c - ∑ i, a i*x i).val
  obtain ⟨d,u,D,hd,hD,heq,hrun⟩ := H m N hm hN x B a c
    (entry_bound (by omega) B hB) hB.2.1
  let L (z : ℤ) (y : Fin N → ℤ) := ∃ (q : ℤ) (t : Fin N → ℤ), z = (m:ℤ)*q+f y ∧ y = B.mulVec t
  have mod_f (y : Fin N → ℤ) : ((f y : ℤ) : ZMod m) = ∑ i, a i*(y i : ZMod m) := by
    simp [f]
  have mod_r : (r : ZMod m) = c-∑ i,a i*x i := by simp [r]
  have fiber (y : Fin N → ℤ) : L r y ↔ y ∈ latticeSpan B ∧ (f y : ZMod m) = r := by
    constructor
    · rintro ⟨q,t,hz,hy⟩
      refine ⟨⟨t,hy⟩,?_⟩
      rw [hz]
      simp
    · rintro ⟨⟨t,hy⟩,hf⟩
      obtain ⟨q,hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp hf
      exact ⟨q,t,by linarith,hy⟩
  have mem_iff (v : Fin N → ZMod m) :
      v ∈ A' ↔ ∃ y : Fin N → ℤ, L r y ∧ ∀ i, v i = x i + (y i : ZMod m) := by
    constructor
    · rintro ⟨⟨t,ht⟩,hval⟩
      refine ⟨B.mulVec t,(fiber _).mpr ⟨⟨t,rfl⟩,?_⟩,ht⟩
      change ∑ i,a i*v i=c at hval
      simp_rw [ht,mul_add] at hval
      rw [Finset.sum_add_distrib] at hval
      rw [mod_f,mod_r]
      linear_combination hval
    · rintro ⟨y,hy,hv⟩
      obtain ⟨⟨t,ht⟩,hf⟩ := (fiber y).mp hy
      refine ⟨⟨t,ht ▸ hv⟩,?_⟩
      change ∑ i,a i*v i=c
      simp_rw [hv,mul_add]
      rw [Finset.sum_add_distrib,← mod_f, hf,mod_r]
      abel
  obtain ⟨x1,hx1⟩ := hnon
  obtain ⟨y,hy,_⟩ := (mem_iff _).mp hx1
  obtain ⟨s0,v0,hr0,_⟩ := (heq r y).mp hy
  have div_eq {s : ℤ} (hs : r = d*s) : r/d = s := by
    rw [hs,Int.mul_ediv_cancel_left _ hd.ne']
  have hr : r = d*(r/d) := by rw [div_eq hr0]; exact hr0
  have hcontain (v : Fin N → ℤ) : (fun i => (m:ℤ)*v i) ∈ latticeSpan D := by
    let y : Fin N → ℤ := fun i => (m:ℤ)*v i
    have hf : f y = (m:ℤ)*f v := by
      dsimp [f,y]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    obtain ⟨t,ht⟩ := hB.2.1 v
    have hy : L 0 y := ⟨-f v,t,by rw [hf]; ring,ht⟩
    obtain ⟨s,w,hs,hw⟩ := (heq 0 y).mp hy
    have hs0 : s = 0 := (mul_eq_zero.mp hs.symm).resolve_left hd.ne'
    exact ⟨w,by simpa [hs0] using hw⟩
  let x' (i : Fin N) := x i+(((r/d)*u i : ℤ) : ZMod m)
  refine ⟨x',D,⟨hD,hcontain,det_divides_of_span D hcontain⟩,?_,hrun⟩
  ext v
  rw [mem_iff]
  constructor
  · rintro ⟨w,hw⟩
    let y : Fin N → ℤ := fun i => (r/d)*u i+D.mulVec w i
    refine ⟨y,(heq r y).mpr ⟨r/d,w,hr,rfl⟩,?_⟩
    intro i
    simpa [x',y,add_assoc] using hw i
  · rintro ⟨y,hy,hv⟩
    obtain ⟨s,w,hs,hw⟩ := (heq r y).mp hy
    refine ⟨w,fun i => ?_⟩
    rw [hv i,hw]
    simp [x',div_eq hs,add_assoc]
