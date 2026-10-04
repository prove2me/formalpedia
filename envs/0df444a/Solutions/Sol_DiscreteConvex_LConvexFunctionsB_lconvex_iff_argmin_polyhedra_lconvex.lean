-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lconvex_iff_argmin_polyhedra_lconvex
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T16:59:57.559335+00:00
-- url     : https://prove2.me/submissions/d0e0bf4f-4df6-490f-b859-31f310c5fb6f

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.OfMap
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBFNat
import Definitions.Def_DiscreteConvex_LConvexFunctions_DiscreteMidpointConvexity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega
import Definitions.Def_DiscreteConvex_LConvexFunctions_LiftedFunctionL
import Mathlib.Data.Fintype.Option
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Set.Finite.Lemmas

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section

open Finset
open scoped BigOperators

namespace FiniteFarkas

lemma interval_feasible {I J : Type*} [Fintype I] [Fintype J]
    (l : I → ℝ) (u : J → ℝ) (h : ∀ i j, l i ≤ u j) :
    ∃ t : ℝ, (∀ i, l i ≤ t) ∧ (∀ j, t ≤ u j) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let := hI
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      exact ⟨0,fun i => isEmptyElim i,fun j => isEmptyElim j⟩
    | inr hJ =>
      let := hJ
      refine ⟨Finset.univ.inf' Finset.univ_nonempty u,fun i => isEmptyElim i,?_⟩
      intro j
      exact Finset.inf'_le u (Finset.mem_univ j)
  | inr hI =>
    let := hI
    refine ⟨Finset.univ.sup' Finset.univ_nonempty l,?_,?_⟩
    · intro i; exact Finset.le_sup' l (Finset.mem_univ i)
    · intro j; exact Finset.sup'_le Finset.univ_nonempty l (fun i _ => h i j)

lemma combination_comp {I J : Type*} [Fintype I] [Fintype J]
    (r : J → I → ℝ) (mu : J → ℝ) (f : I → ℝ) :
    (∑ i, (∑ j, mu j*r j i)*f i) = ∑ j, mu j*(∑ i, r j i*f i) := by
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

abbrev ElimRows {I : Type*} (a : I → ℝ) := {i : I // a i=0} ⊕
  ({i : I // 0<a i} × {i : I // a i<0})

noncomputable def rowWeights {I : Type*} [DecidableEq I] (a : I → ℝ) : ElimRows a → I → ℝ
  | .inl i, k => if k=i.1 then 1 else 0
  | .inr ij, k => (if k=ij.1.1 then (a ij.1.1)⁻¹ else 0) +
      (if k=ij.2.1 then -(a ij.2.1)⁻¹ else 0)

lemma rowWeights_nonneg {I : Type*} [DecidableEq I] (a : I → ℝ)
    (j : ElimRows a) (i : I) : 0 ≤ rowWeights a j i := by
  cases j with
  | inl j => simp only [rowWeights]; split <;> norm_num
  | inr j =>
    apply add_nonneg
    · split <;> simp_all [le_of_lt j.1.2]
    · split <;> simp_all [le_of_lt j.2.2]

lemma rowWeights_sum {I : Type*} [Fintype I] [DecidableEq I] (a f : I → ℝ)
    (j : ElimRows a) : (∑ i, rowWeights a j i*f i) =
    match j with
    | .inl k => f k.1
    | .inr kl => f kl.1.1/a kl.1.1 - f kl.2.1/a kl.2.1 := by
  cases j with
  | inl j => simp [rowWeights]
  | inr j =>
    simp only [rowWeights,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
    simp [div_eq_mul_inv,mul_comm,sub_eq_add_neg]

lemma rowWeights_annihilate {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℝ)
    (j : ElimRows a) : ∑ i, rowWeights a j i*a i=0 := by
  rw [rowWeights_sum]
  cases j with
  | inl j => exact j.2
  | inr j => simp [ne_of_gt j.1.2,ne_of_lt j.2.2]

lemma dot_combination {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℝ) (a : I → J → ℝ) (x : J → ℝ) :
    (∑ j, (∑ i, r i*a i j)*x j) = ∑ i, r i*(∑ j, a i j*x j) := by
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Finite Farkas feasibility, proved by Fourier–Motzkin elimination. -/
theorem feasible (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℝ) (b : I → ℝ)
    (hcert : ∀ w : I → ℝ, (∀ i, 0 ≤ w i) →
      (∀ k, ∑ i, w i*a i k=0) → ∑ i, w i*b i ≤ 0) :
    ∃ x : Fin n → ℝ, ∀ i, b i ≤ ∑ k, a i k*x k := by
  classical
  induction n generalizing I with
  | zero =>
    refine ⟨fun k => Fin.elim0 k,?_⟩
    intro i
    have hh := hcert (fun j => if j=i then 1 else 0)
      (by intro j; split <;> norm_num) (fun k => Fin.elim0 k)
    simpa using hh
  | succ n ih =>
    let a0 : I → ℝ := fun i => a i 0
    let J := ElimRows a0
    let : Fintype J := by dsimp [J, ElimRows]; infer_instance
    let r : J → I → ℝ := rowWeights a0
    let A : J → Fin n → ℝ := fun j k => ∑ i, r j i*a i k.succ
    let B : J → ℝ := fun j => ∑ i, r j i*b i
    have hr (j : J) (i : I) : 0 ≤ r j i := rowWeights_nonneg a0 j i
    have hA0 (j : J) : ∑ i, r j i*a i 0=0 := rowWeights_annihilate a0 j
    have hcert' : ∀ mu : J → ℝ, (∀ j, 0 ≤ mu j) →
        (∀ k, ∑ j, mu j*A j k=0) → ∑ j, mu j*B j ≤ 0 := by
      intro mu hmu hzero
      have hh := hcert (fun i => ∑ j, mu j*r j i)
        (fun i => Finset.sum_nonneg (fun j _ => mul_nonneg (hmu j) (hr j i))) ?_
      · simpa only [combination_comp,B] using hh
      · intro k
        rw [combination_comp]
        cases k using Fin.cases with
        | zero => simp only [hA0,mul_zero,Finset.sum_const_zero]
        | succ k => exact hzero k
    obtain ⟨x,hx⟩ := ih A B hcert'
    let R : I → ℝ := fun i => b i-∑ k, a i k.succ*x k
    have hR (j : J) : ∑ i, r j i*R i ≤ 0 := by
      have hh := hx j
      change (∑ i, r j i*b i) ≤ ∑ k, (∑ i, r j i*a i k.succ)*x k at hh
      rw [dot_combination] at hh
      simpa only [R,mul_sub,Finset.sum_sub_distrib,sub_nonpos] using hh
    have hpair (p : {i : I // 0<a0 i}) (q : {i : I // a0 i<0}) :
        R p.1/a0 p.1 ≤ R q.1/a0 q.1 := by
      have hh := hR (Sum.inr (p,q))
      rw [show r = rowWeights a0 from rfl, rowWeights_sum] at hh
      exact sub_nonpos.mp hh
    obtain ⟨t,htp,htn⟩ := interval_feasible
      (fun p : {i : I // 0<a0 i} => R p.1/a0 p.1)
      (fun q : {i : I // a0 i<0} => R q.1/a0 q.1) hpair
    refine ⟨Fin.cons t x,?_⟩
    intro i
    rw [Fin.sum_univ_succ]
    change b i ≤ a0 i*t+∑ k, a i k.succ*x k
    have hbound : R i ≤ a0 i*t := by
      rcases lt_trichotomy (a0 i) 0 with hn | hz | hp
      · have hh := (le_div_iff_of_neg hn).mp (htn ⟨i,hn⟩)
        simpa only [mul_comm] using hh
      · have hh := hR (Sum.inl ⟨i,hz⟩)
        rw [show r = rowWeights a0 from rfl, rowWeights_sum] at hh
        simpa only [hz,zero_mul] using hh
      · have hh := (div_le_iff₀ hp).mp (htp ⟨i,hp⟩)
        simpa only [mul_comm] using hh
    dsimp [R] at hbound
    linarith

theorem feasible_fintype {I K : Type*} [Fintype I] [Fintype K]
    (a : I → K → ℝ) (b : I → ℝ)
    (hcert : ∀ w : I → ℝ, (∀ i, 0 ≤ w i) →
      (∀ k, ∑ i, w i*a i k=0) → ∑ i, w i*b i ≤ 0) :
    ∃ x : K → ℝ, ∀ i, b i ≤ ∑ k, a i k*x k := by
  classical
  let e := Fintype.equivFin K
  obtain ⟨x,hx⟩ := feasible (Fintype.card K) (fun i k => a i (e.symm k)) b (by
    intro w hw hz
    apply hcert w hw
    intro k
    simpa using hz (e k))
  refine ⟨fun k => x (e k),?_⟩
  intro i
  have he : (∑ k : Fin (Fintype.card K), a i (e.symm k)*x k) =
      ∑ k : K, a i k*x (e k) := by
    apply Fintype.sum_equiv e.symm
    intro k
    simp
  exact he ▸ hx i

end FiniteFarkas

end


section

open scoped BigOperators
open Finset

namespace FiniteLowerFace

lemma affine_average {I K : Type*} [Fintype I] [Fintype K]
    (a : I → K → ℝ) (z w : K → ℝ) (t : ℝ) (l : I → ℝ)
    (hl : ∑ i, l i=1) (hz : ∀ k, ∑ i, l i*a i k=z k) :
    (∑ i, l i*(t+∑ k, w k*a i k)) = t+∑ k, w k*z k := by
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hl,one_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hz k,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma support_of_minimum {I K : Type*} [Fintype I] [Fintype K]
    (a : I → K → ℝ) (c : I → ℝ) (z : K → ℝ) (l0 : I → ℝ)
    (hl0 : ∀ i, 0 ≤ l0 i) (hs0 : ∑ i, l0 i=1)
    (hz0 : ∀ k, ∑ i, l0 i*a i k=z k)
    (hmin : ∀ l : I → ℝ, (∀ i, 0 ≤ l i) → (∑ i, l i=1) →
      (∀ k, ∑ i, l i*a i k=z k) → ∑ i, l0 i*c i ≤ ∑ i, l i*c i) :
    ∃ (t : ℝ) (w : K → ℝ), (∀ i, t+∑ k, w k*a i k ≤ c i) ∧
      t+∑ k, w k*z k = ∑ i, l0 i*c i := by
  classical
  let m : ℝ := ∑ i, l0 i*c i
  let A : Option I → Option K → ℝ := fun i k =>
    match i,k with
    | none,none => 1
    | none,some k => z k
    | some _,none => -1
    | some i,some k => -a i k
  let B : Option I → ℝ := fun i => i.elim m (fun i => -c i)
  have hcert : ∀ v : Option I → ℝ, (∀ i, 0 ≤ v i) →
      (∀ k, ∑ i, v i*A i k=0) → ∑ i, v i*B i ≤ 0 := by
    intro v hv hzero
    have hs : ∑ i, v (some i) = v none := by
      have hh := hzero none
      simp only [Fintype.sum_option,A,mul_one,mul_neg_one,Finset.sum_neg_distrib] at hh
      linarith
    have hz (k : K) : ∑ i, v (some i)*a i k=v none*z k := by
      have hh := hzero (some k)
      simp only [Fintype.sum_option,A,mul_neg,Finset.sum_neg_distrib] at hh
      linarith
    have hm : v none*m ≤ ∑ i, v (some i)*c i := by
      by_cases hnon : v none=0
      · have hzall (i : I) : v (some i)=0 := by
          have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hv (some j))
            (Finset.mem_univ i)
          rw [hs,hnon] at hh
          exact le_antisymm hh (hv (some i))
        simp only [hnon,hzall,zero_mul,Finset.sum_const_zero,le_refl]
      · have hp : 0<v none := lt_of_le_of_ne (hv none) (Ne.symm hnon)
        have hh := hmin (fun i => v (some i)/v none)
          (fun i => div_nonneg (hv (some i)) hp.le)
          (by rw [← Finset.sum_div,hs,div_self hnon])
          (by intro k; simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div,hz, mul_div_cancel_left₀ _ hnon])
        have he : (∑ i, v (some i)/v none*c i) = (∑ i, v (some i)*c i)/v none := by
          simp_rw [div_mul_eq_mul_div,Finset.sum_div]
        rw [he] at hh
        have hh' := (le_div_iff₀ hp).mp hh
        simpa only [m,mul_comm] using hh'
    simpa only [Fintype.sum_option,B,Option.elim_none,Option.elim_some,mul_neg,
      Finset.sum_neg_distrib,← sub_eq_add_neg,sub_nonpos] using hm
  obtain ⟨f,hf⟩ := FiniteFarkas.feasible_fintype A B hcert
  let t := f none
  let w : K → ℝ := fun k => f (some k)
  have hi (i : I) : t+∑ k, w k*a i k ≤ c i := by
    have hh := hf (some i)
    simp only [Fintype.sum_option,A,B,Option.elim_some,neg_mul,Finset.sum_neg_distrib] at hh
    dsimp [t,w]
    simp_rw [mul_comm]
    linarith
  have hb : m ≤ t+∑ k, w k*z k := by
    have hh := hf none
    simpa only [Fintype.sum_option,A,B,Option.elim_none,one_mul,t,w,mul_comm] using hh
  refine ⟨t,w,hi,le_antisymm ?_ hb⟩
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hi i) (hl0 i))
  rw [affine_average a z w t l0 hs0 hz0] at hh
  exact hh

lemma exists_optimum {I K : Type*} [Fintype I] [Fintype K]
    (a : I → K → ℝ) (c : I → ℝ) (z : K → ℝ) (lfeas : I → ℝ)
    (hl : ∀ i, 0 ≤ lfeas i) (hs : ∑ i, lfeas i=1)
    (hz : ∀ k, ∑ i, lfeas i*a i k=z k) :
    ∃ l0 : I → ℝ, (∀ i, 0 ≤ l0 i) ∧ (∑ i, l0 i=1) ∧
      (∀ k, ∑ i, l0 i*a i k=z k) ∧
      (∀ l : I → ℝ, (∀ i, 0 ≤ l i) → (∑ i, l i=1) →
        (∀ k, ∑ i, l i*a i k=z k) → ∑ i, l0 i*c i ≤ ∑ i, l i*c i) := by
  let C : Set (I → ℝ) := stdSimplex ℝ I ∩ {l | ∀ k, ∑ i, l i*a i k=z k}
  have hclosed : IsClosed {l : I → ℝ | ∀ k, ∑ i, l i*a i k=z k} := by
    have he : {l : I → ℝ | ∀ k, ∑ i, l i*a i k=z k} =
        ⋂ k, {l : I → ℝ | ∑ i, l i*a i k=z k} := by ext l; simp
    rw [he]
    apply isClosed_iInter
    intro k
    apply isClosed_eq _ continuous_const
    fun_prop
  have hcompact : IsCompact C := (isCompact_stdSimplex ℝ I).inter_right hclosed
  have hne : C.Nonempty := ⟨lfeas,⟨hl,hs⟩,hz⟩
  obtain ⟨l0,hl0,hmin⟩ := hcompact.exists_isMinOn hne
    (show Continuous (fun l : I → ℝ => ∑ i, l i*c i) by fun_prop).continuousOn
  exact ⟨l0,hl0.1.1,hl0.1.2,hl0.2,fun l hl hs hz => hmin ⟨⟨hl,hs⟩,hz⟩⟩

lemma exposed_combination {I K : Type*} [Fintype I] [Fintype K]
    (a : I → K → ℝ) (c : I → ℝ) (z : K → ℝ) (lfeas : I → ℝ)
    (hl : ∀ i, 0 ≤ lfeas i) (hs : ∑ i, lfeas i=1)
    (hz : ∀ k, ∑ i, lfeas i*a i k=z k) :
    ∃ (l : I → ℝ) (t : ℝ) (w : K → ℝ),
      (∀ i, 0 ≤ l i) ∧ (∑ i, l i=1) ∧ (∀ k, ∑ i, l i*a i k=z k) ∧
      (∀ i, t+∑ k, w k*a i k ≤ c i) ∧
      (∀ i, l i ≠ 0 → t+∑ k, w k*a i k = c i) := by
  obtain ⟨l,hl,hs,hz,hmin⟩ := exists_optimum a c z lfeas hl hs hz
  obtain ⟨t,w,hsupport,heq⟩ := support_of_minimum a c z l hl hs hz hmin
  refine ⟨l,t,w,hl,hs,hz,hsupport,?_⟩
  have hnon (i : I) : 0 ≤ l i*(c i-(t+∑ k, w k*a i k)) :=
    mul_nonneg (hl i) (sub_nonneg.mpr (hsupport i))
  have hsum : (∑ i, l i*(c i-(t+∑ k, w k*a i k)))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [affine_average a z w t l hs hz,heq,sub_self]
  have heachi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp hsum
  intro i hi
  have hh := heachi i (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hi)).symm

end FiniteLowerFace

end


section

open DiscreteConvex.LConvexFunctionsB

def IntEmbedB {V : Type*} (D : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun p : V → ℤ => fun v => (p v : ℝ)) '' D
namespace LConvexSetSeparation
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shift_mem (D : Set (V → ℤ)) (hD : LConvexSet D) (p : V → ℤ)
    (hp : p ∈ D) (k : ℤ) : (fun v => p v+k) ∈ D := by
  have hper : Function.Periodic (fun p : V → ℤ => p ∈ D) 1 := by
    intro q
    apply propext
    constructor
    · intro hq
      simpa only [Pi.add_apply,Pi.one_apply,add_sub_cancel_right] using (hD.2.2 (q+1) hq).2
    · intro hq
      exact (hD.2.2 q hq).1
  have hh := (hper.zsmul k p).mpr hp
  convert hh using 1
  funext v
  simp

theorem mem_of_pairwise_differences (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℤ)
    (hpair : ∀ u v : V, ∃ q ∈ D, p v-p u ≤ q v-q u) : p ∈ D := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    obtain ⟨q,hq⟩ := hD.1
    have he : p=q := Subsingleton.elim _ _
    exact he ▸ hq
  | inr h =>
    letI := h
    have hn : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
    have hrow (u : V) : ∃ z ∈ D, p ≤ z ∧ z u=p u := by
      choose r hrD hr using hpair u
      let w : V → V → ℤ := fun v a => r v a+(p u-r v u)
      have hwD (v : V) : w v ∈ D := shift_mem D hD (r v) (hrD v) (p u-r v u)
      let z : V → ℤ := Finset.univ.sup' hn w
      refine ⟨z,?_,?_,?_⟩
      · exact Finset.sup'_mem D (fun x hx y hy => (hD.2.1 x hx y hy).1)
          Finset.univ hn w (fun v _ => hwD v)
      · intro v
        have hh := (Finset.le_sup' w (Finset.mem_univ v)) v
        have hv := hr v
        change p v ≤ z v
        change w v v ≤ z v at hh
        dsimp [w] at hh
        omega
      · change (Finset.univ.sup' hn w) u=p u
        rw [Finset.sup'_apply]
        exact Finset.sup'_eq_of_forall hn (fun v => w v u)
          (fun v _ => by dsimp [w]; omega)
    choose r hrD hrLe hrEq using hrow
    let z : V → ℤ := Finset.univ.inf' hn r
    have hzD : z ∈ D := Finset.inf'_mem D (fun x hx y hy => (hD.2.1 x hx y hy).2)
      Finset.univ hn r (fun v _ => hrD v)
    have he : z=p := by
      apply le_antisymm
      · intro v
        have hh := (Finset.inf'_le r (Finset.mem_univ v)) v
        simpa only [hrEq v] using hh
      · exact Finset.le_inf' hn r (fun v _ => hrLe v)
    exact he ▸ hzD

theorem separating_difference (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℤ) (hp : p ∉ D) :
    ∃ u v : V, ∀ q ∈ D, q v-q u ≤ p v-p u-1 := by
  classical
  by_contra h
  push Not at h
  apply hp
  apply mem_of_pairwise_differences D hD p
  intro u v
  obtain ⟨q,hq,hh⟩ := h u v
  exact ⟨q,hq,by omega⟩

theorem floor_shift_mem (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℝ) (hp : p ∈ convexHull ℝ (IntEmbedB D)) (t : ℝ) :
    (fun v => ⌊p v+t⌋) ∈ D := by
  classical
  let N : V → ℤ := fun v => ⌊p v+t⌋
  by_contra hn
  obtain ⟨u,v,hsep⟩ := separating_difference D hD N hn
  let B : ℤ := N v-N u-1
  have hc : Convex ℝ {x : V → ℝ | x v-x u ≤ (B : ℝ)} := by
    intro x hx y hy a b ha hb hab
    change a*x v+b*y v-(a*x u+b*y u) ≤ (B : ℝ)
    change x v-x u ≤ (B : ℝ) at hx
    change y v-y u ≤ (B : ℝ) at hy
    have hx' := mul_le_mul_of_nonneg_left hx ha
    have hy' := mul_le_mul_of_nonneg_left hy hb
    have hB : (a+b)*(B : ℝ)=(B : ℝ) := by rw [hab,one_mul]
    nlinarith
  have hi : IntEmbedB D ⊆ {x : V → ℝ | x v-x u ≤ (B : ℝ)} := by
    rintro x ⟨q,hq,rfl⟩
    change (q v : ℝ)-(q u : ℝ) ≤ ((N v-N u-1 : ℤ) : ℝ)
    exact_mod_cast hsep q hq
  have hbound := convexHull_min hi hc hp
  change p v-p u ≤ (B : ℝ) at hbound
  dsimp [B,N] at hbound
  simp only [Int.cast_sub,Int.cast_one] at hbound
  have h1 := Int.floor_le (p v+t)
  have h2 := Int.lt_floor_add_one (p u+t)
  linarith

end LConvexSetSeparation
end


section

set_option autoImplicit false
section
open DiscreteConvex.LConvexFunctions
namespace LDiscreteClipping
variable {V : Type*}

theorem floor_half (n : ℤ) : ⌊(n : ℝ)/2⌋ = n/2 := by
  simpa using Int.floor_div_natCast (n : ℝ) 2

theorem ceil_half (n : ℤ) : ⌈(n : ℝ)/2⌉ = (n+1)/2 := by
  have hh := Int.floor_neg (a := (n : ℝ)/2)
  have hn : ⌊-((n : ℝ)/2)⌋ = (-n)/2 := by
    simpa only [Int.cast_neg, neg_div] using floor_half (-n)
  rw [hn] at hh
  omega

theorem midpointFloor_apply (p q : V → ℤ) (v : V) :
    MidpointFloor p q v = (p v+q v)/2 := floor_half _

theorem midpointCeil_apply (p q : V → ℤ) (v : V) :
    MidpointCeil p q v = (p v+q v+1)/2 := ceil_half _

def clip (d : V → ℤ) (k : ℕ) : V → ℤ := fun v => min (d v) (k : ℤ)

theorem clipping (g : (V → ℤ) → WithTop ℝ) (hg : DiscreteMidpointConvexity g)
    (m : ℕ) (x d : V → ℤ) (hd : ∀ v, 0 ≤ d v ∧ d v ≤ (m : ℤ)) (k : ℕ) :
    g (x+clip d k)+g (x+d-clip d k) ≤ g x+g (x+d) := by
  induction m using Nat.strong_induction_on generalizing x d k with
  | h m ih =>
    by_cases hm : m ≤ 1
    · by_cases hk : k = 0
      · subst k
        have he : clip d 0 = 0 := by
          funext v
          exact min_eq_right (hd v).1
        simp [he]
      · have he : clip d k = d := by
          funext v
          apply min_eq_left
          have hv := hd v
          omega
        simp [he,add_comm]
    by_cases hx : g x = ⊤
    · simp [hx]
    by_cases hy : g (x+d) = ⊤
    · simp [hy]
    let a : V → ℤ := fun w => (d w+1)/2
    let b : V → ℤ := fun w => d w/2
    have hab : a+b=d := by
      funext w
      dsimp [a,b]
      omega
    have hba : b+a=d := by rw [add_comm,hab]
    have ham : (m+1)/2 < m := by omega
    have hbm : m/2 < m := by omega
    have ha (w : V) : 0 ≤ a w ∧ a w ≤ (((m+1)/2 : ℕ) : ℤ) := by
      dsimp [a]
      have hh := hd w
      omega
    have hb (w : V) : 0 ≤ b w ∧ b w ≤ ((m/2 : ℕ) : ℤ) := by
      dsimp [b]
      have hh := hd w
      omega
    let u := clip a ((k+1)/2)
    let v := clip b (k/2)
    have huv : u+v=clip d k := by
      funext w
      dsimp [u,v,clip,a,b]
      have hh := hd w
      omega
    have h1 : g (x+u)+g (x+a-u) ≤ g x+g (x+a) :=
      ih _ ham x a ha ((k+1)/2)
    have e2 : x+b+a=x+d := by rw [add_assoc,hba]
    have h2 : g (x+b+u)+g (x+d-u) ≤ g (x+b)+g (x+d) := by
      simpa only [e2] using ih _ ham (x+b) a ha ((k+1)/2)
    have e3 : x+u+b=x+b+u := by abel
    have h3 : g (x+u+v)+g (x+b+u-v) ≤ g (x+u)+g (x+b+u) := by
      simpa only [e3] using ih _ hbm (x+u) b hb (k/2)
    have e4 : x+a-u+b=x+d-u := by rw [← hab]; abel
    have h4 : g (x+a-u+v)+g (x+d-u-v) ≤ g (x+a-u)+g (x+d-u) := by
      simpa only [e4] using ih _ hbm (x+a-u) b hb (k/2)
    have hhi : MidpointCeil x (x+d)=x+a := by
      funext w
      rw [midpointCeil_apply]
      simp only [Pi.add_apply]
      dsimp [a]
      omega
    have hlo : MidpointFloor x (x+d)=x+b := by
      funext w
      rw [midpointFloor_apply]
      simp only [Pi.add_apply]
      dsimp [b]
      omega
    have hmiddle := hg x (x+d)
    rw [hhi,hlo] at hmiddle
    have hfinite : g (x+a)+g (x+b) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hx,hy⟩) hmiddle
    have hcrosshi : MidpointCeil (x+b+u-v) (x+a-u+v)=x+a := by
      funext w
      rw [midpointCeil_apply]
      simp only [Pi.add_apply,Pi.sub_apply]
      dsimp [a,b]
      omega
    have hcrosslo : MidpointFloor (x+b+u-v) (x+a-u+v)=x+b := by
      funext w
      rw [midpointFloor_apply]
      simp only [Pi.add_apply,Pi.sub_apply]
      dsimp [a,b]
      omega
    have hcross := hg (x+b+u-v) (x+a-u+v)
    rw [hcrosshi,hcrosslo] at hcross
    have hsum : (g (x+u+v)+g (x+d-u-v)) +
        (g (x+b+u-v)+g (x+a-u+v)) ≤ (g x+g (x+d))+(g (x+a)+g (x+b)) := by
      calc
        _ = (g (x+u+v)+g (x+b+u-v))+(g (x+a-u+v)+g (x+d-u-v)) := by ac_rfl
        _ ≤ (g (x+u)+g (x+b+u))+(g (x+a-u)+g (x+d-u)) := add_le_add h3 h4
        _ = (g (x+u)+g (x+a-u))+(g (x+b+u)+g (x+d-u)) := by ac_rfl
        _ ≤ (g x+g (x+a))+(g (x+b)+g (x+d)) := add_le_add h1 h2
        _ = _ := by ac_rfl
    have htotal := (add_le_add (le_refl (g (x+u+v)+g (x+d-u-v))) hcross).trans hsum
    have hfinal := (add_le_add_iff_left_of_ne_top hfinite).mp htotal
    have et1 : x+u+v=x+clip d k := by rw [add_assoc,huv]
    have et2 : x+d-u-v=x+d-clip d k := by rw [← huv]; abel
    simpa only [et1,et2] using hfinal

end LDiscreteClipping
end

section
open DiscreteConvex.LConvexFunctions
namespace LMidpointLift

lemma floor_half (a : ℤ) : ⌊(a : ℝ)/2⌋ = a/2 := by
  simpa using Int.floor_div_natCast (a : ℝ) 2

lemma ceil_half (a : ℤ) : ⌈(a : ℝ)/2⌉ = (a+1)/2 := by
  have hlo : 2*((a+1)/2)-2 < a := by omega
  have hhi : a ≤ 2*((a+1)/2) := by omega
  have hlo' : (2 : ℝ)*(((a+1)/2 : ℤ) : ℝ)-2 < (a : ℝ) := by exact_mod_cast hlo
  have hhi' : (a : ℝ) ≤ (2 : ℝ)*(((a+1)/2 : ℤ) : ℝ) := by exact_mod_cast hhi
  apply Int.ceil_eq_iff.mpr
  constructor <;> linarith

lemma floor_apply {V : Type*} (p q : V → ℤ) (v : V) :
    MidpointFloor p q v = (p v+q v)/2 := floor_half _

lemma ceil_apply {V : Type*} (p q : V → ℤ) (v : V) :
    MidpointCeil p q v = (p v+q v+1)/2 := ceil_half _

theorem lifted_midpoint {V : Type*} (g : (V → ℤ) → WithTop ℝ)
    (hg : DiscreteMidpointConvexity g) : DiscreteMidpointConvexity (LiftedFunctionL g) := by
  intro x y
  let p : V → ℤ := fun v => x (some v)-x none
  let q : V → ℤ := fun v => y (some v)-y none
  change g p+g q ≥ LiftedFunctionL g (MidpointCeil x y)+
    LiftedFunctionL g (MidpointFloor x y)
  by_cases heven : (x none+y none)%2=0
  · have hf : LiftedFunctionL g (MidpointFloor x y) = g (MidpointFloor p q) := by
      apply congrArg g
      funext v
      simp only [floor_apply]
      dsimp [p,q]
      omega
    have hc : LiftedFunctionL g (MidpointCeil x y) = g (MidpointCeil p q) := by
      apply congrArg g
      funext v
      simp only [ceil_apply]
      dsimp [p,q]
      omega
    rw [hf,hc]
    exact hg p q
  · have hodd : (x none+y none)%2=1 := by omega
    have hf : LiftedFunctionL g (MidpointFloor x y) = g (MidpointCeil p q) := by
      apply congrArg g
      funext v
      simp only [floor_apply,ceil_apply]
      dsimp [p,q]
      omega
    have hc : LiftedFunctionL g (MidpointCeil x y) = g (MidpointFloor p q) := by
      apply congrArg g
      funext v
      simp only [floor_apply,ceil_apply]
      dsimp [p,q]
      omega
    rw [hf,hc]
    simpa only [add_comm] using hg p q

end LMidpointLift
end

section
open DiscreteConvex.LConvexFunctions
namespace LMidpointConverse
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coordinate_bound (f : V → ℤ) (v : V) :
    f v ≤ ((∑ w, (f w).natAbs : ℕ) : ℤ) := by
  apply Int.le_natAbs.trans
  exact_mod_cast Finset.single_le_sum (fun w (_ : w ∈ Finset.univ) => Nat.zero_le (f w).natAbs)
    (Finset.mem_univ v)

theorem midpoint_shift_implies_sbf (g : (V → ℤ) → WithTop ℝ)
    (hg : DiscreteMidpointConvexity g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v+k)=g q) : SBF g := by
  intro p q
  let k : ℕ := ∑ v, (p v-q v).natAbs
  let d : V → ℤ := fun v => q v+(k : ℤ)-p v
  let m : ℕ := ∑ v, (d v).natAbs
  have hd (v : V) : 0 ≤ d v ∧ d v ≤ (m : ℤ) := by
    constructor
    · have h := coordinate_bound (fun w => p w-q w) v
      change p v-q v ≤ (k : ℤ) at h
      dsimp [d]
      omega
    · exact coordinate_bound d v
  have hh := LDiscreteClipping.clipping g hg m p d hd k
  have he1 : p+LDiscreteClipping.clip d k = fun v => (p ⊓ q) v+(k : ℤ) := by
    funext v
    simp only [Pi.add_apply,Pi.inf_apply,LDiscreteClipping.clip]
    dsimp [d]
    omega
  have he2 : p+d-LDiscreteClipping.clip d k = p ⊔ q := by
    funext v
    simp only [Pi.add_apply,Pi.sub_apply,Pi.sup_apply,LDiscreteClipping.clip]
    dsimp [d]
    omega
  have he3 : p+d = fun v => q v+(k : ℤ) := by
    funext v
    dsimp [d]
    omega
  rw [he1,he2,he3,hshift,hshift] at hh
  simpa only [add_comm] using hh


end LMidpointConverse
end
end


section

open DiscreteConvex.LConvexFunctionsB

namespace LWeightedMinima
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma finite_dom (g : (V → ℤ) → WithTop ℝ)
    (hbdd : ∃ M : ℤ, ∀ p ∈ DomZ g, ∀ v, |p v| ≤ M) : (DomZ g).Finite := by
  obtain ⟨M,hM⟩ := hbdd
  apply (Set.finite_Icc (fun _ : V => -M) (fun _ => M)).subset
  intro p hp
  exact ⟨fun v => (abs_le.mp (hM p hp v)).1, fun v => (abs_le.mp (hM p hp v)).2⟩

lemma exists_min (g : (V → ℤ) → WithTop ℝ) (hne : (DomZ g).Nonempty)
    (hfin : (DomZ g).Finite) : ∃ p ∈ DomZ g, p ∈ ArgMin g := by
  obtain ⟨p,hp,hmin⟩ := Set.exists_min_image (DomZ g) g hfin hne
  refine ⟨p,hp,?_⟩
  intro q
  by_cases hq : q ∈ DomZ g
  · exact hmin q hq
  · have he : g q = ⊤ := by simpa [DomZ] using hq
    rw [he]
    exact le_top

lemma lattice_min (g : (V → ℤ) → WithTop ℝ) (hS : SBF g)
    (hne : (DomZ g).Nonempty) (p q : V → ℤ)
    (hp : p ∈ ArgMin g) (hq : q ∈ ArgMin g) :
    (p ⊔ q) ∈ ArgMin g ∧ (p ⊓ q) ∈ ArgMin g := by
  obtain ⟨z,hz⟩ := hne
  have hpfin : g p ≠ ⊤ := ne_top_of_le_ne_top hz (hp z)
  have hqfin : g q ≠ ⊤ := ne_top_of_le_ne_top hz (hq z)
  have hs := hS p q
  have hu : g (p ⊔ q) + g q ≤ g p + g q :=
    (add_le_add le_rfl (hq (p ⊓ q))).trans hs
  have hl : g p + g (p ⊓ q) ≤ g p + g q :=
    (add_le_add (hp (p ⊔ q)) le_rfl).trans hs
  have hu' := (add_le_add_iff_left_of_ne_top hqfin).mp hu
  have hl' := (add_le_add_iff_right_of_ne_top hpfin).mp hl
  exact ⟨fun t => hu'.trans (hp t), fun t => hl'.trans (hq t)⟩

lemma weighted_dom (g : (V → ℤ) → WithTop ℝ) (w : V → ℝ) :
    DomZ (LinearWeight g w) = DomZ g := by
  ext p
  change (g p + ((-(∑ v, w v * (p v : ℝ)) : ℝ) : WithTop ℝ) ≠ ⊤) ↔ g p ≠ ⊤
  rw [WithTop.add_ne_top]
  exact and_iff_left WithTop.coe_ne_top

lemma modular_weight (w : V → ℝ) (p q : V → ℤ) :
    (-(∑ v, w v * ((p ⊔ q) v : ℝ))) + (-(∑ v, w v * ((p ⊓ q) v : ℝ))) =
    (-(∑ v, w v * (p v : ℝ))) + (-(∑ v, w v * (q v : ℝ))) := by
  simp only [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [← mul_add, ← mul_add, ← Int.cast_add, ← Int.cast_add]
  congr 2
  exact max_add_min _ _

lemma weighted_sbf (g : (V → ℤ) → WithTop ℝ) (hS : SBF g) (w : V → ℝ) :
    SBF (LinearWeight g w) := by
  intro p q
  simp only [LinearWeight]
  rw [add_add_add_comm (g (p ⊔ q)) _ (g (p ⊓ q)), add_add_add_comm (g p) _ (g q), ← WithTop.coe_add,
    ← WithTop.coe_add, modular_weight]
  exact add_le_add (hS p q) le_rfl

lemma weighted_lnatural (g : (V → ℤ) → WithTop ℝ) (hL : LNaturalConvex g)
    (w : V → ℝ) : LNaturalConvex (LinearWeight g w) := by
  constructor
  · intro p q
    let W : (Option V → ℤ) → ℝ := fun z => -(∑ v, w v * ((z (some v)-z none : ℤ) : ℝ))
    have hmod : W (p ⊔ q) + W (p ⊓ q) = W p + W q := by
      dsimp [W]
      simp only [← neg_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      rw [← mul_add, ← mul_add, ← Int.cast_add, ← Int.cast_add]
      congr 2
      try simp only [Pi.sup_apply,Pi.inf_apply]
      omega
    change (LiftedFunctionL g (p ⊔ q) + (W (p ⊔ q) : WithTop ℝ)) +
      (LiftedFunctionL g (p ⊓ q) + (W (p ⊓ q) : WithTop ℝ)) ≤
      (LiftedFunctionL g p + (W p : WithTop ℝ)) +
      (LiftedFunctionL g q + (W q : WithTop ℝ))
    rw [add_add_add_comm (LiftedFunctionL g (p ⊔ q)) _ (LiftedFunctionL g (p ⊓ q)),
      add_add_add_comm (LiftedFunctionL g p) _ (LiftedFunctionL g q),
      ← WithTop.coe_add, ← WithTop.coe_add,hmod]
    exact add_le_add (hL.1 p q) le_rfl
  · refine ⟨0,?_⟩
    intro p
    simp only [LiftedFunctionL,Pi.add_apply,Pi.one_apply,WithTop.coe_zero,add_zero]
    congr 1
    funext v
    omega

lemma argmin_lift (g : (V → ℤ) → WithTop ℝ) :
    ArgMin (LiftedFunctionL g) = LiftedSetL (ArgMin g) := by
  ext p
  constructor
  · intro hp q
    simpa [LiftedFunctionL] using hp (fun o => o.elim 0 q)
  · intro hp q
    exact hp (fun v => q (some v)-q none)

lemma argmin_lnatural (g : (V → ℤ) → WithTop ℝ) (hL : LNaturalConvex g)
    (hdom : (DomZ g).Nonempty) (hmin : (ArgMin g).Nonempty) :
    LNatConvexSet (ArgMin g) := by
  change LConvexSet (LiftedSetL (ArgMin g))
  rw [← argmin_lift]
  obtain ⟨p,hp⟩ := hmin
  have hnon : (ArgMin (LiftedFunctionL g)).Nonempty := by
    refine ⟨fun o => o.elim 0 p,?_⟩
    intro q
    simpa [LiftedFunctionL] using hp (fun v => q (some v)-q none)
  have hdom' : (DomZ (LiftedFunctionL g)).Nonempty := by
    obtain ⟨z,hz⟩ := hdom
    refine ⟨fun o => o.elim 0 z,?_⟩
    simpa [DomZ,LiftedFunctionL] using hz
  refine ⟨hnon,?_,?_⟩
  · intro x hx y hy
    exact lattice_min (LiftedFunctionL g) hL.1 hdom' x y hx hy
  · intro x hx
    constructor <;> intro q
    · simpa [LiftedFunctionL] using hx q
    · simpa [LiftedFunctionL] using hx q

lemma natural_forward (g : (V → ℤ) → WithTop ℝ) (hne : (DomZ g).Nonempty)
    (hbdd : ∃ M : ℤ, ∀ p ∈ DomZ g, ∀ v, |p v| ≤ M)
    (hL : LNaturalConvex g) :
    ∀ x : V → ℝ, LNatConvexSet (ArgMin (LinearWeight g (fun v => -x v))) := by
  intro x
  have hd : (DomZ (LinearWeight g (fun v => -x v))).Nonempty := by
    rw [weighted_dom]; exact hne
  have hf : (DomZ (LinearWeight g (fun v => -x v))).Finite := by
    rw [weighted_dom]; exact finite_dom g hbdd
  obtain ⟨p,_,hp⟩ := exists_min _ hd hf
  exact argmin_lnatural _ (weighted_lnatural g hL _) hd ⟨p,hp⟩

lemma finite_shift_impossible (S : Set (V → ℤ)) (hfin : S.Finite) (hne : S.Nonempty)
    (hshift : ∀ p ∈ S, (fun v => p v+1) ∈ S) (v : V) : False := by
  obtain ⟨p,hp,hmax⟩ := Set.exists_max_image S (fun p => p v) hfin hne
  have hh := hmax (fun v => p v+1) (hshift p hp)
  omega

lemma argmin_subset_dom (g : (V → ℤ) → WithTop ℝ) (hne : (DomZ g).Nonempty) :
    ArgMin g ⊆ DomZ g := by
  obtain ⟨z,hz⟩ := hne
  intro p hp
  exact ne_top_of_le_ne_top hz (hp z)

lemma bounded_l_characterization (g : (V → ℤ) → WithTop ℝ) (hne : (DomZ g).Nonempty)
    (hbdd : ∃ M : ℤ, ∀ p ∈ DomZ g, ∀ v, |p v| ≤ M) :
    (SBF g ∧ TRF g) ↔ ∀ x : V → ℝ, LConvexSet (ArgMin (LinearWeight g (fun v => -x v))) := by
  classical
  have hf := finite_dom g hbdd
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    have hnT : ¬ TRF g := by
      rintro ⟨r,hr⟩
      apply finite_shift_impossible (DomZ g) hf hne ?_ v
      intro p hp
      have hh : g (p+1) ≠ ⊤ := by rw [hr]; simpa [DomZ] using hp
      exact hh
    constructor
    · intro h
      exact (hnT h.2).elim
    · intro h
      have hzero : LinearWeight g (fun _ : V => -(0 : ℝ)) = g := by
        funext p
        simp [LinearWeight]
      have hset := h (fun _ => 0)
      rw [hzero] at hset
      exact (finite_shift_impossible (ArgMin g) (hf.subset (argmin_subset_dom g hne))
        hset.1 (fun p hp => (hset.2.2 p hp).1) v).elim
  · letI : IsEmpty V := not_nonempty_iff.mp hV
    have hall : ∀ a b : V → ℤ, a=b := fun a b => Subsingleton.elim _ _
    constructor
    · intro _ x
      have hmin : ∀ p : V → ℤ, p ∈ ArgMin (LinearWeight g (fun v => -x v)) := by
        intro p q
        rw [hall p q]
      exact ⟨⟨0,hmin 0⟩,fun p _ q _ => ⟨hmin _,hmin _⟩,
        fun p _ => ⟨hmin _,hmin _⟩⟩
    · intro _
      constructor
      · intro p q
        simp only [hall q p,hall (p ⊔ p) p,hall (p ⊓ p) p]
        exact le_rfl
      · refine ⟨0,?_⟩
        intro p
        rw [hall (p+1) p]
        simp

end LWeightedMinima


end


section

open DiscreteConvex.LConvexFunctionsB

namespace LExposedMinima
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma lifted_hull (D : Set (V → ℤ)) (z : V → ℝ)
    (hz : z ∈ convexHull ℝ (IntEmbedB D)) :
    (fun o : Option V => o.elim 0 z) ∈ convexHull ℝ (IntEmbedB (LiftedSetL D)) := by
  let e : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) :=
    { toFun := fun x o => o.elim 0 x
      map_add' := by intro x y; funext o; cases o <;> simp
      map_smul' := by intro a x; funext o; cases o <;> simp }
  have he : e '' IntEmbedB D ⊆ IntEmbedB (LiftedSetL D) := by
    rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩
    refine ⟨fun o => o.elim 0 p,?_,?_⟩
    · simpa only [LiftedSetL,Set.mem_ofPred_eq,Option.elim_some,Option.elim_none,sub_zero] using hp
    · funext o
      cases o <;> simp [e]
  have hh : e z ∈ e '' convexHull ℝ (IntEmbedB D) := ⟨z,hz,rfl⟩
  rw [e.image_convexHull] at hh
  exact convexHull_mono he hh

lemma natural_floor_shift_mem (D : Set (V → ℤ)) (hD : LNatConvexSet D)
    (z : V → ℝ) (hz : z ∈ convexHull ℝ (IntEmbedB D)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) : (fun v => ⌊z v+t⌋) ∈ D := by
  have hh := LConvexSetSeparation.floor_shift_mem (LiftedSetL D) hD
    (fun o : Option V => o.elim 0 z) (lifted_hull D z hz) t
  have hfloor : ⌊t⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨ht0,ht1⟩
  simpa [LiftedSetL,hfloor] using hh

lemma floor_half_add (n : ℤ) : ⌊(n : ℝ)/2+(1:ℝ)/2⌋ = (n+1)/2 := by
  have he : (n : ℝ)/2+(1:ℝ)/2=((n+1 : ℤ) : ℝ)/2 := by push_cast; ring
  rw [he]
  exact LMidpointLift.floor_half _

lemma rounded_midpoints_in_hull (D : Set (V → ℤ)) (hD : LNatConvexSet D)
    (p q : V → ℤ)
    (hz : (fun v => ((p v+q v : ℤ) : ℝ)/2) ∈ convexHull ℝ (IntEmbedB D)) :
    DiscreteConvex.LConvexFunctions.MidpointFloor p q ∈ D ∧
    DiscreteConvex.LConvexFunctions.MidpointCeil p q ∈ D := by
  constructor
  · have hh := natural_floor_shift_mem D hD _ hz 0 (le_refl _) (by norm_num)
    have he : DiscreteConvex.LConvexFunctions.MidpointFloor p q = (fun v => (p v+q v)/2) := by
      funext v; exact LMidpointLift.floor_apply p q v
    rw [he]
    simpa only [add_zero, LMidpointLift.floor_half] using hh
  · have hh := natural_floor_shift_mem D hD _ hz ((1:ℝ)/2) (by norm_num) (by norm_num)
    have he : DiscreteConvex.LConvexFunctions.MidpointCeil p q = (fun v => (p v+q v+1)/2) := by
      funext v; exact LMidpointLift.ceil_apply p q v
    rw [he]
    simpa only [floor_half_add] using hh

omit [DecidableEq V] in
lemma weight_sum_eq (w : V → ℝ) (a b p q : V → ℤ)
    (he : ∀ v, a v+b v=p v+q v) :
    (-(∑ v, w v * (a v : ℝ))) + (-(∑ v, w v * (b v : ℝ))) =
    (-(∑ v, w v * (p v : ℝ))) + (-(∑ v, w v * (q v : ℝ))) := by
  simp only [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [← mul_add,← mul_add,← Int.cast_add,← Int.cast_add,he]

omit [DecidableEq V] in
lemma cancel_weighted_minima (g : (V → ℤ) → WithTop ℝ) (w : V → ℝ)
    (a b p q : V → ℤ) (ha : a ∈ ArgMin (LinearWeight g w))
    (hb : b ∈ ArgMin (LinearWeight g w)) (he : ∀ v, a v+b v=p v+q v) :
    g a+g b ≤ g p+g q := by
  have hh := add_le_add (ha p) (hb q)
  simp only [LinearWeight] at hh
  rw [add_add_add_comm (g a) _ (g b),add_add_add_comm (g p) _ (g q),
    ← WithTop.coe_add,← WithTop.coe_add,weight_sum_eq w a b p q he] at hh
  exact (add_le_add_iff_left_of_ne_top WithTop.coe_ne_top).mp hh

lemma natural_converse_of_faces (g : (V → ℤ) → WithTop ℝ)
    (hsets : ∀ x : V → ℝ, LNatConvexSet (ArgMin (LinearWeight g (fun v => -x v))))
    (hfaces : ∀ p q : V → ℤ, g p ≠ ⊤ → g q ≠ ⊤ →
      ∃ w : V → ℝ, (fun v => ((p v+q v : ℤ) : ℝ)/2) ∈
        convexHull ℝ (IntEmbedB (ArgMin (LinearWeight g w)))) : LNaturalConvex g := by
  have hmid : DiscreteConvex.LConvexFunctions.DiscreteMidpointConvexity g := by
    intro p q
    by_cases hp : g p=⊤
    · simp [hp]
    by_cases hq : g q=⊤
    · simp [hq]
    obtain ⟨w,hw⟩ := hfaces p q hp hq
    have hs : LNatConvexSet (ArgMin (LinearWeight g w)) := by
      simpa only [neg_neg] using hsets (fun v => -w v)
    obtain ⟨hf,hc⟩ := rounded_midpoints_in_hull _ hs p q hw
    apply cancel_weighted_minima g w _ _ p q hc hf
    intro v
    rw [LMidpointLift.ceil_apply,LMidpointLift.floor_apply]
    omega
  constructor
  · apply LMidpointConverse.midpoint_shift_implies_sbf _ (LMidpointLift.lifted_midpoint g hmid)
    intro q k
    unfold DiscreteConvex.LConvexFunctions.LiftedFunctionL
    congr 1
    funext v
    dsimp
    omega
  · refine ⟨0,?_⟩
    intro p
    simp only [LiftedFunctionL,Pi.add_apply,Pi.one_apply,WithTop.coe_zero,add_zero]
    congr 1
    funext v
    omega

omit [DecidableEq V] in
lemma midpoint_face (g : (V → ℤ) → WithTop ℝ) (hfin : (DomZ g).Finite)
    (p q : V → ℤ) (hp : g p ≠ ⊤) (hq : g q ≠ ⊤) :
    ∃ w : V → ℝ, (fun v => ((p v+q v : ℤ) : ℝ)/2) ∈
      convexHull ℝ (IntEmbedB (ArgMin (LinearWeight g w))) := by
  classical
  let I := DomZ g
  let : Fintype I := hfin.fintype
  let P : I := ⟨p,hp⟩
  let Q : I := ⟨q,hq⟩
  let a : I → V → ℝ := fun i v => (i.1 v : ℝ)
  let c : I → ℝ := fun i => (g i.1).untop i.2
  let z : V → ℝ := fun v => ((p v+q v : ℤ) : ℝ)/2
  let l0 : I → ℝ := fun i => (if i=P then (1:ℝ)/2 else 0) + (if i=Q then (1:ℝ)/2 else 0)
  have hl0 (i : I) : 0 ≤ l0 i := by dsimp [l0]; split_ifs <;> norm_num
  have hs0 : ∑ i, l0 i=1 := by simp [l0,Finset.sum_add_distrib]; norm_num
  have hz0 (v : V) : ∑ i, l0 i*a i v=z v := by
    simp only [l0,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
    simp [a,P,Q,z]
    ring
  obtain ⟨l,t,w,hl,hs,hz,hsupport,htight⟩ :=
    FiniteLowerFace.exposed_combination a c z l0 hl0 hs0 hz0
  have hcoe (i : I) : (c i : WithTop ℝ)=g i.1 := WithTop.coe_untop _ _
  have hvalue (i : I) : LinearWeight g w i.1 = ((c i - ∑ v, w v*a i v : ℝ) : WithTop ℝ) := by
    rw [LinearWeight,← hcoe i,← WithTop.coe_add]
    rfl
  have hmin (i : I) (hi : l i ≠ 0) : i.1 ∈ ArgMin (LinearWeight g w) := by
    have hti : LinearWeight g w i.1=(t : WithTop ℝ) := by
      rw [hvalue,← htight i hi]
      congr 1
      ring
    intro r
    rw [hti]
    by_cases hr : g r=⊤
    · simp [LinearWeight,hr]
    · let j : I := ⟨r,hr⟩
      have hj : LinearWeight g w r = ((c j - ∑ v, w v*a j v : ℝ) : WithTop ℝ) := hvalue j
      rw [hj]
      apply WithTop.coe_le_coe.mpr
      have hh := hsupport j
      linarith
  obtain ⟨j,hj⟩ : ∃ j : I, l j ≠ 0 := by
    by_contra h
    push Not at h
    have hh : ∑ i, l i=0 := by simp [h]
    linarith
  let b : I → V → ℝ := fun i => if l i=0 then a j else a i
  have hb (i : I) : b i ∈ IntEmbedB (ArgMin (LinearWeight g w)) := by
    dsimp [b]
    split_ifs with hi
    · exact ⟨j.1,hmin j hj,rfl⟩
    · exact ⟨i.1,hmin i hi,rfl⟩
  refine ⟨w,mem_convexHull_of_exists_fintype l b hl hs hb ?_⟩
  funext v
  rw [Finset.sum_apply]
  change (∑ i, l i*b i v)=z v
  rw [← hz v]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [b]
  split_ifs with hi
  · simp [hi]
  · rfl

end LExposedMinima

end

open DiscreteConvex.LConvexFunctionsB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ)
    (hne : (DomZ g).Nonempty) (hbdd : ∃ M : ℤ, ∀ p ∈ DomZ g, ∀ v, |p v| ≤ M) :
    ((SBF g ∧ TRF g) ↔ ∀ x : V → ℝ, LConvexSet (ArgMin (LinearWeight g (fun v => -x v)))) ∧
    (LNaturalConvex g ↔ ∀ x : V → ℝ, LNatConvexSet (ArgMin (LinearWeight g (fun v => -x v)))) := by
  refine ⟨LWeightedMinima.bounded_l_characterization g hne hbdd,?_,?_⟩
  · exact LWeightedMinima.natural_forward g hne hbdd
  · intro h
    exact LExposedMinima.natural_converse_of_faces g h
      (LExposedMinima.midpoint_face g (LWeightedMinima.finite_dom g hbdd))

#print axioms solution
