-- Prove2me | solution 1 for DelayDep.Equiv.exo_law_determined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:39:07.574982+00:00
-- url     : https://prove2.me/submissions/9ed15128-b40c-4b5d-b58f-6e0677f80f5a

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DDM
open MeasureTheory DelayDep.Equiv

/-! ### Measurability of the sorting operator -/

lemma measurableSet_sort_eq (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    MeasurableSet {v : Fin k → ℝ | σ = Tuple.sort v} := by
  have : {v : Fin k → ℝ | σ = Tuple.sort v} =
      (⋂ a : Fin k, ⋂ b : Fin k, {v : Fin k → ℝ | a ≤ b → v (σ a) ≤ v (σ b)}) ∩
      (⋂ a : Fin k, ⋂ b : Fin k, {v : Fin k → ℝ | a < b → v (σ a) = v (σ b) → σ a < σ b}) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Tuple.eq_sort_iff]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_)
    (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_)
  · by_cases h : a ≤ b
    · simp only [h, true_implies]
      exact measurableSet_le (measurable_pi_apply (σ a)) (measurable_pi_apply (σ b))
    · simp [h]
  · by_cases h : a < b
    · by_cases h2 : σ a < σ b
      · simp [h, h2]
      · simp only [h, h2, true_implies, imp_false]
        exact (measurableSet_eq_fun (measurable_pi_apply (σ a)) (measurable_pi_apply (σ b))).compl
    · simp [h]

lemma measurable_sortR (k : ℕ) : Measurable (sortR : (Fin k → ℝ) → (Fin k → ℝ)) := by
  have h : ∀ v : Fin k → ℝ, sortR v = fun j =>
      ∑ σ : Equiv.Perm (Fin k), if σ = Tuple.sort v then v (σ j) else 0 := by
    intro v; funext j
    rw [Finset.sum_ite_eq' Finset.univ (Tuple.sort v) (fun σ => v (σ j))]
    simp [sortR]
  have : (sortR : (Fin k → ℝ) → (Fin k → ℝ)) = fun v => fun j =>
      ∑ σ : Equiv.Perm (Fin k), if σ = Tuple.sort v then v (σ j) else 0 := funext h
  rw [this]
  refine measurable_pi_lambda _ (fun j => ?_)
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  exact Measurable.ite (measurableSet_sort_eq k σ) (measurable_pi_apply _) measurable_const

/-! ### Measurable list-valued maps -/

lemma mergeSort_eq (l : List ℝ) :
    l.mergeSort (fun a b => decide (a ≤ b)) = List.ofFn (sortR (fun i : Fin l.length => l.get i)) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact (List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; linarith)
      (fun a b => by simpa using le_total a b) l).imp (by simp)
  · exact (Tuple.monotone_sort _).sortedLE_ofFn.pairwise
  · refine (List.mergeSort_perm l _).trans ?_
    have := (Equiv.Perm.ofFn_comp_perm (Tuple.sort (fun i : Fin l.length => l.get i))
      (fun i : Fin l.length => l.get i)).symm
    rw [List.ofFn_get] at this
    exact this

lemma mergeSort_getD (l : List ℝ) (j : ℕ) :
    (l.mergeSort (fun a b => decide (a ≤ b))).getD j 0 =
      if h : j < l.length then sortR (fun i : Fin l.length => l.getD i 0) ⟨j, h⟩ else 0 := by
  rw [mergeSort_eq]
  have e : (fun i : Fin l.length => l.get i) = (fun i : Fin l.length => l.getD i 0) := by
    funext i; simp [List.getD_eq_getElem?_getD]
  rw [e]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

structure MeasList {X : Type} [MeasurableSpace X] (F : X → List ℝ) : Prop where
  len : Measurable (fun x => (F x).length)
  get : ∀ j, Measurable (fun x => (F x).getD j 0)

variable {X : Type} [MeasurableSpace X]

lemma measurable_of_nat {f : X → ℕ} (hf : Measurable f) (g : ℕ → ℕ) : Measurable (fun x => g (f x)) :=
  measurable_from_top.comp hf

lemma measurable_piecewise_nat {Y : Type} [MeasurableSpace Y] {N : X → ℕ} (hN : Measurable N)
    (G : ℕ → X → Y) (hG : ∀ m, Measurable (G m)) : Measurable (fun x => G (N x) x) := by
  have : Measurable (fun p : X × ℕ => G p.2 p.1) := measurable_from_prod_countable_left hG
  exact this.comp (measurable_id.prodMk hN)

lemma MeasList.filterMap {ι : Type} (l : List ι) (p : ι → X → Prop) {inst : ∀ i x, Decidable (p i x)}
    (hp : ∀ i, MeasurableSet {x | p i x}) (g : ι → X → ℝ) (hg : ∀ i, Measurable (g i)) :
    MeasList (fun x => (l.filter (fun i => decide (p i x))).map (fun i => g i x)) := by
  induction l with
  | nil => exact ⟨measurable_const, fun j => by simp⟩
  | cons a l ih =>
    have hF : ∀ x, ((a :: l).filter (fun i => decide (p i x))).map (fun i => g i x) =
        if p a x then g a x :: (l.filter (fun i => decide (p i x))).map (fun i => g i x)
        else (l.filter (fun i => decide (p i x))).map (fun i => g i x) := by
      intro x; by_cases h : p a x <;> simp [List.filter_cons, h]
    constructor
    · simp_rw [hF]
      have : (fun x => (if p a x then g a x :: (l.filter (fun i => decide (p i x))).map (fun i => g i x)
          else (l.filter (fun i => decide (p i x))).map (fun i => g i x)).length) =
          fun x => if p a x then ((l.filter (fun i => decide (p i x))).map (fun i => g i x)).length + 1
            else ((l.filter (fun i => decide (p i x))).map (fun i => g i x)).length := by
        funext x; split_ifs <;> simp
      rw [this]
      exact Measurable.ite (hp a) (measurable_of_nat ih.len (· + 1)) ih.len
    · intro j
      simp_rw [hF]
      cases j with
      | zero =>
        have : (fun x => (if p a x then g a x :: (l.filter (fun i => decide (p i x))).map (fun i => g i x)
            else (l.filter (fun i => decide (p i x))).map (fun i => g i x)).getD 0 0) =
            fun x => if p a x then g a x
              else ((l.filter (fun i => decide (p i x))).map (fun i => g i x)).getD 0 0 := by
          funext x; split_ifs <;> simp
        rw [this]; exact Measurable.ite (hp a) (hg a) (ih.get 0)
      | succ j =>
        have : (fun x => (if p a x then g a x :: (l.filter (fun i => decide (p i x))).map (fun i => g i x)
            else (l.filter (fun i => decide (p i x))).map (fun i => g i x)).getD (j+1) 0) =
            fun x => if p a x then ((l.filter (fun i => decide (p i x))).map (fun i => g i x)).getD j 0
              else ((l.filter (fun i => decide (p i x))).map (fun i => g i x)).getD (j+1) 0 := by
          funext x; split_ifs <;> simp
        rw [this]; exact Measurable.ite (hp a) (ih.get j) (ih.get (j+1))

lemma MeasList.append {F G : X → List ℝ} (hF : MeasList F) (hG : MeasList G) :
    MeasList (fun x => F x ++ G x) := by
  constructor
  · simp only [List.length_append]
    exact measurable_piecewise_nat hF.len (fun m x => m + (G x).length)
      (fun m => measurable_of_nat hG.len (m + ·))
  · intro j
    have : (fun x => (F x ++ G x).getD j 0) = fun x =>
        if j < (F x).length then (F x).getD j 0 else (G x).getD (j - (F x).length) 0 := by
      funext x
      split_ifs with h
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (not_lt.mp h)]
    rw [this]
    refine Measurable.ite (hF.len (MeasurableSet.of_discrete (s := {k | j < k}))) (hF.get j) ?_
    exact measurable_piecewise_nat hF.len (fun m x => (G x).getD (j - m) 0) (fun m => hG.get _)

lemma MeasList.piecewise {N : X → ℕ} (hN : Measurable N) (F : ℕ → X → List ℝ)
    (hF : ∀ m, MeasList (F m)) : MeasList (fun x => F (N x) x) :=
  ⟨measurable_piecewise_nat hN (fun m x => (F m x).length) (fun m => (hF m).len),
    fun j => measurable_piecewise_nat hN (fun m x => (F m x).getD j 0) (fun m => (hF m).get j)⟩

lemma MeasList.mergeSort {F : X → List ℝ} (hF : MeasList F) :
    MeasList (fun x => (F x).mergeSort (fun a b => decide (a ≤ b))) := by
  constructor
  · simp only [List.length_mergeSort]; exact hF.len
  · intro j
    simp_rw [mergeSort_getD]
    refine measurable_piecewise_nat hF.len
      (fun k x => if h : j < k then sortR (fun i : Fin k => (F x).getD i 0) ⟨j, h⟩ else 0)
      (fun k => ?_)
    by_cases h : j < k
    · have e : (fun x => if h : j < k then sortR (fun i : Fin k => (F x).getD i 0) ⟨j, h⟩ else 0) =
          fun x => sortR (fun i : Fin k => (F x).getD i 0) ⟨j, h⟩ := by
        funext x; rw [dif_pos h]
      rw [e]
      exact (measurable_pi_apply (⟨j, h⟩ : Fin k)).comp ((measurable_sortR k).comp
        (measurable_pi_lambda _ (fun i => hF.get i)))
    · have e : (fun x => if h : j < k then sortR (fun i : Fin k => (F x).getD i 0) ⟨j, h⟩ else 0) =
          fun _ => 0 := by
        funext x; rw [dif_neg h]
      rw [e]; exact measurable_const

lemma MeasList.replicate {K : X → ℕ} (hK : Measurable K) :
    MeasList (fun x => List.replicate (K x) (0:ℝ)) :=
  ⟨by simpa using hK, fun j => by
    have e : (fun x => (List.replicate (K x) (0:ℝ)).getD j 0) = fun _ => 0 := by
      funext x; by_cases h : j < K x <;> simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, h]
    rw [e]; exact measurable_const⟩

end DDM

namespace DDM
open MeasureTheory DelayDep.Equiv
open scoped Classical

variable {n : ℕ} [NeZero n]

abbrev XS (n : ℕ) := ((ℕ → ℝ) × (Fin n → ℝ)) × (ℕ → ℝ × ℝ)

lemma measurable_kappa (i : ℕ) : Measurable (fun x : XS n => kappa x.1.1 i) := by
  unfold kappa
  exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))

lemma measurable_Zvec (i : ℕ) :
    Measurable (fun x : XS n => Zvec x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i) := by
  induction i with
  | zero =>
    show Measurable (fun x : XS n => sortR (fun k => max (x.1.2 k - x.1.1 0) 0))
    exact (measurable_sortR n).comp (measurable_pi_lambda _ fun k =>
      (((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)).sub
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst))).max measurable_const)
  | succ i ih =>
    show Measurable (fun x : XS n => sortR (fun k => max
      (Zvec x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i k
        + (if Zvec x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i 0 ≤ (x.2 i).2
            then (x.2 i).1 else 0) * e1 k - x.1.1 (i + 1)) 0))
    have h0 : Measurable (fun x : XS n => Zvec x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i 0) :=
      (measurable_pi_apply 0).comp ih
    have hT : Measurable (fun x : XS n => (x.2 i).2) :=
      measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)
    have hS : Measurable (fun x : XS n => (x.2 i).1) :=
      measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
    have hite : Measurable (fun x : XS n =>
        if Zvec x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i 0 ≤ (x.2 i).2
          then (x.2 i).1 else 0) :=
      Measurable.ite (measurableSet_le h0 hT) hS measurable_const
    exact (measurable_sortR n).comp (measurable_pi_lambda _ fun k =>
      ((((measurable_pi_apply k).comp ih).add (hite.mul_const _)).sub
        ((measurable_pi_apply (i+1)).comp (measurable_fst.comp measurable_fst))).max measurable_const)

lemma measurable_wait (i : ℕ) :
    Measurable (fun x : XS n => wait x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i) :=
  (measurable_pi_apply 0).comp (measurable_Zvec i)

lemma sInf_eq_iff (S : Set ℕ) (m : ℕ) :
    sInf S = m ↔ (m ∈ S ∧ ∀ i < m, i ∉ S) ∨ ((∀ i, i ∉ S) ∧ m = 0) := by
  constructor
  · intro h
    by_cases hS : S.Nonempty
    · left; subst h
      exact ⟨Nat.sInf_mem hS, fun i hi => Nat.notMem_of_lt_sInf hi⟩
    · right
      have hS' : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
      refine ⟨fun i hi => by rw [hS'] at hi; exact hi, ?_⟩
      rw [← h, hS', Nat.sInf_empty]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · apply le_antisymm (Nat.sInf_le h1)
      by_contra hlt; push_neg at hlt
      exact h2 _ hlt (Nat.sInf_mem ⟨m, h1⟩)
    · have : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr h1
      rw [this, Nat.sInf_empty, h2]

lemma measurable_nextArr (τ : ℝ) : Measurable (fun x : XS n => nextArr x.1.1 τ) := by
  refine measurable_to_countable' (fun m => ?_)
  have : (fun x : XS n => nextArr x.1.1 τ) ⁻¹' {m} =
      ({x | τ < kappa x.1.1 m} ∩ ⋂ i, {x : XS n | i < m → ¬ τ < kappa x.1.1 i}) ∪
      ((⋂ i, {x : XS n | ¬ τ < kappa x.1.1 i}) ∩ {_x | m = 0}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, nextArr, sInf_eq_iff, Set.mem_setOf_eq,
      Set.mem_union, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine MeasurableSet.union (MeasurableSet.inter (measurableSet_lt measurable_const (measurable_kappa m))
    (MeasurableSet.iInter fun i => ?_)) (MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_)
  · by_cases h : i < m
    · simp only [h, true_implies]
      exact (measurableSet_lt measurable_const (measurable_kappa i)).compl
    · simp [h]
  · exact (measurableSet_lt measurable_const (measurable_kappa i)).compl
  · by_cases h : m = 0 <;> simp [h]

lemma measurableSet_inService (τ : ℝ) (i : ℕ) :
    MeasurableSet {x : XS n | inService x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ i} := by
  have hS : Measurable (fun x : XS n => (x.2 i).1) :=
    measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
  have hT : Measurable (fun x : XS n => (x.2 i).2) :=
    measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)
  simp only [inService, served, Set.setOf_and]
  refine MeasurableSet.inter ((measurable_nextArr τ) (MeasurableSet.of_discrete (s := {k | i < k})))
    (MeasurableSet.inter (measurableSet_le (measurable_wait i) hT)
      (MeasurableSet.inter (measurableSet_le ((measurable_kappa i).add (measurable_wait i)) measurable_const)
        (measurableSet_lt measurable_const (((measurable_kappa i).add (measurable_wait i)).add hS))))

lemma measurableSet_inQueue (τ : ℝ) (i : ℕ) :
    MeasurableSet {x : XS n | inQueue x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ i} := by
  have hT : Measurable (fun x : XS n => (x.2 i).2) :=
    measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)
  simp only [inQueue, Set.setOf_and]
  exact MeasurableSet.inter ((measurable_nextArr τ) (MeasurableSet.of_discrete (s := {k | i < k})))
    (measurableSet_lt (measurable_const.sub (measurable_kappa i)) (hT.min (measurable_wait i)))

lemma measList_remaining (τ : ℝ) :
    MeasList (fun x : XS n => remainingList x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ) := by
  unfold remainingList
  refine MeasList.append ?_ ?_
  · have e : ∀ x : XS n, ((List.ofFn x.1.2).filter (fun r => decide (τ < r))).map (fun r => r - τ) =
        ((List.finRange n).filter (fun k => decide (τ < x.1.2 k))).map (fun k => x.1.2 k - τ) := by
      intro x
      rw [List.ofFn_eq_map, List.filter_map, List.map_map]
      rfl
    simp_rw [e]
    exact MeasList.filterMap (List.finRange n) (fun k (x : XS n) => τ < x.1.2 k)
      (fun k => measurableSet_lt measurable_const ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)))
      (fun k (x : XS n) => x.1.2 k - τ)
      (fun k => ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)).sub_const _)
  · exact MeasList.piecewise (measurable_nextArr τ) (fun m x => ((List.range m).filter
        (fun i => decide (inService x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ i))).map
        (fun i => kappa x.1.1 i + wait x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) i
          + (x.2 i).1 - τ))
      (fun m => MeasList.filterMap (List.range m) _ (fun i => measurableSet_inService τ i) _
        (fun i => (((measurable_kappa i).add (measurable_wait i)).add
          (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).sub_const _))

lemma measList_waiting (τ : ℝ) :
    MeasList (fun x : XS n => waitingList x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ) := by
  unfold waitingList
  exact MeasList.piecewise (measurable_nextArr τ) (fun m x => ((List.range m).filter
        (fun i => decide (inQueue x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ i))).map
        (fun i => τ - kappa x.1.1 i))
      (fun m => MeasList.filterMap (List.range m) _ (fun i => measurableSet_inQueue τ i) _
        (fun i => measurable_const.sub (measurable_kappa i)))

lemma measurable_pathX_at (τ : NNReal) :
    Measurable (fun x : XS n => pathX x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ) := by
  have hL := measList_remaining (n := n) τ
  have hW := measList_waiting (n := n) τ
  have hU := (MeasList.replicate (measurable_of_nat hL.len (n - ·))).append hL.mergeSort
  have hB : Measurable (fun x : XS n => kappa x.1.1 (nextArr x.1.1 τ) - τ) :=
    (measurable_piecewise_nat (measurable_nextArr τ) (fun m x => kappa x.1.1 m)
      (fun m => measurable_kappa m)).sub_const _
  unfold pathX
  exact hL.len.prodMk (hW.len.prodMk ((measurable_pi_lambda _ fun (j : Fin n) => hU.get (j : ℕ)).prodMk
    ((measurable_pi_lambda _ fun j => hW.get j).prodMk hB)))

lemma measurable_Phi :
    Measurable (fun x : XS n => fun τ : NNReal =>
      pathX x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ) :=
  measurable_pi_lambda _ (fun τ => measurable_pathX_at τ)

end DDM

namespace DDM
open MeasureTheory ProbabilityTheory DelayDep.Equiv

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

def Psi (E : ExoSystem n f P) (ω : Ω) : XS n :=
  (((fun i => E.α i ω), E.u ω), fun i => (E.S i ω, E.T i ω))

lemma measurable_Psi (E : ExoSystem n f P) : Measurable (Psi E) :=
  ((measurable_pi_lambda _ E.measurable_α).prodMk E.measurable_u).prodMk
    (measurable_pi_lambda _ fun i => (E.measurable_S i).prodMk (E.measurable_T i))

lemma path_eq (E : ExoSystem n f P) :
    E.path = (fun x : XS n => fun τ : NNReal =>
      pathX x.1.1 x.1.2 (fun i => (x.2 i).2) (fun i _ => (x.2 i).1) τ) ∘ Psi E := rfl

lemma map_Psi [IsProbabilityMeasure P] (E : ExoSystem n f P) :
    P.map (Psi E) = (E.inputLaw P).prod
      (Measure.infinitePi (fun i => P.map (fun ω => (E.S i ω, E.T i ω)))) := by
  have hin : Measurable (fun ω => ((fun i => E.α i ω), E.u ω)) :=
    (measurable_pi_lambda _ E.measurable_α).prodMk E.measurable_u
  have hcu : Measurable (fun ω i => (E.S i ω, E.T i ω)) :=
    measurable_pi_lambda _ fun i => (E.measurable_S i).prodMk (E.measurable_T i)
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hin.aemeasurable hcu.aemeasurable).mp E.indep_inputs
  have h2 := E.indep_customers.map_fun_eq_infinitePi_map
    (fun i => (E.measurable_S i).prodMk (E.measurable_T i))
  unfold Psi Inputs.inputLaw
  rw [h1, h2]

end DDM

open MeasureTheory ProbabilityTheory DelayDep.Equiv DDM in
theorem solution (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f)
    (n : ℕ) [NeZero n] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (E₁ : ExoSystem n f P) (E₂ : ExoSystem n f P')
    (h_input : E₁.inputLaw P = E₂.inputLaw P') :
    AEMeasurable E₁.path P ∧ AEMeasurable E₂.path P' ∧ P.map E₁.path = P'.map E₂.path := by
  have hΦ := measurable_Phi (n := n)
  refine ⟨?_, ?_, ?_⟩
  · rw [path_eq]; exact (hΦ.comp (measurable_Psi E₁)).aemeasurable
  · rw [path_eq]; exact (hΦ.comp (measurable_Psi E₂)).aemeasurable
  · rw [path_eq, path_eq, ← Measure.map_map hΦ (measurable_Psi E₁),
      ← Measure.map_map hΦ (measurable_Psi E₂), map_Psi, map_Psi, h_input]
    congr 3
    funext i
    rw [E₁.law_ST i, E₂.law_ST i]
