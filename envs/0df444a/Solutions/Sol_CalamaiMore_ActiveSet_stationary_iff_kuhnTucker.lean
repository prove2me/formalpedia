-- Prove2me | solution 1 for CalamaiMore.ActiveSet.stationary_iff_kuhnTucker
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:53:37.168237+00:00
-- url     : https://prove2.me/submissions/07f459fe-ea9f-4c75-ad93-1ec19c396aea

import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic
import Definitions.Def_CalamaiMore_ActiveSet_projGrad
import Definitions.Def_CalamaiMore_ActiveSet_bindingSet
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
open Set Filter Topology

private theorem cone_reduce {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S,0 < a i) :
    ∃ T : Finset ι,T ⊆ S ∧ LinearIndependent ℝ (fun i : T => c i) ∧
      ∃ q : ι → ℝ,(∀ i ∈ T,0 ≤ q i) ∧
        ∑ i ∈ T,q i • c i = ∑ i ∈ S,a i • c i := by
  classical
  induction S using Finset.strongInductionOn generalizing a with
  | _ S ih =>
    by_cases hli : LinearIndependent ℝ (fun i : S => c i)
    · exact ⟨S,Finset.Subset.refl _,hli,a,fun i hi => (ha i hi).le,rfl⟩
    have hdep : ¬ LinearIndepOn ℝ c (S : Set ι) := hli
    rw [linearIndepOn_finset_iff] at hdep
    push_neg at hdep
    obtain ⟨b,hb,j,hj,hbj⟩:=hdep
    have hbpos : ∃ b : ι → ℝ,(∑ i ∈ S,b i • c i)=0 ∧ ∃ j ∈ S,0 < b j := by
      rcases lt_or_gt_of_ne hbj with hneg | hpos
      · refine ⟨fun i => -b i,?_,j,hj,by linarith⟩
        simp only [neg_smul,Finset.sum_neg_distrib,hb,neg_zero]
      · exact ⟨b,hb,j,hj,hpos⟩
    obtain ⟨b,hb,j,hj,hbj⟩:=hbpos
    let P := S.filter (fun i => 0 < b i)
    have hP : P.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨hj,hbj⟩⟩
    obtain ⟨j,hjP,hmin⟩:=Finset.exists_min_image P (fun i => a i/b i) hP
    have hj:= (Finset.mem_filter.mp hjP).1
    have hbj:=(Finset.mem_filter.mp hjP).2
    let t := a j/b j
    have ht : 0 < t := div_pos (ha j hj) hbj
    let d : ι → ℝ := fun i => a i-t*b i
    have hd : ∀ i ∈ S,0 ≤ d i := by
      intro i hi
      by_cases hbipos : 0 < b i
      · have hh:=hmin i (Finset.mem_filter.mpr ⟨hi,hbipos⟩)
        have hh' : t*b i ≤ a i := (le_div_iff₀ hbipos).mp hh
        dsimp [d]; linarith
      · have hh : t*b i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hbipos)
        dsimp [d]; linarith [ha i hi]
    have hdj : d j=0 := by dsimp [d,t]; field_simp; ring
    let U := S.filter (fun i => 0 < d i)
    have hUS : U ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩
      intro he
      have hh : j ∈ U := he.symm ▸ hj
      have := (Finset.mem_filter.mp hh).2
      rw [hdj] at this
      exact lt_irrefl _ this
    obtain ⟨T,hTU,hTI,q,hq,he⟩:=ih U hUS d (fun i hi => (Finset.mem_filter.mp hi).2)
    refine ⟨T,hTU.trans (Finset.filter_subset _ _),hTI,q,hq,?_⟩
    rw [he]
    calc
      ∑ i ∈ U,d i • c i = ∑ i ∈ S,d i • c i := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hni
        have hle : d i ≤ 0 := by
          by_contra! hh
          exact hni (Finset.mem_filter.mpr ⟨hi,hh⟩)
        rw [le_antisymm hle (hd i hi),zero_smul]
      _ = ∑ i ∈ S,a i • c i-t • (∑ i ∈ S,b i • c i) := by
        simp only [d,sub_smul,mul_smul,Finset.sum_sub_distrib,Finset.smul_sum]
      _ = ∑ i ∈ S,a i • c i := by rw [hb,smul_zero,sub_zero]


private theorem finite_cone_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) :
    IsClosed {y : E | ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ y=∑ i,a i • c i} := by
  classical
  let D (T : Finset ι) : Set E :=
    if LinearIndependent ℝ (fun i : T => c i) then
      (Fintype.linearCombination ℝ (fun i : T => c i)) '' {a : T → ℝ | ∀ i,0 ≤ a i}
    else ∅
  have hD : ∀ T,IsClosed (D T) := by
    intro T
    dsimp [D]
    split_ifs with hli
    · have hi := LinearMap.isClosedEmbedding_of_injective
        (LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp hli))
      apply hi.isClosedMap _
      simp only [setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_empty
  have he : {y : E | ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ y=∑ i,a i • c i} = ⋃ T,D T := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      let S := Finset.univ.filter (fun i => 0<a i)
      obtain ⟨T,hTS,hli,q,hq,heq⟩:=cone_reduce c S a (fun i hi => (Finset.mem_filter.mp hi).2)
      have heq' : ∑ i ∈ T,q i • c i = ∑ i,a i • c i := by
        rw [heq]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hh : a i=0 := by
          apply le_antisymm _ (ha i)
          by_contra! hh
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
        rw [hh,zero_smul]
      apply Set.mem_iUnion.mpr
      refine ⟨T,?_⟩
      dsimp [D]
      rw [if_pos hli]
      refine ⟨fun i => q i,fun i => hq i i.property,?_⟩
      change (∑ i : T,q i • c i)=_
      exact (Finset.sum_coe_sort T (fun i => q i • c i)).trans heq'
    · intro hy
      obtain ⟨T,hT⟩:=Set.mem_iUnion.mp hy
      dsimp [D] at hT
      split_ifs at hT with hli
      · obtain ⟨a,ha,rfl⟩:=hT
        refine ⟨fun i => if hi : i∈T then a ⟨i,hi⟩ else 0,?_,?_⟩
        · intro i; dsimp; split_ifs <;> simp_all
        · simp only [Fintype.linearCombination_apply]
          let q : ι → ℝ := fun i => if hi : i∈T then a ⟨i,hi⟩ else 0
          change (∑ i : T,a i • c i)=∑ i,q i • c i
          calc
            (∑ i : T,a i • c i) = ∑ i : T,q i • c i := by simp [q]
            _ = ∑ i ∈ T,q i • c i := Finset.sum_coe_sort T (fun i => q i • c i)
            _ = ∑ i,q i • c i := Finset.sum_subset (Finset.subset_univ _) (by
              intro i _ hi
              simp [q,hi])
      · exact False.elim hT
  rw [he]
  exact isClosed_iUnion_of_finite hD


private theorem finite_farkas {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (c : ι → E) (g : E)
    (hg : ∀ v : E,(∀ i,0 ≤ inner ℝ (c i) v) → 0 ≤ inner ℝ g v) :
    ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ g=∑ i,a i • c i := by
  classical
  let C : ProperCone ℝ E := {
    carrier := {y : E | ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ y=∑ i,a i • c i}
    zero_mem' := ⟨0,by simp,by simp⟩
    add_mem' := by
      rintro x y ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
      refine ⟨a+b,fun i => add_nonneg (ha i) (hb i),?_⟩
      simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    smul_mem' := by
      rintro r x ⟨a,ha,rfl⟩
      refine ⟨fun i => (r:ℝ)*a i,fun i => mul_nonneg r.property (ha i),?_⟩
      change (r:ℝ) • (∑ i,a i • c i)=_
      simp only [Finset.smul_sum,mul_smul]
    isClosed' := finite_cone_closed c }
  change g∈C
  by_contra hn
  obtain ⟨v,hv,hgv⟩:=C.hyperplane_separation' hn
  have hci : ∀ i,0 ≤ inner ℝ (c i) v := by
    intro i
    apply hv _
    refine ⟨fun j => if j=i then 1 else 0,?_,?_⟩
    · intro j; dsimp; split_ifs <;> norm_num
    · simp
  exact (not_lt_of_ge (hg v hci)) hgv
open Set Filter Topology Module
open CalamaiMore.ActiveSet CalamaiMore.Shared

private theorem active_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x : E) (j : Fin m) :
    j ∈ activeSet c δ x ↔ inner ℝ (c j) x=δ j := by simp [activeSet]

private theorem direction_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x v : E) (hx : x ∈ polyhedron c δ)
    (hv : ∀ j ∈ activeSet c δ x,0 ≤ inner ℝ (c j) v) :
    v ∈ feasibleDirections (polyhedron c δ) x := by
  change ∀ᶠ t in 𝓝[>] (0:ℝ),∀ j,δ j ≤ inner ℝ (c j) (x+t • v)
  rw [eventually_all]
  intro j
  by_cases hj : j ∈ activeSet c δ x
  · have he:=(active_mem c δ x j).mp hj
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [inner_add_right,real_inner_smul_right,he]
    exact le_add_of_nonneg_right (mul_nonneg (show 0 ≤ t from le_of_lt ht) (hv j hj))
  · have hstrict : δ j < inner ℝ (c j) x := lt_of_le_of_ne (hx j)
      (Ne.symm (fun he => hj ((active_mem c δ x j).mpr he)))
    have hc : Continuous (fun t : ℝ => inner ℝ (c j) (x+t • v)) := by fun_prop
    have he : ∀ᶠ t in 𝓝 (0:ℝ),δ j < inner ℝ (c j) (x+t • v) :=
      hc.continuousAt.eventually (eventually_gt_nhds (by simpa using hstrict))
    exact (he.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hfd : ∀ x ∈ polyhedron c δ, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (gradient f) (polyhedron c δ))
    (x : E) (hx : x ∈ polyhedron c δ) :
    CalamaiMore.Shared.IsStationaryPoint f (polyhedron c δ) x ↔ IsKuhnTuckerPoint c δ f x := by
  classical
  constructor
  · intro hs
    have hdual : ∀ v : E,(∀ j : activeSet c δ x,0 ≤ inner ℝ (c j) v) →
        0 ≤ inner ℝ (gradient f x) v := by
      intro v hv
      have hd := direction_feasible c δ x v hx (fun j hj => hv ⟨j,hj⟩)
      have htpos : ∀ᶠ t in 𝓝[>] (0:ℝ),0<t := self_mem_nhdsWithin
      change ∀ᶠ t in 𝓝[>] (0:ℝ),x+t • v∈polyhedron c δ at hd
      obtain ⟨t,ht,hf⟩:=(htpos.and hd).exists
      have hh:=hs.2 _ hf
      simp only [add_sub_cancel_left,real_inner_smul_right] at hh
      exact (mul_nonneg_iff_of_pos_left ht).mp hh
    obtain ⟨a,ha,he⟩:=finite_farkas (fun j : activeSet c δ x => c j) (gradient f x) hdual
    refine ⟨hx,fun j => if hj : j∈activeSet c δ x then a ⟨j,hj⟩ else 0,?_,?_⟩
    · rw [he]
      let q : Fin m → ℝ := fun j => if hj : j∈activeSet c δ x then a ⟨j,hj⟩ else 0
      change (∑ j : activeSet c δ x,a j • c j)=∑ j ∈ activeSet c δ x,q j • c j
      calc
        _ = ∑ j : activeSet c δ x,q j • c j := by simp [q]
        _ = _ := Finset.sum_coe_sort _ (fun j => q j • c j)
    · intro j hj
      dsimp
      rw [dif_pos hj]
      exact ha ⟨j,hj⟩
  · rintro ⟨hx,a,he,ha⟩
    refine ⟨hx,?_⟩
    intro z hz
    rw [he,sum_inner]
    apply Finset.sum_nonneg
    intro j hj
    rw [real_inner_smul_left,inner_sub_right,(active_mem c δ x j).mp hj]
    exact mul_nonneg (ha j hj) (sub_nonneg.mpr (hz j))

