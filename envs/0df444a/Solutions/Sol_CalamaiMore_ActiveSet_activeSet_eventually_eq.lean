-- Prove2me | solution 1 for CalamaiMore.ActiveSet.activeSet_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:46:31.373528+00:00
-- url     : https://prove2.me/submissions/7657ba3e-f117-4ce8-a204-8caad40bfabd

import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_CalamaiMore_QP_IsAlgorithm61Run
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic
import Definitions.Def_CalamaiMore_ActiveSet_projGrad
import Definitions.Def_CalamaiMore_ActiveSet_bindingSet
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.InnerProductSpace.Dual
open Set

private theorem nearest_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    CalamaiMore.Convergence.nearestPoint Ω y ∈ Ω ∧ ∀ w ∈ Ω,
      ‖CalamaiMore.Convergence.nearestPoint Ω y-y‖ ≤ ‖w-y‖ := by
  have he : ∃ z ∈ Ω,∀ w ∈ Ω,‖z-y‖ ≤ ‖w-y‖ := by
    obtain ⟨z,hz,hmin⟩:=exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv y
    refine ⟨z,hz,?_⟩
    intro w hw
    rw [norm_sub_rev z y,norm_sub_rev w y,hmin]
    exact ciInf_le (f:=fun w : Ω => ‖y-w‖) ⟨(0:ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩ ⟨w,hw⟩
  unfold CalamaiMore.Convergence.nearestPoint
  rw [dif_pos he]
  exact Classical.choose_spec he

private theorem nearest_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    ∀ w ∈ Ω, inner ℝ (y-CalamaiMore.Convergence.nearestPoint Ω y)
      (w-CalamaiMore.Convergence.nearestPoint Ω y) ≤ 0 := by
  letI : Nonempty Ω := hne.to_subtype
  obtain ⟨hp,hmin⟩:=nearest_spec Ω hne hc hv y
  apply (norm_eq_iInf_iff_real_inner_le_zero hv hp).mp
  apply le_antisymm
  · apply le_ciInf
    intro w
    simpa only [norm_sub_rev] using hmin w w.property
  · exact ciInf_le (f:=fun w : Ω => ‖y-w‖) ⟨(0:ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩ ⟨_,hp⟩

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

private theorem tangent_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x : E) (hx : x ∈ polyhedron c δ) :
    tangentCone (polyhedron c δ) x = {v | ∀ j ∈ activeSet c δ x,0 ≤ inner ℝ (c j) v} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro v hv j hj
      have he:=(active_mem c δ x j).mp hj
      have htpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t := self_mem_nhdsWithin
      change ∀ᶠ t in 𝓝[>] (0:ℝ),x+t • v∈polyhedron c δ at hv
      obtain ⟨t,ht,hfeas⟩:=(htpos.and hv).exists
      have hh:=hfeas j
      simp only [inner_add_right,real_inner_smul_right,he] at hh
      exact (mul_nonneg_iff_of_pos_left ht).mp (by linarith : 0 ≤ t*inner ℝ (c j) v)
    · simp only [setOf_forall]
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro hj
      exact isClosed_le continuous_const (show Continuous (fun v : E => inner ℝ (c j) v) from continuous_const.inner continuous_id)
  · intro v hv
    exact subset_closure (direction_feasible c δ x v hx hv)

private theorem tangent_closed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (x : E) : IsClosed (tangentCone Ω x) := isClosed_closure

private theorem tangent_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x : E) (hx : x ∈ polyhedron c δ) :
    Convex ℝ (tangentCone (polyhedron c δ) x) := by
  rw [tangent_eq c δ x hx]
  intro v hv w hw a b ha hb hab j hj
  simp only [inner_add_right,real_inner_smul_right]
  exact add_nonneg (mul_nonneg ha (hv j hj)) (mul_nonneg hb (hw j hj))

private theorem tangent_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x : E) (hx : x ∈ polyhedron c δ) :
    (0:E) ∈ tangentCone (polyhedron c δ) x := by
  rw [tangent_eq c δ x hx]
  simp

open Classical in
private theorem independent_dual_vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} (c : ι → E) (hli : LinearIndependent ℝ c) (j : ι) :
    ∃ v : E,∀ i,inner ℝ (c i) v=if i=j then -1 else 0 := by
  classical
  let b := Basis.span hli
  obtain ⟨g,hg⟩:=(b.coord j).exists_extend
  let v := -(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g)
  refine ⟨v,?_⟩
  intro i
  have he:=congrArg (fun F => F (b i)) hg
  simp only [LinearMap.comp_apply,Submodule.subtype_apply,Basis.coord_apply,Basis.repr_self_apply] at he
  have he' : g (c i)=if i=j then 1 else 0 := by simpa [b] using he
  dsimp [v]
  rw [inner_neg_right,real_inner_comm,InnerProductSpace.toDual_symm_apply]
  change -g (c i)=_
  rw [he']
  split_ifs <;> norm_num

private theorem active_eventually_subset {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) (x : ℕ → E) (xs : E)
    (hxs : xs ∈ polyhedron c δ) (hlim : Tendsto x atTop (𝓝 xs)) :
    ∀ᶠ k in atTop,activeSet c δ (x k) ⊆ activeSet c δ xs := by
  have he : ∀ j,∀ᶠ k in atTop,j ∈ activeSet c δ (x k) → j ∈ activeSet c δ xs := by
    intro j
    by_cases hj : j ∈ activeSet c δ xs
    · exact Filter.Eventually.of_forall fun _ _ => hj
    · have hstrict : δ j < inner ℝ (c j) xs := lt_of_le_of_ne (hxs j)
        (Ne.symm (fun he => hj ((active_mem c δ xs j).mpr he)))
      have hc : Tendsto (fun k => inner ℝ (c j) (x k)) atTop (𝓝 (inner ℝ (c j) xs)) :=
        tendsto_const_nhds.inner hlim
      filter_upwards [(tendsto_order.mp hc).1 (δ j) hstrict] with k hk hactive
      have he:=(active_mem c δ (x k) j).mp hactive
      linarith
  exact eventually_all.mpr he
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hfd : ∀ x ∈ polyhedron c δ, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (gradient f) (polyhedron c δ))
    (x : ℕ → E) (xs : E) (hx : ∀ k, x k ∈ polyhedron c δ)
    (hlim : Filter.Tendsto x Filter.atTop (nhds xs))
    (hpg : Filter.Tendsto (fun k => ‖projGrad f (polyhedron c δ) (x k)‖) Filter.atTop (nhds 0))
    (hnd : IsNondegenerate c δ f xs) :
    ∀ᶠ k in Filter.atTop, activeSet c δ (x k) = activeSet c δ xs := by
  classical
  have hgrad : Tendsto (fun k => gradient f (x k)) atTop (𝓝 (gradient f xs)) :=
    Filter.Tendsto.comp (f:=x) (g:=gradient f) (hfc xs hnd.1) (tendsto_nhdsWithin_iff.mpr ⟨hlim,Filter.Eventually.of_forall hx⟩)
  have hp : Tendsto (fun k => projGrad f (polyhedron c δ) (x k)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hpg
  have hsub:=active_eventually_subset c δ x xs hnd.1 hlim
  obtain ⟨lam,hlam,hpos⟩:=hnd.2.2
  have hback : ∀ j,∀ᶠ k in atTop,j ∈ activeSet c δ xs → j ∈ activeSet c δ (x k) := by
    intro j
    by_cases hj : j ∈ activeSet c δ xs
    · obtain ⟨v,hv⟩:=independent_dual_vector (fun i : activeSet c δ xs => c i) hnd.2.1 ⟨j,hj⟩
      have hv' : ∀ i ∈ activeSet c δ xs,inner ℝ (c i) v=if i=j then -1 else 0 := by
        intro i hi
        simpa only [Subtype.mk.injEq] using hv ⟨i,hi⟩
      have hg : inner ℝ (gradient f xs) v = -lam j := by
        rw [hlam,sum_inner]
        simp only [real_inner_smul_left]
        calc
          ∑ i ∈ activeSet c δ xs,lam i*inner ℝ (c i) v = ∑ i ∈ activeSet c δ xs,if i=j then -lam j else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hv' i hi]
            split_ifs with heq
            · subst i; ring
            · simp
          _ = -lam j := by simp [hj]
      have hl : Tendsto (fun k => inner ℝ
          (-gradient f (x k)-projGrad f (polyhedron c δ) (x k))
          (v-projGrad f (polyhedron c δ) (x k))) atTop (𝓝 (lam j)) := by
        have hh:=(hgrad.neg.sub hp).inner (𝕜:=ℝ) ((tendsto_const_nhds (x:=v)).sub hp)
        simpa only [sub_zero,inner_neg_left,hg,neg_neg] using hh
      have he:=(tendsto_order.mp hl).1 0 (hpos j hj)
      filter_upwards [he,hsub] with k hk hsubk _
      by_contra hjk
      have hvc : v ∈ tangentCone (polyhedron c δ) (x k) := by
        rw [tangent_eq c δ (x k) (hx k)]
        intro i hi
        rw [hv' i (hsubk hi),if_neg (by intro heq; subst i; exact hjk hi)]
      have hh:=nearest_inner (tangentCone (polyhedron c δ) (x k))
        ⟨0,tangent_zero c δ (x k) (hx k)⟩ (tangent_closed _ _) (tangent_convex c δ (x k) (hx k))
        (-gradient f (x k)) v hvc
      change inner ℝ (-gradient f (x k)-projGrad f (polyhedron c δ) (x k))
        (v-projGrad f (polyhedron c δ) (x k)) ≤ 0 at hh
      linarith
    · exact Filter.Eventually.of_forall fun _ h => (hj h).elim
  filter_upwards [hsub,eventually_all.mpr hback] with k h1 h2
  exact Finset.Subset.antisymm h1 h2
