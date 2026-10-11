-- Prove2me | solution 1 for Balinski61.Connectivity.graph_n_tuply_connected
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T03:13:14.125284+00:00
-- url     : https://prove2.me/submissions/9c87f5c3-4454-4d12-958e-662e29093e78

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron
import Definitions.Def_Balinski61_Connectivity_TuplyConnected

open scoped RealInnerProductSpace

-- BEGIN COMPLETE MODULE PolyBody
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

def polyBody (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}

lemma polyBody_convex (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (polyBody a b) := by
  intro x hx y hy s t hs ht hsum i
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    s*a i x+t*a i y ≤ s*b i+t*b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
    _ = b i := by rw [← add_mul,hsum,one_mul]

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyBody

-- BEGIN COMPLETE MODULE PolyTopology
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma polyBody_closed (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : IsClosed (polyBody a b) := by
  unfold polyBody
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (a i).continuous_of_finiteDimensional continuous_const

lemma strict_mem_interior (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) {x : E}
    (hx : ∀ i, a i x < b i) : x ∈ interior (polyBody a b) := by
  let U : Set E := {y | ∀ i, a i y < b i}
  have hU : IsOpen U := by
    simp only [U,Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (a i).continuous_of_finiteDimensional continuous_const
  have hsub : U ⊆ polyBody a b := fun y hy i => (hy i).le
  exact interior_maximal hsub hU hx

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyTopology

-- BEGIN COMPLETE MODULE PolyCoercive
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

noncomputable def positiveRowSum (a : ι → E →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  ∑ i, max 0 (a i x)

lemma positiveRowSum_continuous (a : ι → E →ₗ[ℝ] ℝ) : Continuous (positiveRowSum a) := by
  unfold positiveRowSum
  exact continuous_finsetSum _ fun i _ => continuous_const.max (a i).continuous_of_finiteDimensional

omit [FiniteDimensional ℝ E] in
lemma positiveRowSum_pos (a : ι → E →ₗ[ℝ] ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) {x : E} (hx : x≠0) : 0 < positiveRowSum a x := by
  have hn : 0 ≤ positiveRowSum a x := Finset.sum_nonneg fun i _ => le_max_left _ _
  by_contra hp
  have he : positiveRowSum a x=0 := le_antisymm (le_of_not_gt hp) hn
  apply hx
  apply hz
  intro i
  have hh : max 0 (a i x) ≤ positiveRowSum a x :=
    Finset.single_le_sum (fun j _ => le_max_left (0:ℝ) (a j x)) (Finset.mem_univ i)
  rw [he] at hh
  exact (le_max_right _ _).trans hh

omit [FiniteDimensional ℝ E] in
lemma positiveRowSum_smul (a : ι → E →ₗ[ℝ] ℝ) {c : ℝ} (hc : 0≤c) (x : E) :
    positiveRowSum a (c • x) = c * positiveRowSum a x := by
  simp only [positiveRowSum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ hc,mul_zero]

lemma positiveRowSum_coercive [Nontrivial E] (a : ι → E →ₗ[ℝ] ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x, δ*‖x‖ ≤ positiveRowSum a x := by
  obtain ⟨u,hu⟩ := exists_norm_eq (E:=E) (show (0:ℝ)≤1 by norm_num)
  have hne : (Metric.sphere (0:E) 1).Nonempty := ⟨u,by simpa using hu⟩
  obtain ⟨v,hv,hmin⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn hne
    (positiveRowSum_continuous a).continuousOn
  have hvn : ‖v‖=1 := by simpa using hv
  have hv0 : v≠0 := by intro h; simp [h] at hvn
  refine ⟨positiveRowSum a v,positiveRowSum_pos a hz hv0,fun x => ?_⟩
  by_cases hx : x=0
  · subst x; simp [positiveRowSum]
  have hxn : 0<‖x‖ := norm_pos_iff.mpr hx
  have hw : (‖x‖⁻¹:ℝ) • x ∈ Metric.sphere (0:E) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hxn]
    exact inv_mul_cancel₀ hxn.ne'
  have hh : positiveRowSum a v ≤ positiveRowSum a ((‖x‖⁻¹:ℝ) • x) := hmin hw
  rw [positiveRowSum_smul a (inv_nonneg.mpr hxn.le)] at hh
  have hh' := mul_le_mul_of_nonneg_right hh hxn.le
  field_simp at hh'
  exact hh'

lemma polyBody_bounded (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) : Bornology.IsBounded (polyBody a b) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · apply isBounded_iff_forall_norm_le.mpr
    exact ⟨0,fun x _ => by rw [Subsingleton.elim x 0,norm_zero]⟩
  obtain ⟨δ,hδ,hbound⟩ := positiveRowSum_coercive a hz
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(∑ i, max 0 (b i))/δ,fun x hx => ?_⟩
  apply (le_div_iff₀ hδ).mpr
  have hh : positiveRowSum a x ≤ ∑ i,max 0 (b i) :=
    Finset.sum_le_sum fun i _ => max_le_max le_rfl (hx i)
  nlinarith [hbound x]

lemma polyBody_compact (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) : IsCompact (polyBody a b) :=
  Metric.isCompact_of_isClosed_isBounded (polyBody_closed a b) (polyBody_bounded a b hz)

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyCoercive

-- BEGIN COMPLETE MODULE FiniteSlack
section

open Set Filter
open scoped Topology

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v d : E}

lemma feasible_direction_nhds (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d≤0) :
    ∀ᶠ t : ℝ in 𝓝 0, 0≤t → v+t • d ∈ polyBody a b := by
  have hh : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0≤t → a i (v+t • d)≤b i := by
    intro i
    by_cases hi : a i v=b i
    · exact Eventually.of_forall fun t ht=>by
        simp only [map_add,map_smul,smul_eq_mul,hi]
        exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht (hd i hi))
    · have hlt : a i v<b i := lt_of_le_of_ne (hv i) hi
      have hc : Tendsto (fun t : ℝ=>a i v+t*a i d) (𝓝 0) (𝓝 (a i v)) := by
        have hcont : Continuous (fun t : ℝ=>a i v+t*a i d) := by fun_prop
        simpa only [zero_mul,add_zero] using hcont.tendsto 0
      filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
      intro _
      simpa only [map_add,map_smul,smul_eq_mul] using ht.le
  filter_upwards [eventually_all.mpr hh] with t ht hpos i
  exact ht i hpos

lemma feasible_direction_step (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d≤0) :
    ∃ t : ℝ, 0<t ∧ v+t • d ∈ polyBody a b := by
  obtain ⟨t,ht,hf⟩ := (feasible_direction_nhds hv hd).exists_gt
  exact ⟨t,ht,hf ht.le⟩

lemma feasible_kernel_nhds (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d=0) :
    ∀ᶠ t : ℝ in 𝓝 0, v+t • d ∈ polyBody a b := by
  apply eventually_all.mpr
  intro i
  by_cases hi : a i v=b i
  · exact Eventually.of_forall fun t=>by simp [map_add,map_smul,hi,hd i hi]
  · have hlt : a i v<b i := lt_of_le_of_ne (hv i) hi
    have hc : Tendsto (fun t : ℝ=>a i v+t*a i d) (𝓝 0) (𝓝 (a i v)) := by
      have hcont : Continuous (fun t : ℝ=>a i v+t*a i d) := by fun_prop
      simpa only [zero_mul,add_zero] using hcont.tendsto 0
    filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
    simpa only [map_add,map_smul,smul_eq_mul] using ht.le

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE FiniteSlack

-- BEGIN COMPLETE MODULE VertexKernel
section

open Set Filter
open scoped Topology

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v : E}

lemma vertex_kernel_zero (hv : v ∈ (polyBody a b).extremePoints ℝ) {d : E}
    (hd : ∀ i, a i v=b i → a i d=0) : d=0 := by
  have hp := feasible_kernel_nhds hv.1 hd
  have hm := feasible_kernel_nhds hv.1 (d := -d) (fun i hi=>by simp [hd i hi])
  obtain ⟨t,ht,hplus,hminus⟩ := (hp.and hm).exists_gt
  have he : v+t • d=v := hv.2 hplus hminus (by
    simpa only [smul_neg,←sub_eq_add_neg] using mem_openSegment_add_sub (𝕜:=ℝ) v (t • d))
  exact (smul_eq_zero.mp (add_eq_left.mp he)).resolve_left ht.ne'

omit [Fintype ι] in
lemma mem_extremePoints_of_kernel_zero (hv : v ∈ polyBody a b)
    (hk : ∀ d : E, (∀ i, a i v=b i → a i d=0) → d=0) :
    v ∈ (polyBody a b).extremePoints ℝ := by
  refine ⟨hv,?_⟩
  intro x hx y hy hseg
  obtain ⟨s,t,hs,ht,hst,he⟩ := hseg
  apply sub_eq_zero.mp
  apply hk
  intro i hi
  have he' := congrArg (a i) he
  simp only [map_add,map_smul,smul_eq_mul,hi] at he'
  have hx' := hx i
  have hy' := hy i
  have hex : a i x=b i := by
    have hm := mul_le_mul_of_nonneg_left hy' ht.le
    have hsum : s*b i+t*b i=b i := by rw [←add_mul,hst,one_mul]
    apply le_antisymm hx'
    apply (mul_le_mul_iff_right₀ hs).mp
    linarith
  simp only [map_sub,hex,hi,sub_self]

lemma vertex_iff_kernel_zero (hv : v ∈ polyBody a b) :
    v ∈ (polyBody a b).extremePoints ℝ ↔
      ∀ d : E, (∀ i, a i v=b i → a i d=0) → d=0 :=
  ⟨fun h _ hd=>vertex_kernel_zero h hd,mem_extremePoints_of_kernel_zero hv⟩

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE VertexKernel

-- BEGIN COMPLETE MODULE ConeSlice
section

open Set
open scoped BigOperators

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

noncomputable def coneHeight (a : ι → E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] ℝ := -∑ i,a i

def sliceRows (a : ι → E →ₗ[ℝ] ℝ) (h : E →ₗ[ℝ] ℝ) : ι ⊕ Bool → E →ₗ[ℝ] ℝ
  | .inl i => a i
  | .inr true => h
  | .inr false => -h

def sliceBounds : ι ⊕ Bool → ℝ
  | .inl _ => 0
  | .inr true => 1
  | .inr false => -1

noncomputable def coneSlice (a : ι → E →ₗ[ℝ] ℝ) : Set E :=
  polyBody (sliceRows a (coneHeight a)) sliceBounds

omit [FiniteDimensional ℝ E] in
lemma coneHeight_apply (a : ι → E →ₗ[ℝ] ℝ) (d : E) : coneHeight a d = -∑ i,a i d := by
  simp [coneHeight]

omit [FiniteDimensional ℝ E] in
lemma mem_coneSlice (a : ι → E →ₗ[ℝ] ℝ) (d : E) :
    d ∈ coneSlice a ↔ (∀ i,a i d≤0) ∧ coneHeight a d=1 := by
  constructor
  · intro hd
    have h1 := hd (.inr true)
    have h2 := hd (.inr false)
    change coneHeight a d≤1 at h1
    change -coneHeight a d≤ -1 at h2
    exact ⟨fun i=>hd (.inl i),by linarith⟩
  · rintro ⟨hd,hh⟩ (i|v)
    · exact hd i
    · cases v <;> simp [sliceRows,sliceBounds,hh]

omit [FiniteDimensional ℝ E] in
lemma coneHeight_nonneg (a : ι → E →ₗ[ℝ] ℝ) {d : E} (hd : ∀ i,a i d≤0) :
    0≤coneHeight a d := by
  rw [coneHeight_apply]
  exact neg_nonneg.mpr (Finset.sum_nonpos fun i _=>hd i)

omit [FiniteDimensional ℝ E] in
lemma coneHeight_eq_zero (a : ι → E →ₗ[ℝ] ℝ)
    (hk : ∀ d : E,(∀ i,a i d=0)→d=0) {d : E}
    (hd : ∀ i,a i d≤0) (hh : coneHeight a d=0) : d=0 := by
  apply hk
  have hs : (∑ i,a i d)=0 := by rw [coneHeight_apply] at hh; linarith
  exact fun i=>(Finset.sum_eq_zero_iff_of_nonpos (fun j _=>hd j)).mp hs i (Finset.mem_univ i)

lemma coneSlice_compact (a : ι → E →ₗ[ℝ] ℝ)
    (hk : ∀ d : E,(∀ i,a i d=0)→d=0) : IsCompact (coneSlice a) := by
  apply polyBody_compact
  intro d hd
  have h1 := hd (.inr true)
  have h2 := hd (.inr false)
  change coneHeight a d≤0 at h1
  change -coneHeight a d≤0 at h2
  exact coneHeight_eq_zero a hk (fun i=>hd (.inl i)) (by linarith)

omit [FiniteDimensional ℝ E] in
lemma coneSlice_normalize (a : ι → E →ₗ[ℝ] ℝ)
    (hk : ∀ d : E,(∀ i,a i d=0)→d=0) {d : E}
    (hd : ∀ i,a i d≤0) (hne : d≠0) :
    0<coneHeight a d ∧ (coneHeight a d)⁻¹ • d ∈ coneSlice a := by
  have hp : 0<coneHeight a d := lt_of_le_of_ne (coneHeight_nonneg a hd)
    (Ne.symm (fun h=>hne (coneHeight_eq_zero a hk hd h)))
  refine ⟨hp,(mem_coneSlice a _).mpr ⟨?_,?_⟩⟩
  · intro i
    simp only [map_smul,smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hp.le) (hd i)
  · simp [map_smul,smul_eq_mul,hp.ne']

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE ConeSlice

-- BEGIN COMPLETE MODULE ExtremeMaximizer
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_extreme_max {S : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    (c : E →ₗ[ℝ] ℝ) : ∃ d ∈ S.extremePoints ℝ, ∀ x∈S,c x≤c d := by
  obtain ⟨z,hz,hmax⟩ := hS.exists_isMaxOn hne c.continuous_of_finiteDimensional.continuousOn
  let F : Set E := {x∈S | ∀ y∈S,c y≤c x}
  have hF : F.Nonempty := ⟨z,hz,hmax⟩
  have hex : IsExposed ℝ S F := by
    intro _
    exact ⟨⟨c,c.continuous_of_finiteDimensional⟩,rfl⟩
  have hcomp : IsCompact F := hS.of_isClosed_subset (hex.isClosed hS.isClosed) (fun x hx=>hx.1)
  obtain ⟨d,hd⟩ := hcomp.extremePoints_nonempty hF
  exact ⟨d,hex.isExtreme.extremePoints_subset_extremePoints hd,hd.1.2⟩

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE ExtremeMaximizer

-- BEGIN COMPLETE MODULE SliceVertexRay
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ}

omit [FiniteDimensional ℝ E] in
lemma slice_vertex_ray {d : E} (hd : d ∈ (coneSlice a).extremePoints ℝ) {e : E}
    (he : ∀ i,a i d=0 → a i e=0) : e=coneHeight a e • d := by
  have hd1 := ((mem_coneSlice a d).mp hd.1).2
  have hz : e-coneHeight a e • d=0 := by
    apply vertex_kernel_zero hd
    intro j hj
    cases j with
    | inl i =>
      change a i d=0 at hj
      change a i (e-coneHeight a e • d)=0
      simp only [map_sub,map_smul,smul_eq_mul,he i hj,hj,mul_zero,sub_self]
    | inr j =>
      cases j <;> simp [sliceRows,map_sub,map_smul,hd1]
  exact sub_eq_zero.mp hz

lemma exists_improving_slice_vertex (a : ι → E →ₗ[ℝ] ℝ)
    (hk : ∀ d : E,(∀ i,a i d=0)→d=0) (c : E →ₗ[ℝ] ℝ)
    {e : E} (he : ∀ i,a i e≤0) (hc : 0<c e) :
    ∃ d ∈ (coneSlice a).extremePoints ℝ, 0<c d := by
  have hne : e≠0 := by intro h; simp [h] at hc
  obtain ⟨hh,hs⟩ := coneSlice_normalize a hk he hne
  obtain ⟨d,hd,hmax⟩ := exists_extreme_max (coneSlice_compact a hk) ⟨_,hs⟩ c
  refine ⟨d,hd,lt_of_lt_of_le ?_ (hmax _ hs)⟩
  simpa only [map_smul,smul_eq_mul] using mul_pos (inv_pos.mpr hh) hc

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE SliceVertexRay

-- BEGIN COMPLETE MODULE TangentDirection
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v : E}

noncomputable def tangentRows (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (v : E) : ι → E →ₗ[ℝ] ℝ :=
  fun i => if a i v=b i then a i else 0

omit [FiniteDimensional ℝ E] in
lemma tangent_kernel (hv : v ∈ (polyBody a b).extremePoints ℝ) {d : E}
    (hd : ∀ i,tangentRows a b v i d=0) : d=0 := by
  apply vertex_kernel_zero hv
  intro i hi
  simpa [tangentRows,hi] using hd i

lemma improving_direction (hv : v ∈ (polyBody a b).extremePoints ℝ)
    (c : E →ₗ[ℝ] ℝ) {z : E} (hz : z ∈ polyBody a b) (hc : c v<c z) :
    ∃ d, 0<c d ∧ (∀ i,a i v=b i → a i d≤0) ∧
      ∀ e, (∀ i,a i v=b i → a i d=0 → a i e=0) →
        e=coneHeight (tangentRows a b v) e • d := by
  have he : ∀ i,tangentRows a b v i (z-v)≤0 := by
    intro i
    by_cases hi : a i v=b i
    · simpa [tangentRows,hi,map_sub] using sub_nonpos.mpr (hz i)
    · simp [tangentRows,hi]
  have hp : 0<c (z-v) := by simpa only [map_sub] using sub_pos.mpr hc
  obtain ⟨d,hd,hcd⟩ := exists_improving_slice_vertex (tangentRows a b v)
    (fun _ h=>tangent_kernel hv h) c he hp
  refine ⟨d,hcd,?_,?_⟩
  · intro i hi
    simpa [tangentRows,hi] using ((mem_coneSlice _ _).mp hd.1).1 i
  · intro e he
    apply slice_vertex_ray hd
    intro i hi
    by_cases hv' : a i v=b i
    · simp only [tangentRows,if_pos hv'] at hi ⊢
      exact he i hv' hi
    · simp [tangentRows,hv']

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE TangentDirection

-- BEGIN COMPLETE MODULE TightFace
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (J : Set ι)

def tightFace : Set E := {x | x∈polyBody a b ∧ ∀ i∈J,a i x=b i}

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma tightFace_extreme : IsExtreme ℝ (polyBody a b) (tightFace a b J) := by
  refine ⟨fun _ hx=>hx.1,?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx,?_⟩
  intro i hi
  obtain ⟨s,t,hs,ht,hst,he⟩ := hseg
  have he' := congrArg (a i) he
  simp only [map_add,map_smul,smul_eq_mul,hz.2 i hi] at he'
  have hm := mul_le_mul_of_nonneg_left (hy i) ht.le
  have hsum : s*b i+t*b i=b i := by rw [←add_mul,hst,one_mul]
  apply le_antisymm (hx i)
  apply (mul_le_mul_iff_right₀ hs).mp
  linarith

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma tightFace_convex : Convex ℝ (tightFace a b J) := by
  intro x hx y hy s t hs ht hst
  refine ⟨polyBody_convex a b hx.1 hy.1 hs ht hst,?_⟩
  intro i hi
  simp only [map_add,map_smul,smul_eq_mul,hx.2 i hi,hy.2 i hi]
  rw [←add_mul,hst,one_mul]

omit [Fintype ι] in
lemma tightFace_closed : IsClosed (tightFace a b J) := by
  apply (polyBody_closed a b).inter
  change IsClosed {x : E | ∀ i∈J,a i x=b i}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i=>isClosed_iInter fun _=>
    isClosed_eq (a i).continuous_of_finiteDimensional continuous_const

omit [Fintype ι] in
lemma tightFace_compact (hP : IsCompact (polyBody a b)) : IsCompact (tightFace a b J) :=
  hP.of_isClosed_subset (tightFace_closed a b J) (fun _ hx=>hx.1)

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE TightFace

-- BEGIN COMPLETE MODULE LineFaceSegment
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma extreme_line_parameter_nonneg {F : Set E} {v d w : E} {T s : ℝ}
    (hv : v ∈ F.extremePoints ℝ) (hw : w ∈ F) (hT : 0<T)
    (hew : w=v+T • d) (hx : v+s • d ∈ F) (hd : d≠0) : 0 ≤ s := by
  by_contra hn
  have hs : s<0 := lt_of_not_ge hn
  have hp : 0<T-s := by linarith
  have hsum : T/(T-s)+(-s)/(T-s)=1 := by field_simp; ring
  have hzero : T/(T-s)*s+(-s)/(T-s)*T=0 := by ring
  have he : (T/(T-s)) • (v+s • d)+((-s)/(T-s)) • w=v := by
    rw [hew]
    calc
      _ = (T/(T-s)+(-s)/(T-s)) • v+
          (T/(T-s)*s+(-s)/(T-s)*T) • d := by module
      _ = v := by rw [hsum,hzero]; simp
  have heq := hv.2 hx hw ⟨_,_,div_pos hT hp,div_pos (neg_pos.mpr hs) hp,hsum,he⟩
  have hz : s • d=0 := add_eq_left.mp heq
  exact hd ((smul_eq_zero.mp hz).resolve_left hs.ne)

lemma compact_extreme_line_segment {P F : Set E} (hF : IsCompact F) (hconv : Convex ℝ F)
    (hext : IsExtreme ℝ P F) {v d : E} (hv : v ∈ P.extremePoints ℝ)
    (hvF : v∈F) (hline : ∀x∈F,∃s:ℝ,x=v+s • d)
    (c : E →ₗ[ℝ] ℝ) (hd : 0<c d) (hbetter : ∃x∈F,c v<c x) :
    ∃w∈P.extremePoints ℝ, F=segment ℝ v w ∧ c v<c w := by
  obtain ⟨w,hw,hmax⟩ := exists_extreme_max hF ⟨v,hvF⟩ c
  have hwP := hext.extremePoints_subset_extremePoints hw
  obtain ⟨x,hx,hcx⟩ := hbetter
  have hcw : c v<c w := lt_of_lt_of_le hcx (hmax x hx)
  obtain ⟨T,hew⟩ := hline w hw.1
  have hcT : c w=c v+T*c d := by rw [hew,map_add,map_smul,smul_eq_mul]
  have hT : 0<T := by nlinarith
  have hd0 : d≠0 := by intro h; simp [h] at hd
  have hv' : v∈F.extremePoints ℝ := ⟨hvF,fun _ hx _ hy h=>hv.2 (hext.subset hx) (hext.subset hy) h⟩
  refine ⟨w,hwP,?_,hcw⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s,hes⟩ := hline x hx
    have hs : 0 ≤ s := extreme_line_parameter_nonneg hv' hw.1 hT hew (hes ▸ hx) hd0
    have hcs : c x=c v+s*c d := by rw [hes,map_add,map_smul,smul_eq_mul]
    have hsT : s≤T := by have := hmax x hx; nlinarith
    have hp : 0 ≤ s/T := div_nonneg hs hT.le
    have hp1 : s/T≤1 := (div_le_one hT).mpr hsT
    refine ⟨1-s/T,s/T,sub_nonneg.mpr hp1,hp,by ring,?_⟩
    rw [hew,hes]
    have hcoef : s/T*T=s := div_mul_cancel₀ s hT.ne'
    calc
      _ = ((1-s/T)+s/T) • v+(s/T*T) • d := by module
      _ = v+s • d := by rw [hcoef]; simp
  · exact hconv.segment_subset hvF hw.1

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE LineFaceSegment

-- BEGIN COMPLETE MODULE ImprovingEdge
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v : E}

lemma improving_edge (hP : IsCompact (polyBody a b))
    (hv : v∈(polyBody a b).extremePoints ℝ) (c : E →ₗ[ℝ] ℝ)
    (hbetter : ∃z∈polyBody a b,c v<c z) :
    ∃w∈(polyBody a b).extremePoints ℝ,
      Hirsch.Adj (polyBody a b) v w ∧ c v<c w := by
  obtain ⟨z,hz,hcz⟩ := hbetter
  obtain ⟨d,hcd,hd,hray⟩ := improving_direction hv c hz hcz
  let J : Set ι := {i | a i v=b i ∧ a i d=0}
  let F := tightFace a b J
  have hvF : v∈F := ⟨hv.1,fun _ hi=>hi.1⟩
  have hline : ∀x∈F,∃s:ℝ,x=v+s • d := by
    intro x hx
    refine ⟨coneHeight (tangentRows a b v) (x-v),?_⟩
    have he := hray (x-v) (fun i hi hid=>by
      simp only [map_sub,hx.2 i ⟨hi,hid⟩,hi,sub_self])
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  obtain ⟨t,ht,hvt⟩ := feasible_direction_step hv.1 hd
  have htF : v+t • d∈F := by
    refine ⟨hvt,?_⟩
    intro i hi
    simp only [map_add,map_smul,smul_eq_mul,hi.1,hi.2,mul_zero,add_zero]
  have hcv : c v<c (v+t • d) := by
    simp only [map_add,map_smul,smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos ht hcd)
  obtain ⟨w,hw,hseg,hcw⟩ := compact_extreme_line_segment
    (tightFace_compact a b J hP) (tightFace_convex a b J)
    (tightFace_extreme a b J) hv hvF hline c hcd ⟨_,htF,hcv⟩
  refine ⟨w,hw,⟨?_,?_⟩,hcw⟩
  · intro h
    exact (ne_of_lt hcw) (congrArg c h)
  · rw [←hseg]
    exact tightFace_extreme a b J

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE ImprovingEdge

-- BEGIN COMPLETE MODULE GraphAscent
section

open Set

namespace Balinski61.Connectivity.Proof

variable {V : Type*} {G : SimpleGraph V}

lemma reachable_induce_mono {U W : Set V} (hUW : U ⊆ W) {u v : U}
    (h : (G.induce U).Reachable u v) :
    (G.induce W).Reachable ⟨u,hUW u.property⟩ ⟨v,hUW v.property⟩ := by
  let f : G.induce U →g G.induce W :=
    ⟨fun x => ⟨x.val,hUW x.property⟩,fun {_ _} h => h⟩
  exact h.map f

lemma finite_reachable_max [Finite V] (f : V → ℝ)
    (hstep : ∀ v, (∃ z, f v < f z) → ∃ w, G.Adj v w ∧ f v < f w)
    (U : Set V) (hup : ∀ v ∈ U, ∀ w, f v < f w → w ∈ U) (v : U) :
    ∃ w : U, (∀ z, f z ≤ f w) ∧ (G.induce U).Reachable v w := by
  let R : Set U := {w | (G.induce U).Reachable v w}
  have hR : R.Nonempty := ⟨v,SimpleGraph.Reachable.rfl⟩
  obtain ⟨w,hw,hmax⟩ := Set.exists_max_image R (fun x : U => f x) (Set.toFinite R) hR
  refine ⟨w,?_,hw⟩
  intro z
  by_contra hz
  obtain ⟨y,hy,hfy⟩ := hstep w ⟨z,lt_of_not_ge hz⟩
  let y' : U := ⟨y,hup w w.property y hfy⟩
  have hadj : (G.induce U).Adj w y' := hy
  have hyr : y' ∈ R := hw.trans hadj.reachable
  have hh := hmax y' hyr
  exact (not_lt_of_ge hh) hfy

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE GraphAscent

-- BEGIN COMPLETE MODULE ExposingVertex
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ}

lemma exposing_vertex {v : E} (hv : v ∈ (polyBody a b).extremePoints ℝ) :
    ∃ c : E →ₗ[ℝ] ℝ, ∀ x ∈ polyBody a b,
      c x≤c v ∧ (c v≤c x → x=v) := by
  classical
  let I := Finset.univ.filter (fun i => a i v=b i)
  let c : E →ₗ[ℝ] ℝ := ∑ i ∈ I,a i
  have he (x : E) : c x = ∑ i ∈ I,a i x := by simp only [c,LinearMap.sum_apply]
  refine ⟨c,fun x hx => ?_⟩
  have hh (i : ι) (hi : i∈I) : a i x ≤ a i v := by
    have hv' : a i v=b i := (Finset.mem_filter.mp hi).2
    rw [hv']
    exact hx i
  have hle : c x≤c v := by rw [he,he]; exact Finset.sum_le_sum hh
  refine ⟨hle,fun hge => ?_⟩
  have hz : ∑ i ∈ I,(a i v-a i x)=0 := by
    rw [Finset.sum_sub_distrib,←he v,←he x]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sub_nonneg.mpr (hh i hi))).mp hz
  apply sub_eq_zero.mp
  apply vertex_kernel_zero hv
  intro i hi
  have hz' := hzero i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
  simp only [map_sub]
  linarith

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE ExposingVertex

-- BEGIN COMPLETE MODULE FiniteVertices
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)

lemma vertex_pattern_injective : Function.Injective
    (fun v : (polyBody a b).extremePoints ℝ => {i : ι | a i v=b i}) := by
  intro v w he
  change {i : ι | a i (v:E)=b i}={i : ι | a i (w:E)=b i} at he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply vertex_kernel_zero v.property
  intro i hi
  have hw : a i w=b i := by
    have hh : i ∈ {j : ι | a j (v:E)=b j} := hi
    rw [he] at hh
    exact hh
  simp only [map_sub,hi,hw,sub_self]

lemma polyBody_finite_vertices : ((polyBody a b).extremePoints ℝ).Finite := by
  have : Finite ((polyBody a b).extremePoints ℝ) :=
    Finite.of_injective _ (vertex_pattern_injective a b)
  exact Set.finite_coe_iff.mp this

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE FiniteVertices

-- BEGIN COMPLETE MODULE PolyGraphConnectivity
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ}

omit [FiniteDimensional ℝ E] in
lemma polyGraph_preconnected_of_improving
    (hstep : ∀ (v : (polyBody a b).extremePoints ℝ) (c : E →ₗ[ℝ] ℝ),
      (∃ z : (polyBody a b).extremePoints ℝ, c v < c z) →
      ∃ w : (polyBody a b).extremePoints ℝ,
        (polyGraph (polyBody a b)).Adj v w ∧ c v < c w) :
    (polyGraph (polyBody a b)).Preconnected := by
  let V := (polyBody a b).extremePoints ℝ
  have : Finite V := (polyBody_finite_vertices a b).to_subtype
  intro u v
  obtain ⟨c,hc⟩ := exposing_vertex v.property
  obtain ⟨w,hw,hr⟩ := finite_reachable_max
    (G := polyGraph (polyBody a b)) (fun x : V => c x)
    (fun x hx => hstep x c hx) Set.univ (by simp) ⟨u,Set.mem_univ u⟩
  have he : (w.val : E) = (v : E) :=
    (hc w.val w.val.property.1).2 (hw v)
  have he' : w.val=v := Subtype.ext he
  let incl : (polyGraph (polyBody a b)).induce (Set.univ : Set V) →g
      polyGraph (polyBody a b) := ⟨Subtype.val,fun {_ _} h => h⟩
  have hh := hr.map incl
  change (polyGraph (polyBody a b)).Reachable u w.val at hh
  rwa [he'] at hh

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyGraphConnectivity

-- BEGIN COMPLETE MODULE PolyFace
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

def faceRows (a : ι → E →ₗ[ℝ] ℝ) (c : E →ₗ[ℝ] ℝ) : Sum ι Bool → E →ₗ[ℝ] ℝ
  | .inl i => a i
  | .inr false => c
  | .inr true => -c

def faceBounds (b : ι → ℝ) (M : ℝ) : Sum ι Bool → ℝ
  | .inl i => b i
  | .inr false => M
  | .inr true => -M

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma face_body (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : E →ₗ[ℝ] ℝ) (M : ℝ) :
    polyBody (faceRows a c) (faceBounds b M) = {x ∈ polyBody a b | c x=M} := by
  ext x
  constructor
  · intro h
    refine ⟨fun i => h (.inl i),?_⟩
    have h1 := h (.inr false)
    have h2 := h (.inr true)
    change c x≤M at h1
    change -c x≤-M at h2
    linarith
  · rintro ⟨hx,he⟩ i
    rcases i with i | i
    · exact hx i
    · cases i <;> simp [faceRows,faceBounds,he]

lemma max_face_extreme {S : Set E} (c : E →ₗ[ℝ] ℝ) (M : ℝ)
    (hb : ∀ x∈S, c x≤M) : IsExtreme ℝ S {x∈S | c x=M} := by
  apply IsExposed.isExtreme
  intro hn
  let L : E →L[ℝ] ℝ := ⟨c,c.continuous_of_finiteDimensional⟩
  refine ⟨L,?_⟩
  ext x
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨hx,fun y hy => by change c y≤c x; rw [he]; exact hb y hy⟩
  · rintro ⟨hx,hmax⟩
    obtain ⟨z,hz,he⟩ := hn
    refine ⟨hx,le_antisymm (hb x hx) ?_⟩
    have hh := hmax z hz
    change c z≤c x at hh
    rwa [he] at hh

omit [Fintype ι] in
lemma face_compact (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : E →ₗ[ℝ] ℝ) (M : ℝ)
    (hc : IsCompact (polyBody a b)) : IsCompact (polyBody (faceRows a c) (faceBounds b M)) := by
  rw [face_body]
  exact hc.inter_right (isClosed_eq c.continuous_of_finiteDimensional continuous_const)

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyFace

-- BEGIN COMPLETE MODULE LevelConnectivity
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ}

lemma upper_level_preconnected (hc : IsCompact (polyBody a b))
    (c : E →ₗ[ℝ] ℝ) (r : ℝ)
    (hstep : ∀ (v : (polyBody a b).extremePoints ℝ),
      (∃ z : (polyBody a b).extremePoints ℝ, c v<c z) →
      ∃ w : (polyBody a b).extremePoints ℝ,
        (polyGraph (polyBody a b)).Adj v w ∧ c v<c w)
    (hface : ∀ M, (∀ x∈polyBody a b,c x≤M) →
      (polyGraph {x∈polyBody a b | c x=M}).Preconnected) :
    ((polyGraph (polyBody a b)).induce {v : (polyBody a b).extremePoints ℝ | r<c v}).Preconnected := by
  let S := polyBody a b
  let V := S.extremePoints ℝ
  let G := polyGraph S
  have : Finite V := (polyBody_finite_vertices a b).to_subtype
  intro u v
  obtain ⟨z,hz,hmax⟩ := exists_extreme_max hc ⟨u.val,u.val.property.1⟩ c
  let M := c z
  have hex : IsExtreme ℝ S {x∈S | c x=M} := max_face_extreme c M hmax
  obtain ⟨u',hu',hru⟩ := finite_reachable_max (G := G) (fun x : V => c x)
    hstep {v | r<c v} (by intro x hx y hxy; exact lt_trans hx hxy) u
  obtain ⟨v',hv',hrv⟩ := finite_reachable_max (G := G) (fun x : V => c x)
    hstep {v | r<c v} (by intro x hx y hxy; exact lt_trans hx hxy) v
  have heu : c (u'.val : E)=M := le_antisymm (hmax _ u'.val.property.1) (hu' ⟨z,hz⟩)
  have hev : c (v'.val : E)=M := le_antisymm (hmax _ v'.val.property.1) (hv' ⟨z,hz⟩)
  have hmu : r<M := heu ▸ u'.property
  have huf : (u'.val : E) ∈ ({x∈S | c x=M}).extremePoints ℝ := by
    rw [hex.extremePoints_eq]
    exact ⟨⟨u'.val.property.1,heu⟩,u'.val.property⟩
  have hvf : (v'.val : E) ∈ ({x∈S | c x=M}).extremePoints ℝ := by
    rw [hex.extremePoints_eq]
    exact ⟨⟨v'.val.property.1,hev⟩,v'.val.property⟩
  let incl : polyGraph {x∈S | c x=M} →g G.induce {v : V | r<c v} :=
    ⟨fun x => ⟨⟨x,hex.extremePoints_subset_extremePoints x.property⟩,
      by change r<c (x:E); rw [x.property.1.2]; exact hmu⟩,
      fun {_ _} h => ⟨h.1,hex.trans h.2⟩⟩
  have hr := (hface M hmax ⟨u'.val,huf⟩ ⟨v'.val,hvf⟩).map incl
  exact hru.trans (hr.trans hrv.symm)

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE LevelConnectivity

-- BEGIN COMPLETE MODULE PolyConnectivity
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ}

lemma polyGraph_preconnected (hc : IsCompact (polyBody a b)) :
    (polyGraph (polyBody a b)).Preconnected := by
  apply polyGraph_preconnected_of_improving
  intro v c hb
  obtain ⟨z,hz⟩ := hb
  obtain ⟨w,hw,ha,he⟩ := improving_edge hc v.property c ⟨z,z.property.1,hz⟩
  exact ⟨⟨w,hw⟩,ha,he⟩

lemma polyGraph_upper_preconnected (hc : IsCompact (polyBody a b))
    (c : E →ₗ[ℝ] ℝ) (r : ℝ) :
    ((polyGraph (polyBody a b)).induce
      {v : (polyBody a b).extremePoints ℝ | r<c v}).Preconnected := by
  apply upper_level_preconnected hc c r
  · intro v hb
    obtain ⟨z,hz⟩ := hb
    obtain ⟨w,hw,ha,he⟩ := improving_edge hc v.property c ⟨z,z.property.1,hz⟩
    exact ⟨⟨w,hw⟩,ha,he⟩
  · intro M _
    rw [←face_body]
    exact polyGraph_preconnected (face_compact a b c M hc)

lemma polyGraph_lower_preconnected (hc : IsCompact (polyBody a b))
    (c : E →ₗ[ℝ] ℝ) (r : ℝ) :
    ((polyGraph (polyBody a b)).induce
      {v : (polyBody a b).extremePoints ℝ | c v<r}).Preconnected := by
  have h := polyGraph_upper_preconnected hc (-c) (-r)
  have he : {v : (polyBody a b).extremePoints ℝ | -r < (-c) v} =
      {v : (polyBody a b).extremePoints ℝ | c v<r} := by
    ext v
    change -r < -(c v) ↔ c v<r
    exact neg_lt_neg_iff
  rw [he] at h
  exact h

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyConnectivity

-- BEGIN COMPLETE MODULE GraphDeletion
section

open Set

namespace Balinski61.Connectivity.Proof

variable {V : Type*} {G : SimpleGraph V}

lemma graph_deletion_connected (f : V → ℝ) (X : Set V)
    (hX : ∀ v∈X, f v=0) (v₀ : ↥(Xᶜ)) (hv₀ : f v₀=0)
    (hside : ∃ v, f v≠0)
    (hpos : (G.induce {v | 0<f v}).Preconnected)
    (hneg : (G.induce {v | f v<0}).Preconnected)
    (hup : ∀ v, f v=0 → (∃ w,0<f w) → ∃ w,G.Adj v w ∧ 0<f w)
    (hdown : ∀ v, f v=0 → (∃ w,f w<0) → ∃ w,G.Adj v w ∧ f w<0) :
    (G.induce Xᶜ).Connected := by
  have hpX : {v | 0<f v} ⊆ Xᶜ := by
    intro v hv hx
    have hh := hX v hx
    change 0<f v at hv
    linarith
  have hnX : {v | f v<0} ⊆ Xᶜ := by
    intro v hv hx
    have hh := hX v hx
    change f v<0 at hv
    linarith
  have hp (u : ↥(Xᶜ)) (hu : 0<f u) : (G.induce Xᶜ).Reachable u v₀ := by
    obtain ⟨w,hw,hwpos⟩ := hup v₀ hv₀ ⟨u,hu⟩
    have hreach := reachable_induce_mono hpX (hpos ⟨u,hu⟩ ⟨w,hwpos⟩)
    have hadj : (G.induce Xᶜ).Adj v₀ ⟨w,hpX hwpos⟩ := hw
    exact hreach.trans hadj.reachable.symm
  have hn (u : ↥(Xᶜ)) (hu : f u<0) : (G.induce Xᶜ).Reachable u v₀ := by
    obtain ⟨w,hw,hwneg⟩ := hdown v₀ hv₀ ⟨u,hu⟩
    have hreach := reachable_induce_mono hnX (hneg ⟨u,hu⟩ ⟨w,hwneg⟩)
    have hadj : (G.induce Xᶜ).Adj v₀ ⟨w,hnX hwneg⟩ := hw
    exact hreach.trans hadj.reachable.symm
  have hall (u : ↥(Xᶜ)) : (G.induce Xᶜ).Reachable u v₀ := by
    rcases lt_trichotomy (f u) 0 with hu | hu | hu
    · exact hn u hu
    · obtain ⟨w,hw⟩ := hside
      rcases lt_or_gt_of_ne hw with hw | hw
      · obtain ⟨z,hz,hzn⟩ := hdown u hu ⟨w,hw⟩
        have hadj : (G.induce Xᶜ).Adj u ⟨z,hnX hzn⟩ := hz
        exact hadj.reachable.trans (hn ⟨z,hnX hzn⟩ hzn)
      · obtain ⟨z,hz,hzp⟩ := hup u hu ⟨w,hw⟩
        have hadj : (G.induce Xᶜ).Adj u ⟨z,hpX hzp⟩ := hz
        exact hadj.reachable.trans (hp ⟨z,hpX hzp⟩ hzp)
    · exact hp u hu
  have : Nonempty ↥(Xᶜ) := ⟨v₀⟩
  exact ⟨fun u v => (hall u).trans (hall v).symm⟩

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE GraphDeletion

-- BEGIN COMPLETE MODULE SmallSpanNormal
section

open Set
open scoped RealInnerProductSpace

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

lemma small_family_normal (z : ι → E) (hc : Fintype.card ι < Module.finrank ℝ E) :
    ∃ c : E, c≠0 ∧ ∀ i, ⟪c,z i⟫=0 := by
  let K := Submodule.span ℝ (Set.range z)
  have hK : K≠⊤ := by
    intro he
    have hh := finrank_le_of_span_eq_top (show Submodule.span ℝ (Set.range z)=⊤ from he)
    omega
  have hKo : Kᗮ≠⊥ := by
    intro he
    exact hK (Submodule.orthogonal_eq_bot_iff.mp he)
  obtain ⟨c,hcK,hc0⟩ := Kᗮ.ne_bot_iff.mp hKo
  refine ⟨c,hc0,fun i => ?_⟩
  exact (K.mem_orthogonal' c).mp hcK (z i) (Submodule.subset_span ⟨i,rfl⟩)

lemma small_family_affine_normal (z : ι → E) (v : E)
    (hc : Fintype.card ι < Module.finrank ℝ E) :
    ∃ c : E, c≠0 ∧ ∀ i, ⟪c,z i⟫=⟪c,v⟫ := by
  obtain ⟨c,hc0,hh⟩ := small_family_normal (fun i => z i-v) hc
  refine ⟨c,hc0,fun i => ?_⟩
  have h := hh i
  rwa [inner_sub_right,sub_eq_zero] at h

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE SmallSpanNormal

-- BEGIN COMPLETE MODULE FullDimVertices
section

open Set

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E}

lemma extremePoints_affineSpan (hc : IsCompact S) (hv : Convex ℝ S)
    (hi : (interior S).Nonempty) : affineSpan ℝ (S.extremePoints ℝ) = ⊤ := by
  let A := affineSpan ℝ (S.extremePoints ℝ)
  have hsub : S ⊆ (A : Set E) := by
    rw [← closure_convexHull_extremePoints hc hv]
    exact closure_minimal (convexHull_min (subset_affineSpan ℝ _) A.convex) A.closed_of_finiteDimensional
  have hh := affineSpan_le.mpr hsub
  rw [hv.interior_nonempty_iff_affineSpan_eq_top.mp hi] at hh
  exact top_unique hh

lemma extremePoints_encard_lower (hc : IsCompact S) (hv : Convex ℝ S)
    (hi : (interior S).Nonempty) :
    (Module.finrank ℝ E : ℕ∞)+1 ≤ (S.extremePoints ℝ).encard := by
  obtain ⟨s,hs,b,_⟩ := AffineBasis.exists_affine_subbasis (extremePoints_affineSpan hc hv hi)
  have : Finite s := b.finite
  let : Fintype s := Fintype.ofFinite s
  have hcard : s.encard = (Module.finrank ℝ E : ℕ∞)+1 := by
    rw [Set.encard,ENat.card_eq_coe_fintype_card,b.card_eq_finrank_add_one]
    simp
  exact hcard.symm.le.trans (Set.encard_le_encard hs)

lemma polyGraph_encard_lower (hc : IsCompact S) (hv : Convex ℝ S)
    (hi : (interior S).Nonempty) :
    (Module.finrank ℝ E : ℕ∞)+1 ≤ (Set.univ : Set (S.extremePoints ℝ)).encard := by
  rw [Set.encard_univ]
  exact extremePoints_encard_lower hc hv hi

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE FullDimVertices

-- BEGIN COMPLETE MODULE VertexHyperplane
section

open Set
open scoped RealInnerProductSpace

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma vertex_off_hyperplane {S : Set E} (hc : IsCompact S) (hv : Convex ℝ S)
    (hi : (interior S).Nonempty) {c : E} (hne : c≠0) (v₀ : E) :
    ∃ v∈S.extremePoints ℝ, ⟪c,v⟫≠⟪c,v₀⟫ := by
  by_contra hh
  push Not at hh
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ c).toLinearMap
  have he : L.toAffineMap = AffineMap.const ℝ E ⟪c,v₀⟫ :=
    AffineMap.ext_on (extremePoints_affineSpan hc hv hi) hh
  have h0 := DFunLike.congr_fun he (0:E)
  have h1 := DFunLike.congr_fun he c
  change ⟪c,(0:E)⟫=⟪c,v₀⟫ at h0
  change ⟪c,c⟫=⟪c,v₀⟫ at h1
  simp only [inner_zero_right] at h0
  have hz : ⟪c,c⟫=0 := h1.trans h0.symm
  exact hne (inner_self_eq_zero.mp hz)

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE VertexHyperplane

-- BEGIN COMPLETE MODULE PolyDeletion
section

open Set
open scoped RealInnerProductSpace

namespace Balinski61.Connectivity.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ}

lemma polyGraph_tuply_connected (hc : IsCompact (polyBody a b))
    (hi : (interior (polyBody a b)).Nonempty) :
    IsNTuplyConnected (polyGraph (polyBody a b)) (Module.finrank ℝ E) := by
  classical
  let S := polyBody a b
  let V := S.extremePoints ℝ
  have hcard := polyGraph_encard_lower hc (polyBody_convex a b) hi
  refine ⟨hcard,?_⟩
  intro X hX
  have : Finite V := (polyBody_finite_vertices a b).to_subtype
  let : Fintype X := Fintype.ofFinite X
  have hn : Fintype.card X < Module.finrank ℝ E := by
    rw [Set.encard,ENat.card_eq_coe_fintype_card] at hX
    exact_mod_cast hX
  have hne : (Xᶜ).Nonempty := by
    by_contra hh
    have he : X=Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      by_contra hv
      exact hh ⟨v,hv⟩
    rw [he] at hX
    have hh' := hcard.trans_lt hX
    exact (not_lt_of_ge (le_add_of_nonneg_right (by simp))) hh'
  obtain ⟨v₀,hv₀⟩ := hne
  obtain ⟨c,hc0,hcX⟩ := small_family_affine_normal (fun x : X => (x.val : E)) (v₀ : E) hn
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ c).toLinearMap
  let r := L v₀
  let f : V → ℝ := fun v => L v-r
  apply graph_deletion_connected f X
    (fun v hv => sub_eq_zero.mpr (hcX ⟨v,hv⟩)) ⟨v₀,hv₀⟩ (sub_self _)
  · obtain ⟨v,hv,hne⟩ := vertex_off_hyperplane hc (polyBody_convex a b) hi hc0 (v₀ : E)
    exact ⟨⟨v,hv⟩,sub_ne_zero.mpr hne⟩
  · have he : {v : V | 0<f v} = {v : V | r<L v} := by
      ext v
      change 0<L v-r ↔ r<L v
      exact sub_pos
    rw [he]
    exact polyGraph_upper_preconnected hc L r
  · have he : {v : V | f v<0} = {v : V | L v<r} := by
      ext v
      change L v-r<0 ↔ L v<r
      exact sub_neg
    rw [he]
    exact polyGraph_lower_preconnected hc L r
  · intro v hv hb
    obtain ⟨z,hz⟩ := hb
    have hbetter : L v<L z := by change L v-r=0 at hv; change 0<L z-r at hz; linarith
    obtain ⟨w,hw,ha,hlt⟩ := improving_edge hc v.property L ⟨z,z.property.1,hbetter⟩
    refine ⟨⟨w,hw⟩,ha,?_⟩
    change 0<L w-r
    change L v-r=0 at hv
    linarith
  · intro v hv hb
    obtain ⟨z,hz⟩ := hb
    have hbetter : (-L) v<(-L) z := by
      change L v-r=0 at hv
      change L z-r<0 at hz
      simp only [LinearMap.neg_apply]
      linarith
    obtain ⟨w,hw,ha,hlt⟩ := improving_edge hc v.property (-L) ⟨z,z.property.1,hbetter⟩
    refine ⟨⟨w,hw⟩,ha,?_⟩
    change L w-r<0
    change L v-r=0 at hv
    simp only [LinearMap.neg_apply] at hlt
    linarith

end Balinski61.Connectivity.Proof
end
-- END COMPLETE MODULE PolyDeletion

-- BEGIN COMPLETE MODULE BalinskiRoot
section

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem graph_n_tuply_connected (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) :
    IsNTuplyConnected (polyGraph (Hirsch.Hpoly a b)) n := by
  let rows : Fin m → EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    fun i => (innerSL ℝ (a i)).toLinearMap
  have hc := Proof.polyBody_compact rows b hS.only_zero
  obtain ⟨x,hx⟩ := hS.strict_point
  have hi : (interior (Proof.polyBody rows b)).Nonempty :=
    ⟨x,Proof.strict_mem_interior rows b hx⟩
  have hh := Proof.polyGraph_tuply_connected hc hi
  have he : Proof.polyBody rows b = Hirsch.Hpoly a b := by
    ext x
    rfl
  rw [he,finrank_euclideanSpace_fin] at hh
  exact hh

end Balinski61.Connectivity

theorem solution (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : Balinski61.Connectivity.StandingAssumptions a b) :
    Balinski61.Connectivity.IsNTuplyConnected
      (Balinski61.Connectivity.polyGraph (Hirsch.Hpoly a b)) n :=
  Balinski61.Connectivity.graph_n_tuply_connected n m a b hS
end
-- END COMPLETE MODULE BalinskiRoot
