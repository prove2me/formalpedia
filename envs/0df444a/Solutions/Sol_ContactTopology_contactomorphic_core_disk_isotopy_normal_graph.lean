-- Prove2me | solution 1 for ContactTopology.contactomorphic_core_disk_isotopy_normal_graph
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:57:44.037494+00:00
-- url     : https://prove2.me/submissions/14ef37ee-0f53-4772-a19f-1500b01def8d

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_ContactTopology_contactomorphic_core_spanning_disk_neighborhood





namespace ContactTopology.NormalGraph
open Set Function Filter
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma boundary_zero_extension_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (hS : IsClosed S) (h : E → E) (c : ℝ≥0)
    (hh : LipschitzOnWith c h S) (hz : ∀ x ∈ frontier S, h x=0) :
    ∃ H : E → E, LipschitzWith c H ∧ (∀ x ∈ S, H x=h x) ∧ (∀ x ∉ S, H x=0) := by
  classical
  let H : E → E := S.piecewise h (fun _ => 0)
  have hcross : ∀ x ∈ S, ∀ y ∉ S, dist (h x) 0 ≤ c*dist x y := by
    intro x hx y hy
    have hproper : S ≠ univ := by intro heq; apply hy; rw [heq]; exact mem_univ y
    obtain ⟨z,hzS,hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hproper
    have hzmem : z ∈ S := by simpa only [hS.closure_eq] using frontier_subset_closure hzS
    have hdist : dist x z ≤ dist x y := by
      rw [← hd]
      exact Metric.infDist_le_dist_of_mem hy
    calc
      dist (h x) 0=dist (h x) (h z) := by rw [hz z hzS]
      _ ≤ c*dist x z := hh.dist_le_mul x hx z hzmem
      _ ≤ c*dist x y := mul_le_mul_of_nonneg_left hdist c.coe_nonneg
  refine ⟨H,LipschitzWith.of_dist_le_mul ?_,?_,?_⟩
  · intro x y
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa [H,hx,hy] using hh.dist_le_mul x hx y hy
    · simpa [H,hx,hy] using hcross x hx y hy
    · simpa [H,hx,hy,dist_comm] using hcross y hy x hx
    · simp [H,hx,hy,mul_nonneg c.coe_nonneg dist_nonneg]
  · intro x hx
    simp [H,hx]
  · intro x hx
    simp [H,hx]

lemma contracting_displacement_bijective {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : E → E) (c : ℝ≥0) (hc : c < 1) (hh : LipschitzWith c h) :
    Bijective (fun x => x+h x) := by
  constructor
  · intro x y hxy
    have heq : x-y=h y-h x := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm (h y) y] using hxy
    have hd : dist x y ≤ c*dist x y := by
      calc
        dist x y=dist (h y) (h x) := by simp only [dist_eq_norm,heq]
        _ ≤ c*dist y x := hh.dist_le_mul y x
        _=c*dist x y := by rw [dist_comm y x]
    have hnorm : dist x y=0 := by
      have hc' : (c:ℝ) < 1 := hc
      nlinarith [dist_nonneg (x := x) (y := y)]
    exact dist_eq_zero.mp hnorm
  · intro y
    let T : E → E := fun x => y-h x
    have hT : ContractingWith c T := ⟨hc,LipschitzWith.of_dist_le_mul (by
      intro x z
      simpa only [T,dist_sub_left] using hh.dist_le_mul x z)⟩
    let x := ContractingWith.fixedPoint T hT
    have hx : y-h x=x := hT.fixedPoint_isFixedPt
    exact ⟨x,(sub_eq_iff_eq_add.mp hx).symm⟩

lemma boundary_fixed_small_displacement_bijOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (S : Set E) (hS : IsClosed S) (f : E → E) (c : ℝ≥0) (hc : c < 1)
    (hh : LipschitzOnWith c (fun x => f x-x) S)
    (hfix : ∀ x ∈ frontier S, f x=x) : BijOn f S S := by
  obtain ⟨h,hlip,hon,hout⟩ := boundary_zero_extension_lipschitz S hS (fun x => f x-x) c hh
    (fun x hx => by rw [hfix x hx,sub_self])
  let F : E → E := fun x => x+h x
  have hbij : Bijective F := contracting_displacement_bijective h c hc hlip
  have hF : ∀ x ∈ S, F x=f x := by intro x hx; simp only [F,hon x hx]; abel
  have hFo : ∀ x ∉ S, F x=x := by intro x hx; simp only [F,hout x hx,add_zero]
  have hmap : MapsTo f S S := by
    intro x hx
    by_contra hn
    have hEq : F (F x)=F x := hFo (F x) (by simpa only [hF x hx] using hn)
    have hxx := hbij.1 hEq
    have hFx : F x ∈ S := hxx.symm ▸ hx
    exact hn (by simpa only [hF x hx] using hFx)
  refine ⟨hmap,?_,?_⟩
  · intro x hx y hy heq
    exact hbij.1 (by simpa only [hF x hx,hF y hy] using heq)
  · intro y hy
    obtain ⟨x,hx⟩ := hbij.2 y
    have hxS : x ∈ S := by
      by_contra hn
      have hxy : x=y := by simpa only [hFo x hn] using hx
      exact hn (hxy ▸ hy)
    exact ⟨x,hxS,by simpa only [hF x hxS] using hx⟩

end
end ContactTopology.NormalGraph

namespace ContactTopology.ConvexDeformation
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

lemma smooth_injective_derivative_local_chart_general (F : E → E) (hF : ContDiff ℝ ∞ F)
    (p : E) (hinj : Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ p ∈ e.source := by
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] E) p := (hF.differentiable (by simp) p).hasFDerivAt
  exact ⟨hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp),
    hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp),
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)⟩

/-- Local invertibility and injectivity on a compact set give one genuine smooth
chart around the entire compact set, inside any prescribed good open domain. -/
theorem compact_smooth_embedding_chart_general (F : E → E) (hF : ContDiff ℝ ∞ F)
    (S W : Set E) (hS : IsCompact S) (hW : IsOpen W) (hSW : S ⊆ W)
    (hinj : InjOn F S) (hder : ∀ p ∈ W, Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ S ⊆ e.source ∧
      e.source ⊆ W ∧ ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hloc : ∀ p ∈ S, ∃ O ∈ 𝓝 p, InjOn F O := by
    intro p hp
    obtain ⟨e,he,hp⟩ := smooth_injective_derivative_local_chart_general F hF p (hder p (hSW hp))
    exact ⟨e.source,e.open_source.mem_nhds hp,he ▸ e.injOn⟩
  obtain ⟨O,hO,hSO,hOi⟩ := hinj.exists_isOpen_superset hS (fun _ _ => hF.continuous.continuousAt) hloc
  let U := O ∩ W
  have hU : IsOpen U := hO.inter hW
  have hUi : InjOn F U := hOi.mono inter_subset_left
  have hopen : IsOpenMap (U.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    obtain ⟨e,he,hx⟩ := smooth_injective_derivative_local_chart_general F hF x (hder x x.property.2)
    have hm : map F (𝓝 x.val) = 𝓝 (F x.val) := by
      simpa only [he] using e.map_nhds_eq hx
    have hs : map (fun x : U => (x : E)) (𝓝 x) = 𝓝 (x : E) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change 𝓝 (F x.val) ≤ map (fun z : U => F z.val) (𝓝 x)
    rw [show (fun z : U => F z.val) = F ∘ Subtype.val from rfl,← map_map,hs,hm]
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hUi.toPartialEquiv F U) hF.continuous.continuousOn hopen hU
  have he : (e : E → E) = F := rfl
  refine ⟨e,he,fun x hx => ⟨hSO hx,hSW hx⟩,inter_subset_right,?_⟩
  intro y hy
  have hp : e.symm y ∈ W := (e.map_target hy).2
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
    ⟨hder _ hp,LinearMap.injective_iff_surjective.mp (hder _ hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) := (hF.differentiable (by simp) _).hasFDerivAt
  exact e.contDiffAt_symm hy hd hF.contDiffAt

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.NormalGraph
open Set Function Filter
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma near_identity_derivative_injective (L : E →L[ℝ] E)
    (hL : ‖L-ContinuousLinearMap.id ℝ E‖ < 1) : Injective L := by
  intro x y hxy
  let v := x-y
  have hv : L v=0 := by simp only [v,map_sub,hxy,sub_self]
  have hbound := (L-ContinuousLinearMap.id ℝ E).le_opNorm v
  have heq : (L-ContinuousLinearMap.id ℝ E) v = -v := by simp [hv]
  rw [heq,norm_neg] at hbound
  have hn : ‖v‖=0 := by nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma derivative_small_displacement_bijOn (S : Set E) (hS : IsClosed S)
    (hconv : Convex ℝ S) (f : E → E)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ S, ‖fderiv ℝ f x-ContinuousLinearMap.id ℝ E‖ ≤ (1:ℝ)/2)
    (hfix : ∀ x ∈ frontier S, f x=x) : BijOn f S S := by
  apply boundary_fixed_small_displacement_bijOn S hS f (1/2) (by norm_num) _ hfix
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le' hf hbound hconv hy hx
  have heq : f x-f y-(ContinuousLinearMap.id ℝ E) (x-y) =
      (f x-x)-(f y-y) := by simp only [ContinuousLinearMap.id_apply]; abel
  simpa only [dist_eq_norm,heq,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hb

/-- A derivative estimate and actual boundary fixing construct a smooth chart
around the whole compact convex set; surjectivity is a conclusion. -/
theorem near_identity_compact_convex_chart (S : Set E) (hS : IsCompact S)
    (hconv : Convex ℝ S) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ x ∈ S, ‖fderiv ℝ f x-ContinuousLinearMap.id ℝ E‖ ≤ (1:ℝ)/2)
    (hfix : ∀ x ∈ frontier S, f x=x) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E)=f ∧
      S ⊆ e.source ∧ S ⊆ e.target ∧ BijOn f S S ∧
      MapsTo e.symm S S ∧ (∀ x ∈ S, e.symm (f x)=x) ∧
      ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hbij := derivative_small_displacement_bijOn S hS.isClosed hconv f
    (fun x _ => hf.differentiable (by simp) x) hbound hfix
  let W : Set E := {x | ‖fderiv ℝ f x-ContinuousLinearMap.id ℝ E‖ < (3:ℝ)/4}
  have hW : IsOpen W := isOpen_lt
    ((hf.continuous_fderiv (by simp)).sub continuous_const).norm continuous_const
  have hSW : S ⊆ W := by intro x hx; exact lt_of_le_of_lt (hbound x hx) (by norm_num)
  obtain ⟨e,he,hsource,heW,hsmooth⟩ :=
    ContactTopology.ConvexDeformation.compact_smooth_embedding_chart_general f hf S W hS hW hSW
      hbij.injOn (fun x hx => near_identity_derivative_injective _ (lt_trans hx (by norm_num)))
  have htarget : S ⊆ e.target := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := hbij.surjOn hy
    have hm := e.map_source (hsource hx)
    simpa only [he,hxy] using hm
  have hinverse : MapsTo e.symm S S := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := hbij.surjOn hy
    have heq : e.symm y=x := by
      rw [← hxy,← he]
      exact e.left_inv (hsource hx)
    exact heq ▸ hx
  exact ⟨e,he,hsource,htarget,hbij,hinverse,
    fun x hx => by rw [← he]; exact e.left_inv (hsource hx),hsmooth⟩

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

lemma smooth_injective_derivative_local_chart_on (F : E → E) (p : E)
    (hF : ContDiffAt ℝ ∞ F p) (hinj : Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ p ∈ e.source := by
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] E) p := (hF.differentiableAt (by simp)).hasFDerivAt
  exact ⟨hF.toOpenPartialHomeomorph F hd (by simp),
    hF.toOpenPartialHomeomorph_coe hd (by simp),
    hF.mem_toOpenPartialHomeomorph_source hd (by simp)⟩

/-- The compact inverse chart construction with smoothness only on the actual
open coordinate domain. -/
theorem compact_smooth_embedding_chart_on (F : E → E) (S W : Set E)
    (hS : IsCompact S) (hW : IsOpen W) (hSW : S ⊆ W)
    (hF : ∀ p ∈ W, ContDiffAt ℝ ∞ F p)
    (hinj : InjOn F S) (hder : ∀ p ∈ W, Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ S ⊆ e.source ∧
      e.source ⊆ W ∧ ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hloc : ∀ p ∈ S, ∃ O ∈ 𝓝 p, InjOn F O := by
    intro p hp
    obtain ⟨e,he,hp⟩ := smooth_injective_derivative_local_chart_on F p (hF p (hSW hp))
      (hder p (hSW hp))
    exact ⟨e.source,e.open_source.mem_nhds hp,he ▸ e.injOn⟩
  obtain ⟨O,hO,hSO,hOi⟩ := hinj.exists_isOpen_superset hS
    (fun p hp => (hF p (hSW hp)).continuousAt) hloc
  let U := O ∩ W
  have hU : IsOpen U := hO.inter hW
  have hUi : InjOn F U := hOi.mono inter_subset_left
  have hopen : IsOpenMap (U.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    obtain ⟨e,he,hx⟩ := smooth_injective_derivative_local_chart_on F x (hF x x.property.2)
      (hder x x.property.2)
    have hm : map F (𝓝 x.val) = 𝓝 (F x.val) := by
      simpa only [he] using e.map_nhds_eq hx
    have hs : map (fun x : U => (x : E)) (𝓝 x) = 𝓝 (x : E) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change 𝓝 (F x.val) ≤ map (fun z : U => F z.val) (𝓝 x)
    rw [show (fun z : U => F z.val) = F ∘ Subtype.val from rfl,← map_map,hs,hm]
  have hcont : ContinuousOn F U := fun p hp => (hF p hp.2).continuousAt.continuousWithinAt
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hUi.toPartialEquiv F U) hcont hopen hU
  have he : (e : E → E) = F := rfl
  refine ⟨e,he,fun x hx => ⟨hSO hx,hSW hx⟩,inter_subset_right,?_⟩
  intro y hy
  have hp : e.symm y ∈ W := (e.map_target hy).2
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
    ⟨hder _ hp,LinearMap.injective_iff_surjective.mp (hder _ hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) :=
    ((hF _ hp).differentiableAt (by simp)).hasFDerivAt
  exact e.contDiffAt_symm hy hd (hF _ hp)

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_slice (B : P × E → E) (q : P × E)
    (hB : DifferentiableAt ℝ B q) :
    fderiv ℝ (fun x => B (q.1,x)) q.2 =
      (fderiv ℝ B q).comp (ContinuousLinearMap.inr ℝ P E) := by
  have hi : HasFDerivAt (fun x : E => (q.1,x)) (ContinuousLinearMap.inr ℝ P E) q.2 := by
    have hh := (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id q.2)
    have he : (0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.inr ℝ P E := by ext z <;> rfl
    rwa [he] at hh
  exact (hB.hasFDerivAt.comp q.2 hi).fderiv

lemma slice_derivative_continuousOn (B : P × E → E) (A : Set (P × E))
    (hA : IsOpen A) (hB : ∀ q ∈ A, ContDiffAt ℝ ∞ B q) :
    ContinuousOn (fun q => fderiv ℝ (fun x => B (q.1,x)) q.2) A := by
  have hDB : ContinuousOn (fderiv ℝ B) A :=
    (show ContDiffOn ℝ ∞ B A from fun q hq => (hB q hq).contDiffWithinAt).continuousOn_fderiv_of_isOpen
      hA (by simp)
  have hc : ContinuousOn (fun q => (fderiv ℝ B q).comp (ContinuousLinearMap.inr ℝ P E)) A :=
    hDB.clm_comp continuousOn_const
  exact hc.congr (fun q hq => (fderiv_slice B q ((hB q hq).differentiableAt (by simp))))

lemma parameter_map_derivative_injective (B : P × E → E) (q : P × E)
    (hB : DifferentiableAt ℝ B q)
    (hinj : Injective (fderiv ℝ (fun x => B (q.1,x)) q.2)) :
    Injective (fderiv ℝ (fun p : P × E => (p.1,B p)) q) := by
  have hDF := (differentiableAt_fst (𝕜 := ℝ) (p := q)).fderiv_prodMk hB
  intro v w hvw
  rw [hDF,fderiv_fst] at hvw
  have hpair : (v.1,(fderiv ℝ B q) v)=(w.1,(fderiv ℝ B q) w) := by simpa using hvw
  rcases Prod.mk.inj hpair with ⟨hfirst,hsecond⟩
  have hz : (fderiv ℝ B q) (v-w)=0 := by rw [map_sub,hsecond,sub_self]
  have hdiff : v-w=(ContinuousLinearMap.inr ℝ P E) (v.2-w.2) := by
    ext <;> simp [hfirst]
  rw [hdiff] at hz
  have hslice : (fderiv ℝ (fun x => B (q.1,x)) q.2) (v.2-w.2)=0 := by
    rw [fderiv_slice B q hB]; exact hz
  have hlast : v.2=w.2 := sub_eq_zero.mp (hinj (by simpa using hslice))
  exact Prod.ext hfirst hlast

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

/-- A compact family of near-identity, boundary-fixed projections has one
jointly smooth inverse on an open neighborhood in parameter-space times space. -/
theorem parametric_near_identity_chart (T : Set P) (hT : IsCompact T)
    (S : Set E) (hS : IsCompact S) (hconv : Convex ℝ S)
    (A : Set (P × E)) (hA : IsOpen A) (hTA : T ×ˢ S ⊆ A)
    (B : P × E → E) (hB : ∀ q ∈ A, ContDiffAt ℝ ∞ B q)
    (hbound : ∀ p ∈ T, ∀ x ∈ S,
      ‖fderiv ℝ (fun z => B (p,z)) x-ContinuousLinearMap.id ℝ E‖ ≤ (1:ℝ)/2)
    (hfix : ∀ p ∈ T, ∀ x ∈ frontier S, B (p,x)=x) :
    ∃ e : OpenPartialHomeomorph (P × E) (P × E),
      (e : (P × E) → (P × E))=(fun q => (q.1,B q)) ∧
      T ×ˢ S ⊆ e.source ∧ T ×ˢ S ⊆ e.target ∧ e.source ⊆ A ∧
      (∀ p ∈ T, BijOn (fun x => B (p,x)) S S) ∧
      MapsTo e.symm (T ×ˢ S) (T ×ˢ S) ∧
      (∀ p ∈ T, ∀ y ∈ S, (e.symm (p,y)).1=p) ∧
      ∀ q ∈ e.target, ContDiffAt ℝ ∞ e.symm q := by
  let L : P × E → E →L[ℝ] E := fun q => fderiv ℝ (fun x => B (q.1,x)) q.2
  have hL := slice_derivative_continuousOn B A hA hB
  let W : Set (P × E) := A ∩ {q | ‖L q-ContinuousLinearMap.id ℝ E‖ < (3:ℝ)/4}
  have hW : IsOpen W :=
    ((hL.sub continuousOn_const).norm).isOpen_inter_preimage hA isOpen_Iio
  have hKW : T ×ˢ S ⊆ W := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    exact ⟨hTA ⟨hp,hx⟩,lt_of_le_of_lt (hbound p hp x hx) (by norm_num)⟩
  have hbij : ∀ p ∈ T, BijOn (fun x => B (p,x)) S S := by
    intro p hp
    apply derivative_small_displacement_bijOn S hS.isClosed hconv _ _ (hbound p hp) (hfix p hp)
    intro x hx
    exact ((hB (p,x) (hTA ⟨hp,hx⟩)).comp x (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  let F : P × E → P × E := fun q => (q.1,B q)
  have hF : ∀ q ∈ W, ContDiffAt ℝ ∞ F q :=
    fun q hq => contDiffAt_fst.prodMk (hB q hq.1)
  have hi : InjOn F (T ×ˢ S) := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩ ⟨q,y⟩ ⟨hq,hy⟩ heq
    have hpq : p=q := congrArg Prod.fst heq
    subst q
    exact Prod.ext rfl ((hbij p hp).injOn hx hy (congrArg Prod.snd heq))
  have hd : ∀ q ∈ W, Injective (fderiv ℝ F q) := by
    intro q hq
    apply parameter_map_derivative_injective B q ((hB q hq.1).differentiableAt (by simp))
    exact near_identity_derivative_injective _ (lt_trans hq.2 (by norm_num))
  obtain ⟨e,he,hsrc,heW,hsmooth⟩ := compact_smooth_embedding_chart_on F (T ×ˢ S) W
    (hT.prod hS) hW hKW hF hi hd
  have hsurj : SurjOn F (T ×ˢ S) (T ×ˢ S) := by
    rintro ⟨p,y⟩ ⟨hp,hy⟩
    obtain ⟨x,hx,hxy⟩ := (hbij p hp).surjOn hy
    exact ⟨(p,x),⟨hp,hx⟩,Prod.ext rfl hxy⟩
  have htgt : T ×ˢ S ⊆ e.target := by
    intro q hq
    obtain ⟨p,hp,hpq⟩ := hsurj hq
    simpa only [he,hpq] using e.map_source (hsrc hp)
  have hinv : MapsTo e.symm (T ×ˢ S) (T ×ˢ S) := by
    intro q hq
    obtain ⟨p,hp,hpq⟩ := hsurj hq
    have heq : e.symm q=p := by rw [← hpq,← he]; exact e.left_inv (hsrc hp)
    exact heq ▸ hp
  refine ⟨e,he,hsrc,htgt,fun q hq => (heW hq).1,hbij,hinv,?_,hsmooth⟩
  intro p hp y hy
  have hright := e.right_inv (htgt (show (p,y) ∈ T ×ˢ S from ⟨hp,hy⟩))
  rw [he] at hright
  exact congrArg Prod.fst hright

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform spatial derivative control is derived from the actual family and
its diagonal identity, rather than supplied as a graph-position hypothesis. -/
theorem uniform_diagonal_derivative_bound (S N : Set E) (hS : IsCompact S)
    (hN : IsOpen N) (hSN : S ⊆ N)
    (A : Set ((ℝ × ℝ) × E)) (hA : IsOpen A)
    (B : (ℝ × ℝ) × E → E) (hB : ∀ q ∈ A, ContDiffAt ℝ ∞ B q)
    (hdiagA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ S, ((t,0),x) ∈ A)
    (hdiag : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ N, B ((t,0),x)=x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ d : ℝ, |d| ≤ δ → ∀ x ∈ S,
      ((t,d),x) ∈ A ∧
      ‖fderiv ℝ (fun z => B ((t,d),z)) x-ContinuousLinearMap.id ℝ E‖ ≤ (1:ℝ)/2 := by
  let L : ((ℝ × ℝ) × E) → E →L[ℝ] E :=
    fun q => fderiv ℝ (fun x => B (q.1,x)) q.2
  have hL := slice_derivative_continuousOn B A hA hB
  let O : Set ((ℝ × ℝ) × E) :=
    A ∩ {q | ‖L q-ContinuousLinearMap.id ℝ E‖ < (1:ℝ)/2}
  have hO : IsOpen O :=
    ((hL.sub continuousOn_const).norm).isOpen_inter_preimage hA isOpen_Iio
  let J : (ℝ × E) × ℝ → (ℝ × ℝ) × E := fun q => ((q.1.1,q.2),q.1.2)
  have hJ : Continuous J := by fun_prop
  have hdiagL : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ S, L ((t,0),x)=ContinuousLinearMap.id ℝ E := by
    intro t ht x hx
    have heq : (fun z => B ((t,0),z)) =ᶠ[𝓝 x] (fun z : E => z) := by
      filter_upwards [hN.mem_nhds (hSN hx)] with z hz
      exact hdiag t ht z hz
    exact heq.fderiv_eq.trans (fderiv_id (𝕜 := ℝ))
  have hdiagO : (Icc (0:ℝ) 1 ×ˢ S) ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' O := by
    rintro ⟨⟨t,x⟩,d⟩ ⟨⟨ht,hx⟩,hd⟩
    have hd0 : d=0 := hd
    subst d
    refine ⟨hdiagA t ht x hx,?_⟩
    change ‖L ((t,0),x)-ContinuousLinearMap.id ℝ E‖ < (1:ℝ)/2
    rw [hdiagL t ht x hx,sub_self,norm_zero]
    norm_num
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (isCompact_Icc.prod hS)
    isCompact_singleton (hO.preimage hJ) hdiagO
  have hzV : (0:ℝ) ∈ V := h0V (mem_singleton 0)
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  refine ⟨r/2,by positivity,?_⟩
  intro t ht d hd x hx
  have hdV : d ∈ V := hrV (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact lt_of_le_of_lt hd (by linarith))
  have hh := hUV (show ((t,x),d) ∈ U ×ˢ V from ⟨hKU ⟨ht,hx⟩,hdV⟩)
  exact ⟨hh.1,hh.2.le⟩

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Actual smooth nearby embeddings, with diagonal projection identity and
fixed boundary, have jointly smooth normal-graph coordinates. No injectivity,
surjectivity, inverse, graph position, or subdivision is supplied as input. -/
theorem diagonal_normal_graph_family (S N : Set E) (hS : IsCompact S)
    (hconv : Convex ℝ S) (hN : IsOpen N) (hSN : S ⊆ N)
    (A : Set ((ℝ × ℝ) × E)) (hA : IsOpen A)
    (B : (ℝ × ℝ) × E → E) (H : (ℝ × ℝ) × E → ℝ)
    (hB : ∀ q ∈ A, ContDiffAt ℝ ∞ B q) (hH : ∀ q ∈ A, ContDiffAt ℝ ∞ H q)
    (hdiagA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ S, ((t,0),x) ∈ A)
    (hdiag : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ N, B ((t,0),x)=x)
    (hfix : ∀ t ∈ Icc (0:ℝ) 1, ∀ d : ℝ, ∀ x ∈ frontier S, B ((t,d),x)=x)
    (hHfix : ∀ t ∈ Icc (0:ℝ) 1, ∀ d : ℝ, ∀ x ∈ frontier S, H ((t,d),x)=0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ O : Set ((ℝ × ℝ) × E), IsOpen O ∧
      (Icc (0:ℝ) 1 ×ˢ Icc (-δ) δ) ×ˢ S ⊆ O ∧
      ∃ θ : (ℝ × ℝ) × E → E, ∃ g : (ℝ × ℝ) × E → ℝ,
        ContDiffOn ℝ ∞ θ O ∧ ContDiffOn ℝ ∞ g O ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∀ d : ℝ, |d| ≤ δ →
          BijOn (fun x => B ((t,d),x)) S S ∧
          (∀ y ∈ S, θ ((t,d),y) ∈ S ∧
            B ((t,d),θ ((t,d),y))=y ∧ H ((t,d),θ ((t,d),y))=g ((t,d),y)) ∧
          (∀ x ∈ S, θ ((t,d),B ((t,d),x))=x) ∧
          (∀ y ∈ frontier S, g ((t,d),y)=0) := by
  obtain ⟨δ,hδ,hnear⟩ := uniform_diagonal_derivative_bound S N hS hN hSN A hA B hB hdiagA hdiag
  let T : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (-δ) δ
  have hTA : T ×ˢ S ⊆ A := by
    rintro ⟨⟨t,d⟩,x⟩ ⟨⟨ht,hd⟩,hx⟩
    exact (hnear t ht d (abs_le.mpr hd) x hx).1
  obtain ⟨e,he,hsrc,htgt,heA,hbij,hinv,hfirst,hsmooth⟩ :=
    parametric_near_identity_chart T (isCompact_Icc.prod isCompact_Icc) S hS hconv A hA hTA B hB
      (fun p hp x hx => (hnear p.1 hp.1 p.2 (abs_le.mpr hp.2) x hx).2)
      (fun p hp x hx => hfix p.1 hp.1 p.2 x hx)
  let θ : (ℝ × ℝ) × E → E := fun q => (e.symm q).2
  let g : (ℝ × ℝ) × E → ℝ := fun q => H (e.symm q)
  have hθ : ContDiffOn ℝ ∞ θ e.target := fun q hq => (hsmooth q hq).snd.contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ g e.target := by
    intro q hq
    exact ((hH _ (heA (e.map_target hq))).comp q (hsmooth q hq)).contDiffWithinAt
  refine ⟨δ,hδ,e.target,e.open_target,htgt,θ,g,hθ,hg,?_⟩
  intro t ht d hd
  have hp : (t,d) ∈ T := ⟨ht,abs_le.mp hd⟩
  have hθdata : ∀ y ∈ S, θ ((t,d),y) ∈ S ∧
      B ((t,d),θ ((t,d),y))=y ∧ H ((t,d),θ ((t,d),y))=g ((t,d),y) := by
    intro y hy
    have hq : ((t,d),y) ∈ T ×ˢ S := ⟨hp,hy⟩
    have hfp := hfirst (t,d) hp y hy
    have hr := e.right_inv (htgt hq)
    rw [he] at hr
    have hb : B (e.symm ((t,d),y))=y := congrArg Prod.snd hr
    have hpair : e.symm ((t,d),y)=((t,d),θ ((t,d),y)) := Prod.ext hfp rfl
    refine ⟨(hinv hq).2,?_,?_⟩
    · simpa only [hpair] using hb
    · change H ((t,d),θ ((t,d),y))=H (e.symm ((t,d),y))
      rw [hpair]
  have hθleft : ∀ x ∈ S, θ ((t,d),B ((t,d),x))=x := by
    intro x hx
    have hl := e.left_inv (hsrc (show ((t,d),x) ∈ T ×ˢ S from ⟨hp,hx⟩))
    rw [he] at hl
    exact congrArg Prod.snd hl
  refine ⟨hbij (t,d) hp,hθdata,hθleft,?_⟩
  intro y hy
  have hyS : y ∈ S := by simpa only [hS.isClosed.closure_eq] using frontier_subset_closure hy
  have heq : θ ((t,d),y)=y := by simpa only [hfix t ht d y hy] using hθleft y hyS
  rw [← (hθdata y hyS).2.2,heq,hHfix t ht d y hy]

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Normal graphs for an actual ambient isotopy, in a genuine prescribed
chart. The coordinate inverse is required smooth only at chart points. -/
theorem ambient_isotopy_normal_graph (S : Set E) (hS : IsCompact S) (hconv : Convex ℝ S)
    (M : Set Y) (C : E × ℝ → Y) (R : Y → E × ℝ) (N : Set (E × ℝ))
    (hN : IsOpen N) (hSN : ∀ x ∈ S, (x,0) ∈ N)
    (hC : ContDiff ℝ ∞ C) (hCM : ∀ z, C z ∈ M)
    (hR : ∀ z ∈ N, ContDiffAt ℝ ∞ R (C z))
    (hRC : ∀ z ∈ N, R (C z)=z)
    (hlocal : ∀ z ∈ N, ∃ U : Set Y, IsOpen U ∧ C z ∈ U ∧
      ∀ y ∈ U, y ∈ M → R y ∈ N ∧ C (R y)=y)
    (φ ρ : ℝ → Y → Y)
    (hφ : ∀ t y, y ∈ M → ContDiffAt ℝ ∞ (fun p : ℝ × Y => φ p.1 p.2) (t,y))
    (hρ : ∀ t y, y ∈ M → ContDiffAt ℝ ∞ (fun p : ℝ × Y => ρ p.1 p.2) (t,y))
    (hφM : ∀ t, MapsTo (φ t) M M) (hρM : ∀ t, MapsTo (ρ t) M M)
    (hleft : ∀ t y, y ∈ M → ρ t (φ t y)=y)
    (hboundary : ∀ t x, x ∈ frontier S → φ t (C (x,0))=C (x,0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ O : Set ((ℝ × ℝ) × E), IsOpen O ∧
      (Icc (0:ℝ) 1 ×ˢ Icc (-δ) δ) ×ˢ S ⊆ O ∧
      ∃ θ : (ℝ × ℝ) × E → E, ∃ g : (ℝ × ℝ) × E → ℝ,
        ContDiffOn ℝ ∞ θ O ∧ ContDiffOn ℝ ∞ g O ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∀ d : ℝ, |d| ≤ δ →
          (∀ x ∈ S, R (ρ t (φ (t+d) (C (x,0)))) ∈ N ∧
            C (R (ρ t (φ (t+d) (C (x,0)))))=ρ t (φ (t+d) (C (x,0)))) ∧
          BijOn (fun x => (R (ρ t (φ (t+d) (C (x,0))))).1) S S ∧
          (∀ y ∈ S, θ ((t,d),y) ∈ S ∧ (y,g ((t,d),y)) ∈ N ∧
            ρ t (φ (t+d) (C (θ ((t,d),y),0)))=C (y,g ((t,d),y))) ∧
          (∀ x ∈ S, θ ((t,d),(R (ρ t (φ (t+d) (C (x,0))))).1)=x) ∧
          (∀ y ∈ frontier S, g ((t,d),y)=0) ∧
          (fun x => ρ t (φ (t+d) (C (x,0)))) '' S =
            (fun y => C (y,g ((t,d),y))) '' S := by
  let U : Set Y := {y | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
    ∀ z ∈ V, z ∈ M → R z ∈ N ∧ C (R z)=z}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨V,hV,hy,hdata⟩
    exact mem_of_superset (hV.mem_nhds hy) (fun z hz => ⟨V,hV,hz,hdata⟩)
  have hCU : ∀ z ∈ N, C z ∈ U := by
    intro z hz
    obtain ⟨V,hV,hzV,hdata⟩ := hlocal z hz
    exact ⟨V,hV,hzV,hdata⟩
  have hUdata : ∀ y ∈ U, y ∈ M → R y ∈ N ∧ C (R y)=y := by
    rintro y ⟨V,hV,hy,hdata⟩ hym
    exact hdata y hy hym
  let Q : (ℝ × ℝ) × E → Y := fun q => ρ q.1.1 (φ (q.1.1+q.1.2) (C (q.2,0)))
  have hQ : ContDiff ℝ ∞ Q := by
    rw [contDiff_iff_contDiffAt]
    intro q
    have hP : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × E => φ (q.1.1+q.1.2) (C (q.2,0))) q :=
      (hφ (q.1.1+q.1.2) (C (q.2,0)) (hCM _)).comp q (f := fun q : (ℝ × ℝ) × E => (q.1.1+q.1.2,C (q.2,0)))
        (((contDiffAt_fst.fst).add contDiffAt_fst.snd).prodMk
          (hC.contDiffAt.comp q (contDiffAt_snd.prodMk contDiffAt_const)))
    exact (hρ q.1.1 (φ (q.1.1+q.1.2) (C (q.2,0))) (hφM _ (hCM _))).comp q
      (f := fun q : (ℝ × ℝ) × E => (q.1.1,φ (q.1.1+q.1.2) (C (q.2,0))))
      (contDiffAt_fst.fst.prodMk hP)
  have hQM : ∀ q, Q q ∈ M := fun q => hρM _ (hφM _ (hCM _))
  let A : Set ((ℝ × ℝ) × E) := Q ⁻¹' U
  have hA : IsOpen A := hU.preimage hQ.continuous
  have hcoord : ∀ q ∈ A, ContDiffAt ℝ ∞ (fun p => R (Q p)) q := by
    intro q hq
    have hh := hUdata (Q q) hq (hQM q)
    have hRy : ContDiffAt ℝ ∞ R (Q q) := by
      simpa only [hh.2] using hR (R (Q q)) hh.1
    exact hRy.comp q hQ.contDiffAt
  let B : (ℝ × ℝ) × E → E := fun q => (R (Q q)).1
  let H : (ℝ × ℝ) × E → ℝ := fun q => (R (Q q)).2
  have hB : ∀ q ∈ A, ContDiffAt ℝ ∞ B q := fun q hq => (hcoord q hq).fst
  have hH : ∀ q ∈ A, ContDiffAt ℝ ∞ H q := fun q hq => (hcoord q hq).snd
  have hdiagQ : ∀ t x, Q ((t,0),x)=C (x,0) := by
    intro t x
    exact (by simpa only [Q,add_zero] using hleft t (C (x,0)) (hCM (x,0)))
  let Nbase : Set E := (fun x => (x,(0:ℝ))) ⁻¹' N
  have hNbase : IsOpen Nbase := hN.preimage (continuous_id.prodMk continuous_const)
  have hdiagA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ S, ((t,0),x) ∈ A := by
    intro t ht x hx
    change Q ((t,0),x) ∈ U
    rw [hdiagQ]
    exact hCU (x,0) (hSN x hx)
  have hdiag : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ Nbase, B ((t,0),x)=x := by
    intro t ht x hx
    change (R (Q ((t,0),x))).1=x
    rw [hdiagQ,hRC (x,0) hx]
  have hboundaryN : ∀ x ∈ frontier S, (x,0) ∈ N := by
    intro x hx
    apply hSN x
    simpa only [hS.isClosed.closure_eq] using frontier_subset_closure hx
  have hboundaryRQ : ∀ t d x, x ∈ frontier S → R (Q ((t,d),x))=(x,0) := by
    intro t d x hx
    have hr : ρ t (C (x,0))=C (x,0) := by
      simpa only [hboundary t x hx] using hleft t (C (x,0)) (hCM (x,0))
    change R (ρ t (φ (t+d) (C (x,0))))=(x,0)
    rw [hboundary (t+d) x hx,hr,hRC (x,0) (hboundaryN x hx)]
  obtain ⟨δ,hδ,O,hO,hKO,θ,g,hθ,hg,hdata⟩ := diagonal_normal_graph_family S Nbase hS hconv
    hNbase hSN A hA B H hB hH hdiagA hdiag
      (fun t _ d x hx => congrArg Prod.fst (hboundaryRQ t d x hx))
      (fun t _ d x hx => congrArg Prod.snd (hboundaryRQ t d x hx))
  -- Retain actual coordinate membership as well as the graph conclusion.
  obtain ⟨δ₀,hδ₀,hnear⟩ := uniform_diagonal_derivative_bound S Nbase hS hNbase hSN A hA B hB hdiagA hdiag
  let ε := min δ δ₀
  have hε : 0 < ε := lt_min hδ hδ₀
  refine ⟨ε,hε,O,hO,?_,θ,g,hθ,hg,?_⟩
  · rintro ⟨⟨t,d⟩,x⟩ ⟨⟨ht,hd⟩,hx⟩
    exact hKO ⟨⟨ht,⟨le_trans (neg_le_neg (min_le_left δ δ₀)) hd.1,
      hd.2.trans (min_le_left δ δ₀)⟩⟩,hx⟩
  intro t ht d hd
  have hdδ : |d| ≤ δ := hd.trans (min_le_left δ δ₀)
  have hdδ₀ : |d| ≤ δ₀ := hd.trans (min_le_right δ δ₀)
  obtain ⟨hbij,hθdata,hleftθ,hzero⟩ := hdata t ht d hdδ
  have hcoords : ∀ x ∈ S, R (Q ((t,d),x)) ∈ N ∧ C (R (Q ((t,d),x)))=Q ((t,d),x) := by
    intro x hx
    exact hUdata _ (hnear t ht d hdδ₀ x hx).1 (hQM _)
  have hgraph : ∀ y ∈ S, θ ((t,d),y) ∈ S ∧ (y,g ((t,d),y)) ∈ N ∧
      Q ((t,d),θ ((t,d),y))=C (y,g ((t,d),y)) := by
    intro y hy
    obtain ⟨hx,hbase,hheight⟩ := hθdata y hy
    have hpair : R (Q ((t,d),θ ((t,d),y)))=(y,g ((t,d),y)) := Prod.ext hbase hheight
    refine ⟨hx,by simpa only [hpair] using (hcoords _ hx).1,?_⟩
    rw [← (hcoords _ hx).2,hpair]
  refine ⟨hcoords,hbij,hgraph,hleftθ,hzero,?_⟩
  apply Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    have hy : B ((t,d),x) ∈ S := hbij.mapsTo hx
    refine ⟨B ((t,d),x),hy,?_⟩
    have hh := (hgraph _ hy).2.2
    rw [hleftθ x hx] at hh
    exact hh.symm
  · rintro z ⟨y,hy,rfl⟩
    exact ⟨θ ((t,d),y),(hgraph y hy).1,(hgraph y hy).2.2⟩

end
end ContactTopology.NormalGraph

namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
abbrev Plane := Fin 2 → ℝ
abbrev V := Fin 3 → ℝ

def diskSq (x : Plane) : ℝ := x 0^2+x 1^2
lemma diskSq_continuous : Continuous diskSq := by unfold diskSq; fun_prop
lemma disk_compact : IsCompact {x : Plane | diskSq x ≤ 1} := by
  apply (isCompact_Icc : IsCompact (Icc (![-1,-1] : Plane) ![1,1])).of_isClosed_subset
    (isClosed_le diskSq_continuous continuous_const)
  intro x hx
  have hh : x 0^2+x 1^2 ≤ 1 := hx
  constructor <;> intro i <;> fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]

lemma disk_convex : Convex ℝ {x : Plane | diskSq x ≤ 1} := by
  intro x hx y hy a b ha hb hab
  have hident : diskSq (a • x+b • y)=a*diskSq x+b*diskSq y-a*b*diskSq (x-y) := by
    have hbeq : b=1-a := by linarith
    simp only [diskSq,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
    rw [hbeq]
    ring
  have hnon : 0 ≤ diskSq (x-y) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hxa := mul_le_mul_of_nonneg_left hx ha
  have hyb := mul_le_mul_of_nonneg_left hy hb
  change diskSq (a • x+b • y) ≤ 1
  rw [hident]
  nlinarith [mul_nonneg (mul_nonneg ha hb) hnon]

lemma disk_frontier_sq (x : Plane) (hx : x ∈ frontier {x : Plane | diskSq x ≤ 1}) :
    diskSq x=1 := by
  have hclosed : IsClosed {x : Plane | diskSq x ≤ 1} := isClosed_le diskSq_continuous continuous_const
  have hle : diskSq x ≤ 1 := by simpa only [hclosed.closure_eq,mem_ofPred_eq] using frontier_subset_closure hx
  apply le_antisymm hle
  by_contra hn
  have hlt : diskSq x < 1 := lt_of_not_ge hn
  have hi : x ∈ interior {x : Plane | diskSq x ≤ 1} :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset
      ((isOpen_lt diskSq_continuous continuous_const).mem_nhds hlt) (fun z hz => (show diskSq z < 1 from hz).le))
  exact hx.2 hi

def join (q : Plane × ℝ) : V := ![q.1 0,q.1 1,q.2]
def split (y : V) : Plane × ℝ := (![y 0,y 1],y 2)
lemma join_smooth : ContDiff ℝ ∞ join := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [join] <;> fun_prop
lemma split_smooth : ContDiff ℝ ∞ split := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [split] <;> fun_prop
  · exact contDiff_apply ℝ ℝ 2
lemma join_split (y : V) : join (split y)=y := by ext i; fin_cases i <;> rfl
lemma split_join (q : Plane × ℝ) : split (join q)=q := by
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · rfl

end
end ContactTopology.NormalGraph


open BirkhoffGlobalSection Set
open scoped ContDiff

theorem solution
    (F : EquivariantSphereContactomorphism) (φ ρ : ℝ → Phase → Phase)
    (hφ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => φ p.1 p.2) (t,y))
    (hρ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2) (t,y))
    (hφS : ∀ t, MapsTo (φ t) unitThreeSphere unitThreeSphere)
    (hρS : ∀ t, MapsTo (ρ t) unitThreeSphere unitThreeSphere)
    (hleft : ∀ t y, y ∈ unitThreeSphere → ρ t (φ t y)=y)
    (hboundary : ∀ t (u : Plane), u 0^2+u 1^2=1 →
      φ t (F.toFun ![u 0,u 1,0,0])=F.toFun ![u 0,u 1,0,0]) :
    let D : Set Plane := {u | u 0^2+u 1^2 ≤ 1}
    let disk : Plane → Phase := fun u =>
      ![2*u 0/(1+u 0^2+u 1^2),2*u 1/(1+u 0^2+u 1^2),
        (1-u 0^2-u 1^2)/(1+u 0^2+u 1^2),0]
    ∃ C : Plane × ℝ → Phase, ∃ R : Phase → Plane × ℝ, ∃ N : Set (Plane × ℝ),
      ContDiff ℝ ∞ C ∧ IsOpen N ∧ (∀ u ∈ D, (u,0) ∈ N) ∧
      (∀ z, C z ∈ unitThreeSphere) ∧ (∀ u, C (u,0)=F.toFun (disk u)) ∧
      (∀ z ∈ N, ContDiffAt ℝ ∞ R (C z) ∧ R (C z)=z) ∧
      (∀ z ∈ N, ∃ U : Set Phase, IsOpen U ∧ C z ∈ U ∧
        ∀ y ∈ U, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ O : Set ((ℝ × ℝ) × Plane), IsOpen O ∧
        (Icc (0:ℝ) 1 ×ˢ Icc (-δ) δ) ×ˢ D ⊆ O ∧
        ∃ θ : (ℝ × ℝ) × Plane → Plane, ∃ g : (ℝ × ℝ) × Plane → ℝ,
          ContDiffOn ℝ ∞ θ O ∧ ContDiffOn ℝ ∞ g O ∧
          ∀ t ∈ Icc (0:ℝ) 1, ∀ a : ℝ, |a| ≤ δ →
            (∀ u ∈ D, R (ρ t (φ (t+a) (C (u,0)))) ∈ N ∧
              C (R (ρ t (φ (t+a) (C (u,0)))))=ρ t (φ (t+a) (C (u,0)))) ∧
            BijOn (fun u => (R (ρ t (φ (t+a) (C (u,0))))).1) D D ∧
            (∀ v ∈ D, θ ((t,a),v) ∈ D ∧ (v,g ((t,a),v)) ∈ N ∧
              ρ t (φ (t+a) (C (θ ((t,a),v),0)))=C (v,g ((t,a),v))) ∧
            (∀ u ∈ D, θ ((t,a),(R (ρ t (φ (t+a) (C (u,0))))).1)=u) ∧
            (∀ v ∈ frontier D, g ((t,a),v)=0) ∧
            (fun u => ρ t (φ (t+a) (F.toFun (disk u)))) '' D =
              (fun v => C (v,g ((t,a),v))) '' D := by


  classical
  dsimp only
  let D : Set Plane := {u | u 0^2+u 1^2 ≤ 1}
  let disk : Plane → Phase := fun u =>
    ![2*u 0/(1+u 0^2+u 1^2),2*u 1/(1+u 0^2+u 1^2),
      (1-u 0^2-u 1^2)/(1+u 0^2+u 1^2),0]
  obtain ⟨C₀,R₀,r,N₀,hC₀,hr,hrpos,hN₀,hDN₀,hC₀S,hdisk₀,hEmb,hR₀,hpb,hlocal₀,hchar,hlegend⟩ :=
    ContactTopology.contactomorphic_core_spanning_disk_neighborhood F
  let C : Plane × ℝ → Phase := C₀ ∘ ContactTopology.NormalGraph.join
  let R : Phase → Plane × ℝ := ContactTopology.NormalGraph.split ∘ R₀
  let N : Set (Plane × ℝ) := ContactTopology.NormalGraph.join ⁻¹' N₀
  have hC : ContDiff ℝ ∞ C := hC₀.comp ContactTopology.NormalGraph.join_smooth
  have hN : IsOpen N := hN₀.preimage ContactTopology.NormalGraph.join_smooth.continuous
  have hDN : ∀ u ∈ D, (u,(0:ℝ)) ∈ N := fun u hu => hDN₀ u hu
  have hCS : ∀ z, C z ∈ unitThreeSphere := fun z => hC₀S _
  have hdisk : ∀ u, C (u,0)=F.toFun (disk u) := fun u => hdisk₀ u
  have hR : ∀ z ∈ N, ContDiffAt ℝ ∞ R (C z) ∧ R (C z)=z := by
    intro z hz
    obtain ⟨hRs,hRC,hinj⟩ := hR₀ (ContactTopology.NormalGraph.join z) hz
    refine ⟨ContactTopology.NormalGraph.split_smooth.contDiffAt.comp (C z) hRs,?_⟩
    change ContactTopology.NormalGraph.split (R₀ (C₀ (ContactTopology.NormalGraph.join z)))=z
    rw [hRC,ContactTopology.NormalGraph.split_join]
  have hlocal : ∀ z ∈ N, ∃ U : Set Phase, IsOpen U ∧ C z ∈ U ∧
      ∀ y ∈ U, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y := by
    intro z hz
    obtain ⟨U,hU,hzU,hdata⟩ := hlocal₀ (ContactTopology.NormalGraph.join z) hz
    refine ⟨U,hU,hzU,?_⟩
    intro y hy hyS
    obtain ⟨hRy,hCR⟩ := hdata y hy hyS
    constructor
    · change ContactTopology.NormalGraph.join (ContactTopology.NormalGraph.split (R₀ y)) ∈ N₀
      rwa [ContactTopology.NormalGraph.join_split]
    · change C₀ (ContactTopology.NormalGraph.join (ContactTopology.NormalGraph.split (R₀ y)))=y
      rwa [ContactTopology.NormalGraph.join_split]
  have hboundary' : ∀ t u, u ∈ frontier D → φ t (C (u,0))=C (u,0) := by
    intro t u hu
    have hq : u 0^2+u 1^2=1 := ContactTopology.NormalGraph.disk_frontier_sq u hu
    have hden : 1+u 0^2+u 1^2=2 := by linarith
    have hnum : 1-u 0^2-u 1^2=0 := by linarith
    have hdc : disk u=![u 0,u 1,0,0] := by
      ext i
      fin_cases i <;> simp [disk,hden,hnum]
    rw [hdisk,hdc]
    exact hboundary t u hq
  obtain ⟨δ,hδ,O,hO,hDO,θ,g,hθ,hg,hdata⟩ := ContactTopology.NormalGraph.ambient_isotopy_normal_graph
    D ContactTopology.NormalGraph.disk_compact ContactTopology.NormalGraph.disk_convex
      unitThreeSphere C R N hN hDN hC hCS (fun z hz => (hR z hz).1) (fun z hz => (hR z hz).2)
      hlocal φ ρ hφ hρ hφS hρS hleft hboundary'
  refine ⟨C,R,N,hC,hN,hDN,hCS,hdisk,hR,hlocal,δ,hδ,O,hO,hDO,θ,g,hθ,hg,?_⟩
  intro t ht a ha
  obtain ⟨hcoords,hbij,hgraph,hθleft,hzero,himage⟩ := hdata t ht a ha
  refine ⟨hcoords,hbij,hgraph,hθleft,hzero,?_⟩
  simpa only [hdisk] using himage
