-- Prove2me | solution 1 for ContactTopology.contactomorphic_core_disk_finite_pinched_collars
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:04:46.665988+00:00
-- url     : https://prove2.me/submissions/33c9fadb-79e5-401d-b9ed-fe4806b5c87e

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Theorems.Thm_ContactTopology_contactomorphic_core_disk_isotopy_normal_graph






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



namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Radial boundary comparison, reusing the construction in
NormalMatching.boundary_vanishing_estimate, now including the disk center. -/
lemma disk_boundary_distance (x : Plane) (hx : diskSq x ≤ 1) :
    ∃ p : Plane, diskSq p=1 ∧ ‖x-p‖ ≤ 1-diskSq x := by
  have hnon : 0 ≤ diskSq x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hz : diskSq x=0
  · have hx0 : x=0 := by
      ext i
      fin_cases i <;> simp only [diskSq] at hz <;> dsimp <;>
        nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
    refine ⟨![1,0],by norm_num [diskSq],?_⟩
    rw [hx0]
    norm_num [diskSq,pi_norm_le_iff_of_nonneg,Fin.forall_fin_two]
  let t := Real.sqrt (diskSq x)
  have ht : 0 < t := Real.sqrt_pos.mpr (lt_of_le_of_ne hnon (Ne.symm hz))
  have ht1 : t ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by simpa using hx⟩
  have ht2 : t^2=diskSq x := Real.sq_sqrt hnon
  let p : Plane := t⁻¹ • x
  have hp : diskSq p=1 := by
    have he : diskSq p=diskSq x/t^2 := by dsimp [p]; simp [diskSq,div_eq_mul_inv]; ring
    rw [he,ht2,div_self hz]
  refine ⟨p,hp,?_⟩
  have hq : 0 ≤ 1-diskSq x := sub_nonneg.mpr hx
  apply (pi_norm_le_iff_of_nonneg hq).mpr
  intro i
  have hcomp : x i^2 ≤ diskSq x := by fin_cases i <;> simp [diskSq] <;> positivity
  have hxi : |x i| ≤ t := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have he : x i-p i=x i*(t-1)/t := by
    change x i-t⁻¹*x i=x i*(t-1)/t
    field_simp [ht.ne']
  change |x i-p i| ≤ 1-diskSq x
  rw [he,abs_div,abs_mul,abs_of_pos ht,abs_of_nonpos (by linarith : t-1 ≤ 0)]
  apply (div_le_iff₀ ht).mpr
  have htq : 1-t ≤ 1-diskSq x := by
    nlinarith [mul_nonneg ht.le (show 0 ≤ 1-t by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxi) (show 0 ≤ 1-t by linarith),
    mul_nonneg ht.le (sub_nonneg.mpr htq)]

lemma disk_boundary_vanishing_derivative_estimate (f : Plane → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ x, diskSq x ≤ 1 → DifferentiableAt ℝ f x)
    (hder : ∀ x, diskSq x ≤ 1 → ‖fderiv ℝ f x‖ ≤ ε)
    (hzero : ∀ x, diskSq x=1 → f x=0) :
    ∀ x, diskSq x ≤ 1 → |f x| ≤ ε*(1-diskSq x) := by
  intro x hx
  obtain ⟨p,hp,hdist⟩ := disk_boundary_distance x hx
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hf hder disk_convex hp.le hx
  rw [hzero p hp,sub_zero,Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hdist hε)

lemma disk_uniqueDiff : UniqueDiffOn ℝ {x : Plane | diskSq x ≤ 1} := by
  apply uniqueDiffOn_convex disk_convex
  refine ⟨0,mem_interior_iff_mem_nhds.mpr ?_⟩
  apply mem_of_superset ((isOpen_lt diskSq_continuous continuous_const).mem_nhds
    (show diskSq (0:Plane) < 1 by norm_num [diskSq]))
  intro x hx
  exact (show diskSq x < 1 from hx).le

lemma scalar_slice_derivative (g : (ℝ × ℝ) × Plane → ℝ) (q : (ℝ × ℝ) × Plane)
    (hg : DifferentiableAt ℝ g q) :
    fderiv ℝ (fun x => g (q.1,x)) q.2=
      (fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) Plane) := by
  have hh := (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have he : (0 : Plane →L[ℝ] (ℝ × ℝ)).prod (ContinuousLinearMap.id ℝ Plane)=
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) Plane := by ext z <;> rfl
  rw [he] at hh
  exact (hg.hasFDerivAt.comp q.2 hh).fderiv

/-- On a uniform smaller time interval, a smooth graph vanishing at zero time
and at the boundary lies between arbitrarily thin pinched quadratic graphs. -/
theorem uniform_pinched_height_bound (δ : ℝ) (hδ : 0 < δ)
    (O : Set ((ℝ × ℝ) × Plane)) (hO : IsOpen O)
    (hKO : (Icc (0:ℝ) 1 ×ˢ Icc (-δ) δ) ×ˢ {x : Plane | diskSq x ≤ 1} ⊆ O)
    (g : (ℝ × ℝ) × Plane → ℝ) (hg : ContDiffOn ℝ ∞ g O)
    (hg0 : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, diskSq x ≤ 1 → g ((t,0),x)=0)
    (hgb : ∀ t ∈ Icc (0:ℝ) 1, ∀ a : ℝ, |a| ≤ δ →
      ∀ x, diskSq x=1 → g ((t,a),x)=0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ a : ℝ, |a| ≤ η →
      ∀ x, diskSq x ≤ 1 → |g ((t,a),x)| ≤ ε*(1-diskSq x) := by
  let L : ((ℝ × ℝ) × Plane) → Plane →L[ℝ] ℝ :=
    fun q => fderiv ℝ (fun x => g (q.1,x)) q.2
  have hL : ContinuousOn L O := by
    have hD := hg.continuousOn_fderiv_of_isOpen hO (by simp)
    have hc : ContinuousOn (fun q => (fderiv ℝ g q).comp
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ) Plane)) O := hD.clm_comp continuousOn_const
    exact hc.congr (fun q hq => scalar_slice_derivative g q
      (((hg q hq).contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)))
  have hdiagL : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, diskSq x ≤ 1 → L ((t,0),x)=0 := by
    intro t ht x hx
    have hq : ((t,0),x) ∈ O := hKO ⟨⟨ht,⟨by linarith, hδ.le⟩⟩,hx⟩
    have hgs : DifferentiableAt ℝ (fun z => g ((t,0),z)) x :=
      (((hg _ hq).contDiffAt (hO.mem_nhds hq)).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hz : HasFDerivWithinAt (fun z => g ((t,0),z)) 0 {x : Plane | diskSq x ≤ 1} x :=
      (hasFDerivWithinAt_const (𝕜 := ℝ) (0:ℝ) x _).congr (fun z hz => hg0 t ht z hz) (hg0 t ht x hx)
    exact disk_uniqueDiff.eq hx hgs.hasFDerivAt.hasFDerivWithinAt hz
  let A : Set ((ℝ × ℝ) × Plane) := O ∩ {q | ‖L q‖ < ε}
  have hA : IsOpen A := hL.norm.isOpen_inter_preimage hO isOpen_Iio
  let J : (ℝ × Plane) × ℝ → (ℝ × ℝ) × Plane := fun q => ((q.1.1,q.2),q.1.2)
  have hJ : Continuous J := by fun_prop
  have hKA : (Icc (0:ℝ) 1 ×ˢ {x : Plane | diskSq x ≤ 1}) ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' A := by
    rintro ⟨⟨t,x⟩,a⟩ ⟨⟨ht,hx⟩,ha⟩
    have ha0 : a=0 := ha
    subst a
    refine ⟨hKO ⟨⟨ht,⟨by linarith,hδ.le⟩⟩,hx⟩,?_⟩
    change ‖L ((t,0),x)‖ < ε
    rwa [hdiagL t ht x hx,norm_zero]
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (isCompact_Icc.prod disk_compact)
    isCompact_singleton (hA.preimage hJ) hKA
  have hzV : (0:ℝ) ∈ V := h0V (mem_singleton 0)
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  let η := min δ (r/2)
  have hη : 0 < η := lt_min hδ (by positivity)
  refine ⟨η,hη,min_le_left _ _,?_⟩
  intro t ht a ha
  have haδ : |a| ≤ δ := ha.trans (min_le_left _ _)
  have haV : a ∈ V := hrV (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact lt_of_le_of_lt (ha.trans (min_le_right _ _)) (by linarith))
  have hdata : ∀ x, diskSq x ≤ 1 → ((t,a),x) ∈ O ∧ ‖L ((t,a),x)‖ < ε := by
    intro x hx
    exact hUV (show ((t,x),a) ∈ U ×ˢ V from ⟨hKU ⟨ht,hx⟩,haV⟩)
  apply disk_boundary_vanishing_derivative_estimate _ ε hε.le _ _ (hgb t ht a haδ)
  · intro x hx
    have hq := (hdata x hx).1
    exact (((hg _ hq).contDiffAt (hO.mem_nhds hq)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  · intro x hx
    exact (hdata x hx).2.le

end
end ContactTopology.NormalGraph


namespace ContactTopology.NormalGraph
open Set Function Filter Topology
open scoped ContDiff Topology NNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma compact_disk_vertical_band (N : Set (Plane × ℝ)) (hN : IsOpen N)
    (hDN : ∀ u, diskSq u ≤ 1 → (u,0) ∈ N) :
    ∃ r : ℝ, 0 < r ∧ ∀ u, diskSq u ≤ 1 → ∀ z : ℝ, |z| ≤ r → (u,z) ∈ N := by
  have hD0 : {u : Plane | diskSq u ≤ 1} ×ˢ ({0}:Set ℝ) ⊆ N := by
    rintro ⟨u,z⟩ ⟨hu,hz⟩
    have hz0 : z=0 := hz
    simpa only [hz0] using hDN u hu
  obtain ⟨U,V,hU,hV,hDU,h0V,hUV⟩ := generalized_tube_lemma disk_compact isCompact_singleton hN hD0
  have hzV : (0:ℝ) ∈ V := h0V (mem_singleton 0)
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  refine ⟨r/2,by positivity,?_⟩
  intro u hu z hz
  apply hUV
  refine ⟨hDU hu,hrV ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero]
  exact lt_of_le_of_lt hz (by linarith)

lemma disk_sq_one_frontier (u : Plane) (hu : diskSq u=1) :
    u ∈ frontier {x : Plane | diskSq x ≤ 1} := by
  apply (mem_frontier_iff_notMem_interior (show u ∈ {x : Plane | diskSq x ≤ 1} from hu.le)).mpr
  intro hi
  have hn : ∀ᶠ b : ℝ in 𝓝 (1:ℝ), b • u ∈ {x : Plane | diskSq x ≤ 1} := by
    have hT : Tendsto (fun b : ℝ => b • u) (𝓝 (1:ℝ)) (𝓝 u) := by
      have hc : Continuous (fun b : ℝ => b • u) := continuous_id.smul continuous_const
      simpa only [ContinuousAt,one_smul] using (hc.continuousAt (x := (1:ℝ)))
    exact hT (mem_interior_iff_mem_nhds.mp hi)
  have hn' : ∀ᶠ b : ℝ in 𝓝[>] (1:ℝ), b • u ∈ {x : Plane | diskSq x ≤ 1} :=
    hn.filter_mono nhdsWithin_le_nhds
  obtain ⟨b,hbD,hb1⟩ := (hn'.and self_mem_nhdsWithin).exists
  have heq : diskSq (b • u)=b^2 := by
    calc
      diskSq (b • u)=b^2*diskSq u := by simp [diskSq]; ring
      _=b^2 := by rw [hu,mul_one]
  have hbq : diskSq (b • u) ≤ 1 := hbD
  rw [heq] at hbq
  have hbgt : 1 < b := hb1
  nlinarith

lemma pinched_height_in_band (r : ℝ) (hr : 0 < r) (u : Plane) (hu : diskSq u ≤ 1) :
    |r*(1-diskSq u)| ≤ r := by
  have hq : 0 ≤ diskSq u := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [abs_of_nonneg (mul_nonneg hr.le (sub_nonneg.mpr hu))]
  nlinarith

end
end ContactTopology.NormalGraph


namespace ContactTopology.NormalGraph
open BirkhoffGlobalSection Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma parametrized_chart_graph_immersion
    (C : Plane × ℝ → Phase) (R : Phase → Plane × ℝ) (N : Set (Plane × ℝ))
    (hN : IsOpen N) (hC : ContDiff ℝ ∞ C) (hCS : ∀ z, C z ∈ unitThreeSphere)
    (hR : ∀ z ∈ N, ContDiffAt ℝ ∞ R (C z) ∧ R (C z)=z)
    (φ ρ : ℝ → Phase → Phase)
    (hφ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => φ p.1 p.2) (t,y))
    (hρ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2) (t,y))
    (hφS : ∀ t, MapsTo (φ t) unitThreeSphere unitThreeSphere)
    (hleft : ∀ t y, y ∈ unitThreeSphere → ρ t (φ t y)=y)
    (b : Plane → ℝ) (hb : ContDiff ℝ ∞ b) (t : ℝ) (u : Plane) (hu : (u,b u) ∈ N) :
    Injective (fderiv ℝ (fun v => φ t (C (v,b v))) u) := by
  let f : Plane → Phase := fun v => φ t (C (v,b v))
  let k : Phase → Plane := fun y => (R (ρ t y)).1
  have hf : ContDiffAt ℝ ∞ f u :=
    (hφ t (C (u,b u)) (hCS _)).comp u
      (f := fun v : Plane => (t,C (v,b v)))
      (contDiffAt_const.prodMk (hC.comp (contDiff_id.prodMk hb)).contDiffAt)
  have hρt : ContDiffAt ℝ ∞ (ρ t) (f u) :=
    (hρ t (f u) (hφS t (hCS _))).comp (f u) (contDiffAt_const.prodMk contDiffAt_id)
  have hRp : ContDiffAt ℝ ∞ R (ρ t (f u)) := by
    simpa only [f,hleft t (C (u,b u)) (hCS _)] using (hR (u,b u) hu).1
  have hk : ContDiffAt ℝ ∞ k (f u) := (hRp.comp (f u) hρt).fst
  have heq : (k ∘ f) =ᶠ[𝓝 u] (fun v : Plane => v) := by
    have hn : ∀ᶠ v in 𝓝 u, (v,b v) ∈ N :=
      ((continuous_id.prodMk hb.continuous).continuousAt.preimage_mem_nhds (hN.mem_nhds hu))
    filter_upwards [hn] with v hv
    change (R (ρ t (φ t (C (v,b v))))).1=v
    rw [hleft t _ (hCS _),(hR _ hv).2]
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp u (hk.differentiableAt (by simp)) (hf.differentiableAt (by simp))] at hd
  have hid : fderiv ℝ (fun v : Plane => v) u=ContinuousLinearMap.id ℝ Plane := fderiv_id
  rw [hid] at hd
  intro v w hvw
  have he := congrArg (fderiv ℝ k (f u)) hvw
  change (fderiv ℝ k (f u)).comp (fderiv ℝ f u) v=
    (fderiv ℝ k (f u)).comp (fderiv ℝ f u) w at he
  simpa only [hd,ContinuousLinearMap.id_apply] using he

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
    (hright : ∀ t y, y ∈ unitThreeSphere → φ t (ρ t y)=y)
    (hboundary : ∀ t (u : Plane), u 0^2+u 1^2=1 →
      φ t (F.toFun ![u 0,u 1,0,0])=F.toFun ![u 0,u 1,0,0]) :
    let D : Set Plane := {u | u 0^2+u 1^2 ≤ 1}
    let disk : Plane → Phase := fun u =>
      ![2*u 0/(1+u 0^2+u 1^2),2*u 1/(1+u 0^2+u 1^2),
        (1-u 0^2-u 1^2)/(1+u 0^2+u 1^2),0]
    ∃ C : Plane × ℝ → Phase, ∃ R : Phase → Plane × ℝ, ∃ N : Set (Plane × ℝ),
    ∃ r : ℝ, ∃ m : ℕ, ∃ lower upper : ℝ × Plane → Phase,
      ContDiff ℝ ∞ C ∧ IsOpen N ∧ 0 < r ∧
      (∀ z, C z ∈ unitThreeSphere) ∧ (∀ u, C (u,0)=F.toFun (disk u)) ∧
      (∀ z ∈ N, ContDiffAt ℝ ∞ R (C z) ∧ R (C z)=z) ∧
      (∀ u ∈ D, ∀ z : ℝ, |z| ≤ r → (u,z) ∈ N) ∧
      ContDiff ℝ ∞ lower ∧ ContDiff ℝ ∞ upper ∧
      (∀ t u, lower (t,u)=φ t (C (u,-(r*(1-(u 0^2+u 1^2))))) ∧
        upper (t,u)=φ t (C (u,r*(1-(u 0^2+u 1^2))))) ∧
      (∀ t u, lower (t,u) ∈ unitThreeSphere ∧ upper (t,u) ∈ unitThreeSphere) ∧
      (∀ t, InjOn (fun u => lower (t,u)) D ∧ InjOn (fun u => upper (t,u)) D) ∧
      (∀ t, ∀ u ∈ D, Function.Injective (fderiv ℝ (fun v => lower (t,v)) u) ∧
        Function.Injective (fderiv ℝ (fun v => upper (t,v)) u)) ∧
      (∀ t, ∀ u ∈ D, ∀ v ∈ D,
        (lower (t,u)=upper (t,v) ↔ u=v ∧ u 0^2+u 1^2=1)) ∧
      (∀ t u, u 0^2+u 1^2=1 →
        lower (t,u)=F.toFun ![u 0,u 1,0,0] ∧ upper (t,u)=F.toFun ![u 0,u 1,0,0]) ∧
      ∀ j : ℕ, j ≤ m →
        (j:ℝ)/(m+1:ℝ) ∈ Icc (0:ℝ) 1 ∧
        ∀ s ∈ Icc ((j:ℝ)/(m+1:ℝ)) ((j+1:ℝ)/(m+1:ℝ)), ∀ u ∈ D,
          ∃ v ∈ D, ∃ z : ℝ, |z| ≤ (r/2)*(1-(v 0^2+v 1^2)) ∧
            φ s (F.toFun (disk u))=φ ((j:ℝ)/(m+1:ℝ)) (C (v,z)) := by


  classical
  dsimp only
  let D : Set Plane := {u | u 0^2+u 1^2 ≤ 1}
  let disk : Plane → Phase := fun u =>
    ![2*u 0/(1+u 0^2+u 1^2),2*u 1/(1+u 0^2+u 1^2),
      (1-u 0^2-u 1^2)/(1+u 0^2+u 1^2),0]
  obtain ⟨C,R,N,hC,hN,hDN,hCS,hdisk,hR,hlocal,δ,hδ,O,hO,hKO,θ,g,hθ,hg,hdata⟩ :=
    ContactTopology.contactomorphic_core_disk_isotopy_normal_graph F φ ρ hφ hρ hφS hρS hleft hboundary
  obtain ⟨r,hr,hband⟩ := ContactTopology.NormalGraph.compact_disk_vertical_band N hN hDN
  have hg0 : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, ContactTopology.NormalGraph.diskSq u ≤ 1 → g ((t,0),u)=0 := by
    intro t ht u hu
    obtain ⟨hcoords,hbij,hgraph,hθleft,hzero,himage⟩ := hdata t ht 0 (by simpa using hδ.le)
    obtain ⟨hθu,hug,hgraphu⟩ := hgraph u hu
    have heq : C (θ ((t,0),u),0)=C (u,g ((t,0),u)) := by
      simpa only [add_zero,hleft t _ (hCS _)] using hgraphu
    have hh := congrArg R heq
    rw [(hR _ (hDN _ hθu)).2,(hR _ hug).2] at hh
    exact (congrArg Prod.snd hh).symm
  have hgb : ∀ t ∈ Icc (0:ℝ) 1, ∀ a : ℝ, |a| ≤ δ →
      ∀ u, ContactTopology.NormalGraph.diskSq u=1 → g ((t,a),u)=0 := by
    intro t ht a ha u hu
    have hbd : u ∈ frontier D := ContactTopology.NormalGraph.disk_sq_one_frontier u hu
    exact (hdata t ht a ha).2.2.2.2.1 u hbd
  obtain ⟨η,hη,hηδ,hheight⟩ := ContactTopology.NormalGraph.uniform_pinched_height_bound δ hδ O hO hKO g hg
    hg0 hgb (r/2) (by positivity)
  let q : Plane → ℝ := fun u => 1-(u 0^2+u 1^2)
  have hq : ContDiff ℝ ∞ q := by fun_prop
  let minus : Plane → Plane × ℝ := fun u => (u,-(r*q u))
  let plus : Plane → Plane × ℝ := fun u => (u,r*q u)
  have hminus : ContDiff ℝ ∞ minus := contDiff_id.prodMk (contDiff_const.mul hq).neg
  have hplus : ContDiff ℝ ∞ plus := contDiff_id.prodMk (contDiff_const.mul hq)
  have hminusN : ∀ u ∈ D, minus u ∈ N := by
    intro u hu
    exact hband u hu (-(r*q u)) (by simpa only [abs_neg,q,ContactTopology.NormalGraph.diskSq] using ContactTopology.NormalGraph.pinched_height_in_band r hr u hu)
  have hplusN : ∀ u ∈ D, plus u ∈ N := by
    intro u hu
    exact hband u hu (r*q u) (ContactTopology.NormalGraph.pinched_height_in_band r hr u hu)
  let lower : ℝ × Plane → Phase := fun p => φ p.1 (C (minus p.2))
  let upper : ℝ × Plane → Phase := fun p => φ p.1 (C (plus p.2))
  have hlower : ContDiff ℝ ∞ lower := by
    rw [contDiff_iff_contDiffAt]
    intro p
    exact (hφ p.1 (C (minus p.2)) (hCS _)).comp p
      (f := fun p : ℝ × Plane => (p.1,C (minus p.2)))
      (contDiffAt_fst.prodMk ((hC.comp hminus).comp contDiff_snd).contDiffAt)
  have hupper : ContDiff ℝ ∞ upper := by
    rw [contDiff_iff_contDiffAt]
    intro p
    exact (hφ p.1 (C (plus p.2)) (hCS _)).comp p
      (f := fun p : ℝ × Plane => (p.1,C (plus p.2)))
      (contDiffAt_fst.prodMk ((hC.comp hplus).comp contDiff_snd).contDiffAt)
  have hφinj : ∀ t, InjOn (φ t) unitThreeSphere := by
    intro t x hx y hy heq
    have hh := congrArg (ρ t) heq
    simpa only [hleft t x hx,hleft t y hy] using hh
  have hCinj : InjOn C N := by
    intro x hx y hy heq
    have hh := congrArg R heq
    simpa only [(hR x hx).2,(hR y hy).2] using hh
  have hinj : ∀ t, InjOn (fun u => lower (t,u)) D ∧ InjOn (fun u => upper (t,u)) D := by
    intro t
    constructor
    · intro u hu v hv heq
      have hh := hCinj (hminusN u hu) (hminusN v hv) (hφinj t (hCS _) (hCS _) heq)
      exact congrArg Prod.fst hh
    · intro u hu v hv heq
      have hh := hCinj (hplusN u hu) (hplusN v hv) (hφinj t (hCS _) (hCS _) heq)
      exact congrArg Prod.fst hh
  have himm : ∀ t, ∀ u ∈ D, Function.Injective (fderiv ℝ (fun v => lower (t,v)) u) ∧
      Function.Injective (fderiv ℝ (fun v => upper (t,v)) u) := by
    intro t u hu
    constructor
    · exact ContactTopology.NormalGraph.parametrized_chart_graph_immersion C R N hN hC hCS hR
        φ ρ hφ hρ hφS hleft (fun u => -(r*q u)) (contDiff_const.mul hq).neg t u (hminusN u hu)
    · exact ContactTopology.NormalGraph.parametrized_chart_graph_immersion C R N hN hC hCS hR
        φ ρ hφ hρ hφS hleft (fun u => r*q u) (contDiff_const.mul hq) t u (hplusN u hu)
  have hcross : ∀ t, ∀ u ∈ D, ∀ v ∈ D, lower (t,u)=upper (t,v) ↔ u=v ∧ u 0^2+u 1^2=1 := by
    intro t u hu v hv
    constructor
    · intro heq
      have hh := hCinj (hminusN u hu) (hplusN v hv) (hφinj t (hCS _) (hCS _) heq)
      have huv : u=v := congrArg Prod.fst hh
      refine ⟨huv,?_⟩
      have hz := congrArg Prod.snd hh
      change -(r*q u)=r*q v at hz
      rw [← huv] at hz
      dsimp only [q] at hz
      nlinarith
    · rintro ⟨rfl,huq⟩
      have hz : q u=0 := by simp [q,huq]
      simp only [lower,upper,minus,plus,hz,mul_zero,neg_zero]
  have hdisk_boundary : ∀ u : Plane, u 0^2+u 1^2=1 → disk u=![u 0,u 1,0,0] := by
    intro u hu
    have hden : 1+u 0^2+u 1^2=2 := by linarith
    have hnum : 1-u 0^2-u 1^2=0 := by linarith
    ext i
    fin_cases i <;> simp [disk,hden,hnum]
  have hfixed : ∀ t u, u 0^2+u 1^2=1 →
      lower (t,u)=F.toFun ![u 0,u 1,0,0] ∧ upper (t,u)=F.toFun ![u 0,u 1,0,0] := by
    intro t u hu
    have hz : q u=0 := by simp [q,hu]
    have hd : C (u,0)=F.toFun ![u 0,u 1,0,0] :=
      (hdisk u).trans (congrArg F.toFun (hdisk_boundary u hu))
    simp only [lower,upper,minus,plus,hz,mul_zero,neg_zero,hd,hboundary t u hu,and_self]
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hη
  have hden : 0 < (m+1:ℝ) := by positivity
  refine ⟨C,R,N,r,m,lower,upper,hC,hN,hr,hCS,hdisk,hR,hband,hlower,hupper,
    fun t u => ⟨rfl,rfl⟩,fun t u => ⟨hφS t (hCS _),hφS t (hCS _)⟩,hinj,himm,hcross,hfixed,?_⟩
  intro j hj
  have hjr : (j:ℝ) ≤ m+1 := by exact_mod_cast (Nat.le_trans hj (Nat.le_succ m))
  let t : ℝ := (j:ℝ)/(m+1:ℝ)
  have ht : t ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg j) hden.le,(div_le_one hden).mpr hjr⟩
  refine ⟨ht,?_⟩
  intro s hs u hu
  have ha : |s-t| ≤ η := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have hb : s-t ≤ 1/(m+1:ℝ) := by
      calc
        s-t ≤ (j+1:ℝ)/(m+1:ℝ)-(j:ℝ)/(m+1:ℝ) := sub_le_sub_right hs.2 _
        _=1/(m+1:ℝ) := by ring
    exact (hb.trans_lt hm).le
  have haδ : |s-t| ≤ δ := ha.trans hηδ
  obtain ⟨hcoords,hbij,hgraph,hθleft,hzero,himage⟩ := hdata t ht (s-t) haδ
  let v : Plane := (R (ρ t (φ (t+(s-t)) (C (u,0))))).1
  have hv : v ∈ D := hbij.mapsTo hu
  have heq : ρ t (φ (t+(s-t)) (C (u,0)))=C (v,g ((t,s-t),v)) := by
    have hh := (hgraph v hv).2.2
    rw [hθleft u hu] at hh
    exact hh
  have hsimp : t+(s-t)=s := by ring
  rw [hsimp] at heq
  refine ⟨v,hv,g ((t,s-t),v),hheight t ht (s-t) ha v hv,?_⟩
  have hh := congrArg (φ t) heq
  rw [hright t _ (hφS s (hCS _)),hdisk] at hh
  exact hh
