-- Prove2me | solution 1 for BregmanPPA.IneqMult.lemmaA4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T22:38:16.237786+00:00
-- url     : https://prove2.me/submissions/1334e779-bdfe-498d-ba3f-f278d83f0ff7

import Definitions.Def_BregmanPPA_IneqMult_Program
set_option autoImplicit false
section
set_option autoImplicit false
open Filter Topology
namespace BregmanIneqMultCodex
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- Weak separation in the actual span, with a functional nontrivial on that span. -/
theorem relative_separate_origin (s : Set H) (hs : Convex ℝ s) (hne : s.Nonempty)
    (hzero : (0 : H) ∈ affineSpan ℝ s) (hnot : (0 : H) ∉ s) :
    ∃ L : H →L[ℝ] ℝ, (∀ y ∈ s, 0 ≤ L y) ∧
      ∃ y ∈ Submodule.span ℝ s, L y ≠ 0 := by
  classical
  let A := (affineSpan ℝ s).direction
  have hA : A.toAffineSubspace=affineSpan ℝ s :=
    AffineSubspace.direction_eq_self_iff_zero_mem.mpr hzero
  have hsets : (A : Set H)=(affineSpan ℝ s : Set H) := congrArg (fun p : AffineSubspace ℝ H => (p : Set H)) hA
  let e : A ≃ₜ affineSpan ℝ s := Homeomorph.setCongr hsets
  let S : Set A := ((↑) ⁻¹' s)
  have heq : S=e ⁻¹' ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by ext p; rfl
  have hconv : Convex ℝ S := hs.linear_preimage A.subtype
  have hint : (interior S).Nonempty := by
    obtain ⟨p,hp⟩ := Set.Nonempty.intrinsicInterior hs hne
    obtain ⟨q,hq,he⟩ := mem_intrinsicInterior.mp hp
    refine ⟨e.symm q,?_⟩
    rw [heq,← e.preimage_interior]
    simpa only [Set.mem_preimage,e.apply_symm_apply] using hq
  have hz : (0 : A) ∉ interior S := by
    intro h
    have hi : (0 : A) ∈ S := interior_subset h
    exact hnot hi
  obtain ⟨l,hl,hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point hconv hz hint
  obtain ⟨g,hg⟩ := (-l).toLinearMap.exists_extend
  let L : H →L[ℝ] ℝ := LinearMap.toContinuousLinearMap g
  have hL (a : A) : L a=-(l a) := by
    have hi := congrArg (fun f : A →ₗ[ℝ] ℝ => f a) hg
    exact hi
  refine ⟨L,?_,?_⟩
  · intro y hy
    have hyA : y ∈ A := by
      change y ∈ A.toAffineSubspace
      rw [hA]
      exact subset_affineSpan ℝ s hy
    have hi := hbound ⟨y,hyA⟩ hy
    rw [map_zero] at hi
    rw [hL ⟨y,hyA⟩]
    linarith
  · have he : ∃ a : A, l a ≠ 0 := by
      by_contra hn
      apply hl
      ext a
      by_contra ha
      exact hn ⟨a,ha⟩
    obtain ⟨a,ha⟩ := he
    have haA : (a : H) ∈ affineSpan ℝ s := by
      rw [← hA]; exact a.property
    refine ⟨a,affineSpan_subset_span haA,?_⟩
    rw [hL a]
    exact neg_ne_zero.mpr ha
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n : ℕ}

/-- A supporting linear functional is constant on the affine span at an intrinsic-interior point. -/
theorem intrinsic_support_constant (s : Set (E n)) (x : E n)
    (hx : x ∈ intrinsicInterior ℝ s) (L : E n →L[ℝ] ℝ)
    (hmin : ∀ y ∈ s, L x ≤ L y) : ∀ y ∈ affineSpan ℝ s, L y=L x := by
  obtain ⟨x',hx',heq⟩ := mem_intrinsicInterior.mp hx
  intro y hy
  let l : ℝ →ᵃ[ℝ] E n := AffineMap.lineMap x y
  have hxA : x ∈ affineSpan ℝ s := by rw [← heq]; exact x'.property
  have hlA (t : ℝ) : l t ∈ affineSpan ℝ s := AffineMap.lineMap_mem t hxA hy
  let ls : ℝ → affineSpan ℝ s := fun t => ⟨l t,hlA t⟩
  have hls : Continuous ls := (AffineMap.lineMap_continuous (p := x) (q := y)).subtype_mk hlA
  have hzero : ls 0=x' := by apply Subtype.ext; simp only [ls,l,AffineMap.lineMap_apply_zero,heq]
  have ht : Tendsto ls (𝓝 0) (𝓝 x') := by rw [← hzero]; exact hls.tendsto 0
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), l t ∈ s := by
    have h := ht.eventually (IsOpen.mem_nhds isOpen_interior hx')
    filter_upwards [h] with t hmem
    have hi : ls t ∈ ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := interior_subset hmem
    exact hi
  have hn' : ∀ᶠ t in 𝓝 (0 : ℝ), l (-t) ∈ s := by
    have htneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0 : ℝ))
    exact htneg.eventually hn
  have he : ∀ᶠ t in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < t ∧ l t ∈ s ∧ l (-t) ∈ s := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hn,nhdsWithin_le_nhds hn'] with t ht hp hm
    exact ⟨ht,hp,hm⟩
  obtain ⟨t,ht,hp,hm⟩ := he.exists
  have hi := hmin _ hp
  have hj := hmin _ hm
  simp only [l,AffineMap.lineMap_apply_module,map_add,map_smul,smul_eq_mul] at hi hj
  nlinarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n : ℕ}

theorem common_intrinsic_separator_constant (s t : Set (E n)) (x : E n)
    (hxS : x ∈ intrinsicInterior ℝ s) (hxT : x ∈ intrinsicInterior ℝ t)
    (L : E n →L[ℝ] ℝ) (hsep : ∀ y ∈ s, ∀ z ∈ t, L y ≤ L z) :
    ∀ y ∈ affineSpan ℝ s, ∀ z ∈ affineSpan ℝ t, L y=L z := by
  have hxS' : x ∈ s := intrinsicInterior_subset hxS
  have hxT' : x ∈ t := intrinsicInterior_subset hxT
  have hs : ∀ y ∈ affineSpan ℝ s, L y=L x := by
    have hi := intrinsic_support_constant s x hxS (-L) (by
      intro y hy
      simp only [ContinuousLinearMap.neg_apply]
      exact neg_le_neg (hsep y hy x hxT'))
    intro y hy
    simpa only [ContinuousLinearMap.neg_apply,neg_inj] using hi y hy
  have ht := intrinsic_support_constant t x hxT L (by intro z hz; exact hsep x hxS' z hz)
  intro y hy z hz
  exact (hs y hy).trans (ht z hz).symm

theorem common_intrinsic_separator_annihilates (s t : Set (E n)) (x : E n)
    (hxS : x ∈ intrinsicInterior ℝ s) (hxT : x ∈ intrinsicInterior ℝ t)
    (L : E n →L[ℝ] ℝ) (hsep : ∀ y ∈ s, ∀ z ∈ t, L y ≤ L z) :
    ∀ d ∈ Submodule.span ℝ {d : E n | ∃ y ∈ s, ∃ z ∈ t, d=y-z}, L d=0 := by
  have hc := common_intrinsic_separator_constant s t x hxS hxT L hsep
  have hker : {d : E n | ∃ y ∈ s, ∃ z ∈ t, d=y-z} ⊆ LinearMap.ker L.toLinearMap := by
    rintro d ⟨y,hy,z,hz,rfl⟩
    change L (y-z)=0
    rw [map_sub,hc y (subset_affineSpan ℝ s hy) z (subset_affineSpan ℝ t hz),sub_self]
  have hspan : Submodule.span ℝ {d : E n | ∃ y ∈ s, ∃ z ∈ t, d=y-z} ≤ LinearMap.ker L.toLinearMap :=
    Submodule.span_le.mpr hker
  intro d hd
  exact hspan hd
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}
abbrev WeightedPerturbSpace (n m : ℕ) := (Fin m → E n) × ℝ

noncomputable def weightedPerturbCost (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v x : E n) (xs : Fin m → E n) : ℝ :=
  (∑ i, w i*((F i (xs i)).toReal-(F i x₀).toReal))-inner ℝ v (x-x₀)

def weightedPerturbSet (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) : Set (WeightedPerturbSpace n m) :=
  {p | ∃ x : E n, ∃ xs : Fin m → E n, (∀ i, F i (xs i) ≠ ⊤) ∧
    p.1=(fun i => xs i-x) ∧ weightedPerturbCost F w x₀ v x xs < p.2}

theorem weightedPerturbCost_convex (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i)) (hw : ∀ i, 0 ≤ w i)
    (x₀ v x y : E n) (xs ys : Fin m → E n)
    (hxs : ∀ i, F i (xs i) ≠ ⊤) (hys : ∀ i, F i (ys i) ≠ ⊤)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (∀ i, F i (a • xs i+b • ys i) ≠ ⊤) ∧
    weightedPerturbCost F w x₀ v (a • x+b • y) (fun i => a • xs i+b • ys i) ≤
      a*weightedPerturbCost F w x₀ v x xs+b*weightedPerturbCost F w x₀ v y ys := by
  have hbound (i : Fin m) : F i (a • xs i+b • ys i) ≤
      (((a*(F i (xs i)).toReal+b*(F i (ys i)).toReal : ℝ)) : EReal) := by
    have ex := EReal.coe_toReal (hxs i) ((hF i).1.1 (xs i))
    have ey := EReal.coe_toReal (hys i) ((hF i).1.1 (ys i))
    have hx : (xs i,(F i (xs i)).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
      change F i (xs i) ≤ ((F i (xs i)).toReal : EReal); rw [ex]
    have hy : (ys i,(F i (ys i)).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
      change F i (ys i) ≤ ((F i (ys i)).toReal : EReal); rw [ey]
    exact (hF i).2 hx hy ha hb hab
  have hz : ∀ i, F i (a • xs i+b • ys i) ≠ ⊤ :=
    fun i => ne_of_lt ((hbound i).trans_lt (EReal.coe_lt_top _))
  refine ⟨hz,?_⟩
  have hcoord (i : Fin m) : w i*((F i (a • xs i+b • ys i)).toReal-(F i x₀).toReal) ≤
      a*(w i*((F i (xs i)).toReal-(F i x₀).toReal))+b*(w i*((F i (ys i)).toReal-(F i x₀).toReal)) := by
    have hi := hbound i
    rw [← EReal.coe_toReal (hz i) ((hF i).1.1 _)] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    have hm := mul_le_mul_of_nonneg_left hir (hw i)
    have he := congrArg (fun r : ℝ => r*(w i*(F i x₀).toReal)) hab
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hlin : inner ℝ v (a • x+b • y-x₀)=a*inner ℝ v (x-x₀)+b*inner ℝ v (y-x₀) := by
    simp only [inner_sub_right,inner_add_right,inner_smul_right]
    nlinarith [congrArg (fun r : ℝ => r*inner ℝ v x₀) hab]
  dsimp only [weightedPerturbCost]
  rw [hlin]
  linarith

theorem weightedPerturbSet_convex (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i)) (hw : ∀ i, 0 ≤ w i)
    (x₀ v : E n) : Convex ℝ (weightedPerturbSet F w x₀ v) := by
  rintro p ⟨x,xs,hxs,hp,hpc⟩ q ⟨y,ys,hys,hq,hqc⟩ a b ha hb hab
  have hc := weightedPerturbCost_convex F w hF hw x₀ v x y xs ys hxs hys a b ha hb hab
  refine ⟨a • x+b • y,fun i => a • xs i+b • ys i,hc.1,?_,?_⟩
  · change a • p.1+b • q.1=(fun i => (a • xs i+b • ys i)-(a • x+b • y))
    rw [hp,hq]
    funext i
    change a • (xs i-x)+b • (ys i-y)=(a • xs i+b • ys i)-(a • x+b • y)
    module
  · change weightedPerturbCost F w x₀ v _ _ < a*p.2+b*q.2
    apply hc.2.trans_lt
    by_cases hapos : 0 < a
    · have hi := mul_lt_mul_of_pos_left hpc hapos
      have hj := mul_le_mul_of_nonneg_left hqc.le hb
      linarith
    · have hbpos : 0 < b := by linarith
      have hi := mul_le_mul_of_nonneg_left hpc.le ha
      have hj := mul_lt_mul_of_pos_left hqc hbpos
      linarith

theorem weightedPerturbSet_vertical (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤) (r : ℝ) (hr : 0 < r) :
    (0,r) ∈ weightedPerturbSet F w x₀ v := by
  refine ⟨x₀,fun _ => x₀,hx,?_,?_⟩
  · funext i; simp
  · simpa [weightedPerturbCost] using hr

theorem weightedPerturbSet_origin_span (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤) :
    (0 : WeightedPerturbSpace n m) ∈ affineSpan ℝ (weightedPerturbSet F w x₀ v) := by
  let p : WeightedPerturbSpace n m := (0,1)
  let q : WeightedPerturbSpace n m := (0,2)
  have hp := subset_affineSpan ℝ (weightedPerturbSet F w x₀ v)
    (weightedPerturbSet_vertical F w x₀ v hx 1 (by norm_num))
  have hq := subset_affineSpan ℝ (weightedPerturbSet F w x₀ v)
    (weightedPerturbSet_vertical F w x₀ v hx 2 (by norm_num))
  have hl := AffineMap.lineMap_mem (-1 : ℝ) hp hq
  have he : AffineMap.lineMap p q (-1 : ℝ)=0 := by
    ext <;> norm_num [p,q,AffineMap.lineMap_apply_module]
  rw [he] at hl
  exact hl

theorem weightedPerturbSet_excludes_origin (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n)
    (hbound : ∀ y : E n, (∀ i, F i y ≠ ⊤) → inner ℝ v (y-x₀) ≤
      ∑ i, w i*((F i y).toReal-(F i x₀).toReal)) :
    (0 : WeightedPerturbSpace n m) ∉ weightedPerturbSet F w x₀ v := by
  rintro ⟨x,xs,hxs,hd,hc⟩
  have he : xs=(fun _ => x) := by
    funext i
    have hi := congrFun hd i
    change (0 : E n)=xs i-x at hi
    exact sub_eq_zero.mp hi.symm
  rw [he] at hxs hc
  have hi := hbound x hxs
  change weightedPerturbCost F w x₀ v x (fun _ => x) < 0 at hc
  dsimp only [weightedPerturbCost] at hc
  linarith

theorem weightedPerturb_separator (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i)) (hw : ∀ i, 0 ≤ w i)
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hbound : ∀ y : E n, (∀ i, F i y ≠ ⊤) → inner ℝ v (y-x₀) ≤
      ∑ i, w i*((F i y).toReal-(F i x₀).toReal)) :
    ∃ L : WeightedPerturbSpace n m →L[ℝ] ℝ,
      (∀ y ∈ weightedPerturbSet F w x₀ v, 0 ≤ L y) ∧
      ∃ y ∈ Submodule.span ℝ (weightedPerturbSet F w x₀ v), L y ≠ 0 := by
  exact relative_separate_origin _ (weightedPerturbSet_convex F w hF hw x₀ v)
    ⟨(0,1),weightedPerturbSet_vertical F w x₀ v hx 1 (by norm_num)⟩
    (weightedPerturbSet_origin_span F w x₀ v hx) (weightedPerturbSet_excludes_origin F w x₀ v hbound)
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

noncomputable def weightedCoordInjection (i : Fin m) : E n →L[ℝ] WeightedPerturbSpace n m :=
  LinearMap.toContinuousLinearMap ((LinearMap.inl ℝ (Fin m → E n) ℝ).comp
    (LinearMap.single ℝ (fun _ : Fin m => E n) i))
noncomputable def weightedCoordFunctional (L : WeightedPerturbSpace n m →L[ℝ] ℝ) (i : Fin m) : E n →L[ℝ] ℝ :=
  L.comp (weightedCoordInjection i)
def weightedVertical (L : WeightedPerturbSpace n m →L[ℝ] ℝ) : ℝ := L (0,1)

theorem weightedCoordFunctional_apply (L : WeightedPerturbSpace n m →L[ℝ] ℝ) (i : Fin m) (x : E n) :
    weightedCoordFunctional L i x=L (Pi.single i x,0) := rfl

theorem weightedSeparator_split (L : WeightedPerturbSpace n m →L[ℝ] ℝ) (d : Fin m → E n) (r : ℝ) :
    L (d,r)=(∑ i, weightedCoordFunctional L i (d i))+r*weightedVertical L := by
  classical
  have he : (d,r)=(∑ i : Fin m, (Pi.single i (d i), (0 : ℝ)))+r • (0,1) := by
    ext <;> simp [Prod.fst_sum,Prod.snd_sum,LinearMap.sum_single_apply]
  rw [he,map_add,map_sum,map_smul]
  simp only [weightedCoordFunctional_apply,weightedVertical,smul_eq_mul]

theorem weightedSeparator_cost_bound (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) (L : WeightedPerturbSpace n m →L[ℝ] ℝ)
    (hL : ∀ p ∈ weightedPerturbSet F w x₀ v, 0 ≤ L p)
    (x : E n) (xs : Fin m → E n) (hxs : ∀ i, F i (xs i) ≠ ⊤) :
    0 ≤ L ((fun i => xs i-x),weightedPerturbCost F w x₀ v x xs) := by
  let d : Fin m → E n := fun i => xs i-x
  let r := weightedPerturbCost F w x₀ v x xs
  have hc : Continuous (fun ε : ℝ => L (d,r+ε)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => L (d,r+ε)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (L (d,r))) := by
    simpa only [add_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hL _ ⟨x,xs,hxs,rfl,by change r < r+ε; exact lt_add_of_pos_right _ hε⟩

theorem weightedSeparator_central_identity (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (L : WeightedPerturbSpace n m →L[ℝ] ℝ)
    (hL : ∀ p ∈ weightedPerturbSet F w x₀ v, 0 ≤ L p) (z : E n) :
    (∑ i, weightedCoordFunctional L i z)=-weightedVertical L*inner ℝ v z := by
  have h1 := weightedSeparator_cost_bound F w x₀ v L hL (x₀+z) (fun _ => x₀) hx
  have h2 := weightedSeparator_cost_bound F w x₀ v L hL (x₀-z) (fun _ => x₀) hx
  have hd1 : (fun i : Fin m => (fun _ : Fin m => x₀) i-(x₀+z))=(fun _ => -z) := by funext i; abel
  have hd2 : (fun i : Fin m => (fun _ : Fin m => x₀) i-(x₀-z))=(fun _ => z) := by funext i; abel
  have hc1 : weightedPerturbCost F w x₀ v (x₀+z) (fun _ => x₀)=-inner ℝ v z := by simp [weightedPerturbCost]
  have hc2 : weightedPerturbCost F w x₀ v (x₀-z) (fun _ => x₀)=inner ℝ v z := by simp [weightedPerturbCost]
  rw [hd1,hc1,weightedSeparator_split] at h1
  rw [hd2,hc2,weightedSeparator_split] at h2
  simp only [map_neg,Finset.sum_neg_distrib] at h1
  nlinarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem weightedSeparator_vertical_positive (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (hri : ∃ x : E n, ∀ i, x ∈ intrinsicInterior ℝ {y : E n | F i y ≠ ⊤})
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (L : WeightedPerturbSpace n m →L[ℝ] ℝ)
    (hL : ∀ p ∈ weightedPerturbSet F w x₀ v, 0 ≤ L p)
    (hnonzero : ∃ y ∈ Submodule.span ℝ (weightedPerturbSet F w x₀ v), L y ≠ 0) :
    0 < weightedVertical L := by
  classical
  have ha : 0 ≤ weightedVertical L := hL _ (weightedPerturbSet_vertical F w x₀ v hx 1 (by norm_num))
  by_contra hapos
  have ha0 : weightedVertical L=0 := le_antisymm (le_of_not_gt hapos) ha
  obtain ⟨xc,hxc⟩ := hri
  have hcfinite : ∀ i, F i xc ≠ ⊤ := fun i => intrinsicInterior_subset (hxc i)
  have hmin (i : Fin m) : ∀ y ∈ {y : E n | F i y ≠ ⊤}, weightedCoordFunctional L i xc ≤ weightedCoordFunctional L i y := by
    intro y hy
    change F i y ≠ ⊤ at hy
    let xs : Fin m → E n := fun j => if j=i then y else xc
    have hxs : ∀ j, F j (xs j) ≠ ⊤ := by
      intro j
      by_cases hj : j=i
      · subst j; simpa only [xs,if_pos rfl] using hy
      · simpa only [xs,if_neg hj] using hcfinite j
    have hd : (fun j => xs j-xc)=Pi.single i (y-xc) := by
      funext j
      by_cases hj : j=i
      · subst j; simp [xs,Pi.single_apply]
      · simp [xs,hj,Pi.single_apply,Ne.symm hj]
    have hb := weightedSeparator_cost_bound F w x₀ v L hL xc xs hxs
    rw [hd,weightedSeparator_split,ha0,mul_zero,add_zero] at hb
    have he : (∑ j, weightedCoordFunctional L j ((Pi.single i (y-xc) : Fin m → E n) j))=weightedCoordFunctional L i (y-xc) := by
      simp [Pi.single_apply,apply_ite]
    rw [he,map_sub] at hb
    linarith
  have hflat (i : Fin m) (y : E n) (hy : F i y ≠ ⊤) :
      weightedCoordFunctional L i y=weightedCoordFunctional L i xc :=
    intrinsic_support_constant _ xc (hxc i) (weightedCoordFunctional L i) (hmin i) y
      (subset_affineSpan ℝ _ hy)
  have hcentral (y : E n) : (∑ i, weightedCoordFunctional L i y)=0 := by
    simpa only [ha0,neg_zero,zero_mul] using weightedSeparator_central_identity F w x₀ v hx L hL y
  have hzero : ∀ p ∈ weightedPerturbSet F w x₀ v, L p=0 := by
    rintro p ⟨x,xs,hxs,hp,hpc⟩
    change L (p.1,p.2)=0
    rw [weightedSeparator_split,hp,ha0,mul_zero,add_zero]
    simp only [map_sub,Finset.sum_sub_distrib]
    have he : (∑ i, weightedCoordFunctional L i (xs i))=∑ i, weightedCoordFunctional L i xc :=
      Finset.sum_congr rfl (fun i _ => hflat i (xs i) (hxs i))
    rw [he,hcentral xc,hcentral x,sub_self]
  have hker : weightedPerturbSet F w x₀ v ⊆ LinearMap.ker L.toLinearMap := hzero
  have hs : Submodule.span ℝ (weightedPerturbSet F w x₀ v) ≤ LinearMap.ker L.toLinearMap := Submodule.span_le.mpr hker
  obtain ⟨y,hy,hny⟩ := hnonzero
  exact hny (hs hy)
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

noncomputable def weightedSeparatorVector (L : WeightedPerturbSpace n m →L[ℝ] ℝ) (i : Fin m) : E n :=
  (-(weightedVertical L)⁻¹) • (InnerProductSpace.toDual ℝ (E n)).symm (weightedCoordFunctional L i)

theorem weightedSeparatorVector_pairing (L : WeightedPerturbSpace n m →L[ℝ] ℝ) (i : Fin m) (y : E n) :
    inner ℝ (weightedSeparatorVector L i) y=(-(weightedVertical L)⁻¹)*weightedCoordFunctional L i y := by
  simp only [weightedSeparatorVector,real_inner_smul_left,InnerProductSpace.toDual_symm_apply]

theorem weightedSeparatorVector_sum (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (L : WeightedPerturbSpace n m →L[ℝ] ℝ)
    (hL : ∀ p ∈ weightedPerturbSet F w x₀ v, 0 ≤ L p) (ha : 0 < weightedVertical L) :
    (∑ i, weightedSeparatorVector L i)=v := by
  apply ext_inner_right ℝ
  intro z
  rw [sum_inner]
  simp_rw [weightedSeparatorVector_pairing]
  rw [← Finset.mul_sum,weightedSeparator_central_identity F w x₀ v hx L hL z]
  field_simp [ha.ne']

theorem weightedSeparatorVector_bound (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (L : WeightedPerturbSpace n m →L[ℝ] ℝ)
    (hL : ∀ p ∈ weightedPerturbSet F w x₀ v, 0 ≤ L p) (ha : 0 < weightedVertical L)
    (i : Fin m) (y : E n) (hy : F i y ≠ ⊤) :
    inner ℝ (weightedSeparatorVector L i) (y-x₀) ≤ w i*((F i y).toReal-(F i x₀).toReal) := by
  classical
  let xs : Fin m → E n := fun j => if j=i then y else x₀
  have hxs : ∀ j, F j (xs j) ≠ ⊤ := by
    intro j
    by_cases hj : j=i
    · subst j; simpa only [xs,if_pos rfl] using hy
    · simpa only [xs,if_neg hj] using hx j
  have hd : (fun j => xs j-x₀)=Pi.single i (y-x₀) := by
    funext j
    by_cases hj : j=i
    · subst j; simp [xs,Pi.single_apply]
    · simp [xs,hj,Pi.single_apply,Ne.symm hj]
  have hterm (j : Fin m) : w j*((F j (xs j)).toReal-(F j x₀).toReal)=
      if j=i then w i*((F i y).toReal-(F i x₀).toReal) else 0 := by
    by_cases hj : j=i
    · subst j; simp [xs]
    · simp [xs,hj]
  have hc : weightedPerturbCost F w x₀ v x₀ xs=w i*((F i y).toReal-(F i x₀).toReal) := by
    dsimp only [weightedPerturbCost]
    simp_rw [hterm]
    simp
  have hb := weightedSeparator_cost_bound F w x₀ v L hL x₀ xs hxs
  rw [hd,hc,weightedSeparator_split] at hb
  have he : (∑ j, weightedCoordFunctional L j ((Pi.single i (y-x₀) : Fin m → E n) j))=weightedCoordFunctional L i (y-x₀) := by
    simp [Pi.single_apply,apply_ite]
  rw [he] at hb
  have hm := mul_nonneg (inv_nonneg.mpr ha.le) hb
  have heq : (weightedVertical L)⁻¹*(weightedCoordFunctional L i (y-x₀)+
      (w i*((F i y).toReal-(F i x₀).toReal))*weightedVertical L)=
      (weightedVertical L)⁻¹*weightedCoordFunctional L i (y-x₀)+w i*((F i y).toReal-(F i x₀).toReal) := by
    field_simp [ha.ne'] <;> ring
  rw [heq] at hm
  rw [weightedSeparatorVector_pairing]
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem qualified_weighted_decomposition (F : Fin m → E n → EReal) (w : Fin m → ℝ)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i)) (hw : ∀ i, 0 ≤ w i)
    (hri : ∃ x : E n, ∀ i, x ∈ intrinsicInterior ℝ {y : E n | F i y ≠ ⊤})
    (x₀ v : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hbound : ∀ y : E n, (∀ i, F i y ≠ ⊤) → inner ℝ v (y-x₀) ≤
      ∑ i, w i*((F i y).toReal-(F i x₀).toReal)) :
    ∃ ν : E n, ν ∈ normalCone {x | ∀ i, F i x ≠ ⊤} x₀ ∧
      ∃ ξ : Fin m → E n, (∀ i, w i ≠ 0 → IsSubgradient (F i) x₀ (ξ i)) ∧
        v=ν+∑ i, w i • ξ i := by
  classical
  obtain ⟨L,hL,hnonzero⟩ := weightedPerturb_separator F w hF hw x₀ v hx hbound
  have ha := weightedSeparator_vertical_positive F w hri x₀ v hx L hL hnonzero
  let Q : Fin m → E n := weightedSeparatorVector L
  let ν : E n := ∑ i, if w i=0 then Q i else 0
  let ξ : Fin m → E n := fun i => if w i=0 then 0 else (w i)⁻¹ • Q i
  have hQ (i : Fin m) (y : E n) (hy : F i y ≠ ⊤) :
      inner ℝ (Q i) (y-x₀) ≤ w i*((F i y).toReal-(F i x₀).toReal) :=
    weightedSeparatorVector_bound F w x₀ v hx L hL ha i y hy
  refine ⟨ν,⟨hx,?_⟩,ξ,?_,?_⟩
  · intro y hy
    change ∀ i, F i y ≠ ⊤ at hy
    dsimp only [ν]
    rw [sum_inner]
    apply Finset.sum_nonpos
    intro i hi
    by_cases hwz : w i=0
    · simp only [if_pos hwz]
      simpa only [hwz,zero_mul] using hQ i y (hy i)
    · simp only [if_neg hwz,inner_zero_left]; exact le_rfl
  · intro i hi
    have he : ξ i=(w i)⁻¹ • Q i := by simp only [ξ,if_neg hi]
    refine ⟨hx i,?_⟩
    intro y
    by_cases hy : F i y=⊤
    · rw [hy]; exact le_top
    have ex := EReal.coe_toReal (hx i) ((hF i).1.1 x₀)
    have ey := EReal.coe_toReal hy ((hF i).1.1 y)
    have hm := mul_le_mul_of_nonneg_left (hQ i y hy) (inv_nonneg.mpr (hw i))
    have hb : inner ℝ (ξ i) (y-x₀) ≤ (F i y).toReal-(F i x₀).toReal := by
      rw [he,real_inner_smul_left]
      simpa only [← mul_assoc,inv_mul_cancel₀ hi,one_mul] using hm
    rw [← ex,← ey,← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    linarith
  · have hs : (∑ i, Q i)=v := weightedSeparatorVector_sum F w x₀ v hx L hL ha
    rw [← hs]
    dsimp only [ν,ξ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hwz : w i=0
    · simp [hwz]
    · simp [hwz,smul_smul,mul_inv_cancel₀ hwz]
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem composite_epi_finite (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (x : E n) (r : ℝ) (hx : compositeFn F F₀ x ≤ (r : EReal)) :
    (∀ i, F i x ≠ ⊤) ∧ F₀ (gvec F x) ≤ (r : EReal) := by
  classical
  have hfinite : ∀ i, F i x ≠ ⊤ := by
    by_contra hn
    simp only [compositeFn,if_neg hn] at hx
    exact EReal.coe_ne_top r (top_le_iff.mp hx)
  exact ⟨hfinite,by simpa only [compositeFn,if_pos hfinite] using hx⟩

theorem original_composite_convex (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hF₀ : IsConvexFn F₀)
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v) :
    IsConvexFn (compositeFn F F₀) := by
  classical
  intro u hu v hv a b ha hb hab
  have eu := composite_epi_finite F F₀ u.1 u.2 hu
  have ev := composite_epi_finite F F₀ v.1 v.2 hv
  let z := a • u.1+b • v.1
  have hbnd (i : Fin m) : F i z ≤ (((a*(F i u.1).toReal+b*(F i v.1).toReal : ℝ)) : EReal) := by
    have ex := EReal.coe_toReal (eu.1 i) ((hF i).1.1 u.1)
    have ey := EReal.coe_toReal (ev.1 i) ((hF i).1.1 v.1)
    have hx : (u.1,(F i u.1).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
      change F i u.1 ≤ ((F i u.1).toReal : EReal); rw [ex]
    have hy : (v.1,(F i v.1).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
      change F i v.1 ≤ ((F i v.1).toReal : EReal); rw [ey]
    exact (hF i).2 hx hy ha hb hab
  have hz : ∀ i, F i z ≠ ⊤ := fun i => ne_of_lt ((hbnd i).trans_lt (EReal.coe_lt_top _))
  have hvec : ∀ i, gvec F z i ≤ (a • gvec F u.1+b • gvec F v.1) i := by
    intro i
    have hi := hbnd i
    rw [← EReal.coe_toReal (hz i) ((hF i).1.1 z)] at hi
    exact EReal.coe_le_coe_iff.mp hi
  have houter := hmono _ _ hvec
  have hx : (gvec F u.1,u.2) ∈ {p : E m × ℝ | F₀ p.1 ≤ (p.2 : EReal)} := eu.2
  have hy : (gvec F v.1,v.2) ∈ {p : E m × ℝ | F₀ p.1 ≤ (p.2 : EReal)} := ev.2
  have hc := hF₀ hx hy ha hb hab
  change compositeFn F F₀ z ≤ (((a*u.2+b*v.2 : ℝ)) : EReal)
  rw [compositeFn,if_pos hz]
  exact houter.trans hc

theorem original_composite_proper_at (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF₀ : IsProperFn F₀) (x₀ : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hnear : ∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤) : IsProperFn (compositeFn F F₀) := by
  classical
  refine ⟨?_,x₀,?_⟩
  · intro x
    by_cases hi : ∀ i, F i x ≠ ⊤
    · simp only [compositeFn,if_pos hi]; exact hF₀.1 _
    · simp only [compositeFn,if_neg hi]; exact top_ne_bot
  · simp only [compositeFn,if_pos hx]
    exact hnear.self_of_nhds
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem convex_differentiable_subgradient (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (z : E m) (hz : F z ≠ ⊤)
    (hd : DifferentiableAt ℝ (fun q => (F q).toReal) z) :
    IsSubgradient F z (gradient (fun q => (F q).toReal) z) := by
  refine ⟨hz,?_⟩
  intro y
  by_cases hy : F y=⊤
  · rw [hy]; exact le_top
  have ez := EReal.coe_toReal hz (hp.1 z)
  have ey := EReal.coe_toReal hy (hp.1 y)
  let l : ℝ →ᵃ[ℝ] E m := AffineMap.lineMap z y
  let G : E m → ℝ := fun q => (F q).toReal
  have hder : HasDerivAt (G ∘ l) (inner ℝ (gradient G z) (y-z)) 0 := by
    simpa only [G,InnerProductSpace.toDual_apply_apply] using
      hd.hasGradientAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ))) (by simp [l])
  have hb : ∀ t : ℝ, 0 < t → t < 1 → t⁻¹*(G (l t)-G z) ≤ G y-G z := by
    intro t ht ht1
    have hx : (z,(F z).toReal) ∈ {p : E m × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F z ≤ ((F z).toReal : EReal); rw [ez]
    have hy' : (y,(F y).toReal) ∈ {p : E m × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F y ≤ ((F y).toReal : EReal); rw [ey]
    have hi := hc hx hy' (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    change F ((1-t) • z+t • y) ≤ (((1-t)*(F z).toReal+t*(F y).toReal : ℝ) : EReal) at hi
    have hl : l t=(1-t) • z+t • y := by simp [l,AffineMap.lineMap_apply_module]
    rw [← hl] at hi
    have hft : F (l t) ≠ ⊤ := ne_of_lt (hi.trans_lt (EReal.coe_lt_top _))
    rw [← EReal.coe_toReal hft (hp.1 (l t))] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ ht).mpr
    dsimp only [G]
    nlinarith
  have hi : inner ℝ (gradient G z) (y-z) ≤ G y-G z := by
    apply le_of_tendsto hder.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    simpa only [Function.comp_def,zero_add,smul_eq_mul,l,AffineMap.lineMap_apply_zero] using hb t ht ht1
  rw [← ez,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  dsimp only [G] at hi
  linarith

theorem monotone_gradient_nonnegative (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F u ≤ F v)
    (z : E m) (hz : F z ≠ ⊤) (hd : DifferentiableAt ℝ (fun q => (F q).toReal) z) :
    ∀ i, 0 ≤ (gradient (fun q => (F q).toReal) z) i := by
  classical
  intro i
  let e := EuclideanSpace.single i (1 : ℝ)
  have he : ∀ j, (z-e) j ≤ z j := by
    intro j
    change z j-e j ≤ z j
    have hn : 0 ≤ e j := by simp only [e,EuclideanSpace.single_apply]; split_ifs <;> norm_num
    linarith
  have hm := hmono _ _ he
  have hyt : F (z-e) ≠ ⊤ := ne_of_lt (hm.trans_lt (lt_top_iff_ne_top.mpr hz))
  have hs := (convex_differentiable_subgradient F hp hc z hz hd).2 (z-e)
  have ez := EReal.coe_toReal hz (hp.1 z)
  have ey := EReal.coe_toReal hyt (hp.1 (z-e))
  rw [← ez,← ey,← EReal.coe_add] at hs
  rw [← ez,← ey] at hm
  have hir := EReal.coe_le_coe_iff.mp hs
  have hmr := EReal.coe_le_coe_iff.mp hm
  have hv : inner ℝ (gradient (fun q => (F q).toReal) z) (z-e-z)=
      -(gradient (fun q => (F q).toReal) z) i := by
    have heq : z-e-z=-e := by abel
    rw [heq,inner_neg_right]
    rw [show e=EuclideanSpace.single i (1 : ℝ) from rfl,EuclideanSpace.inner_single_right]
    simp only [one_mul,starRingEnd_apply,star_trivial]
  rw [hv] at hir
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem composite_chain_rhs_subgradient (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hF₀ : IsProperFn F₀ ∧ IsConvexFn F₀)
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v)
    (x₀ : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hnear : ∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤)
    (hd : DifferentiableAt ℝ (fun z : E m => (F₀ z).toReal) (gvec F x₀))
    (ν : E n) (hν : ν ∈ normalCone {x | compositeFn F F₀ x ≠ ⊤} x₀)
    (ξ : Fin m → E n)
    (hξ : ∀ i, (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) i ≠ 0 →
      IsSubgradient (F i) x₀ (ξ i)) :
    IsSubgradient (compositeFn F F₀) x₀
      (ν+∑ i, (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) i • ξ i) := by
  classical
  let w := gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)
  have hft : F₀ (gvec F x₀) ≠ ⊤ := hnear.self_of_nhds
  have hw : ∀ i, 0 ≤ w i := monotone_gradient_nonnegative F₀ hF₀.1 hF₀.2 hmono _ hft hd
  have hs := convex_differentiable_subgradient F₀ hF₀.1 hF₀.2 _ hft hd
  have hp := original_composite_proper_at F F₀ hF₀.1 x₀ hx hnear
  have he₀ : compositeFn F F₀ x₀=F₀ (gvec F x₀) := by simp only [compositeFn,if_pos hx]
  have hxG : compositeFn F F₀ x₀ ≠ ⊤ := by rw [he₀]; exact hft
  refine ⟨hxG,?_⟩
  intro y
  by_cases hy : compositeFn F F₀ y=⊤
  · rw [hy]; exact le_top
  have ex := EReal.coe_toReal hxG (hp.1 x₀)
  have ey := EReal.coe_toReal hy (hp.1 y)
  have hyF := (composite_epi_finite F F₀ y (compositeFn F F₀ y).toReal (by rw [ey])).1
  have hey : compositeFn F F₀ y=F₀ (gvec F y) := by simp only [compositeFn,if_pos hyF]
  have houter := hs.2 (gvec F y)
  rw [← he₀,← hey,← ex,← ey,← EReal.coe_add] at houter
  have hout := EReal.coe_le_coe_iff.mp houter
  have hcoord (i : Fin m) : w i*inner ℝ (ξ i) (y-x₀) ≤
      w i*((F i y).toReal-(F i x₀).toReal) := by
    by_cases hi : w i=0
    · simp only [hi,zero_mul,le_refl]
    · have hsi := (hξ i hi).2 y
      have exi := EReal.coe_toReal (hx i) ((hF i).1.1 x₀)
      have eyi := EReal.coe_toReal (hyF i) ((hF i).1.1 y)
      rw [← exi,← eyi,← EReal.coe_add] at hsi
      have hr := EReal.coe_le_coe_iff.mp hsi
      apply mul_le_mul_of_nonneg_left _ (hw i)
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  have hinner : inner ℝ w (gvec F y-gvec F x₀)=∑ i, w i*((F i y).toReal-(F i x₀).toReal) := by
    simp only [PiLp.inner_apply,Real.inner_apply,PiLp.sub_apply]
    rfl
  rw [← hinner] at hsum
  have hn := hν.2 y hy
  rw [← ex,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  change (compositeFn F F₀ x₀).toReal+inner ℝ (ν+∑ i, w i • ξ i) (y-x₀) ≤ (compositeFn F F₀ y).toReal
  simp only [inner_add_left,sum_inner,real_inner_smul_left]
  change (compositeFn F F₀ x₀).toReal+inner ℝ w (gvec F y-gvec F x₀) ≤ (compositeFn F F₀ y).toReal at hout
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem composite_subgradient_weighted_bound (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i)) (hF₀ : IsProperFn F₀)
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v)
    (x₀ : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hnear : ∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤)
    (hd : DifferentiableAt ℝ (fun z : E m => (F₀ z).toReal) (gvec F x₀))
    (v : E n) (hs : IsSubgradient (compositeFn F F₀) x₀ v) :
    ∀ y : E n, (∀ i, F i y ≠ ⊤) → inner ℝ v (y-x₀) ≤
      inner ℝ (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) (gvec F y-gvec F x₀) := by
  intro y hy
  let l : ℝ →ᵃ[ℝ] E m := AffineMap.lineMap (gvec F x₀) (gvec F y)
  let M : E m → ℝ := fun z => (F₀ z).toReal
  have hder : HasDerivAt (M ∘ l)
      (inner ℝ (gradient M (gvec F x₀)) (gvec F y-gvec F x₀)) 0 := by
    simpa only [M,InnerProductSpace.toDual_apply_apply] using
      hd.hasGradientAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := gvec F x₀) (b := gvec F y) (x := (0 : ℝ))) (by simp [l])
  have hlt : Tendsto (fun t => l t) (𝓝 0) (𝓝 (gvec F x₀)) := by
    simpa only [l,AffineMap.lineMap_apply_zero] using (AffineMap.lineMap_continuous (p := gvec F x₀) (q := gvec F y)).tendsto (0 : ℝ)
  have hnt : ∀ᶠ t in 𝓝 (0 : ℝ), F₀ (l t) ≠ ⊤ := hlt.eventually hnear
  have hbase : compositeFn F F₀ x₀=F₀ (gvec F x₀) := by simp only [compositeFn,if_pos hx]
  have hb : ∀ t : ℝ, 0 < t → t < 1 → F₀ (l t) ≠ ⊤ →
      inner ℝ v (y-x₀) ≤ t⁻¹*(M (l t)-M (gvec F x₀)) := by
    intro t ht ht1 hFt
    let xt := (1-t) • x₀+t • y
    have hcoord (i : Fin m) : F i xt ≤ (((1-t)*(F i x₀).toReal+t*(F i y).toReal : ℝ) : EReal) := by
      have ex := EReal.coe_toReal (hx i) ((hF i).1.1 x₀)
      have ey := EReal.coe_toReal (hy i) ((hF i).1.1 y)
      have hx' : (x₀,(F i x₀).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
        change F i x₀ ≤ ((F i x₀).toReal : EReal); rw [ex]
      have hy' : (y,(F i y).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
        change F i y ≤ ((F i y).toReal : EReal); rw [ey]
      exact (hF i).2 hx' hy' (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    have hfinite : ∀ i, F i xt ≠ ⊤ := fun i => ne_of_lt ((hcoord i).trans_lt (EReal.coe_lt_top _))
    have hvec : ∀ i, gvec F xt i ≤ (l t) i := by
      intro i
      have hi := hcoord i
      rw [← EReal.coe_toReal (hfinite i) ((hF i).1.1 xt)] at hi
      have hir := EReal.coe_le_coe_iff.mp hi
      simpa only [l,AffineMap.lineMap_apply_module,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,gvec,WithLp.equiv_symm_apply,WithLp.ofLp_toLp] using hir
    have hupper : compositeFn F F₀ xt ≤ F₀ (l t) := by
      rw [compositeFn,if_pos hfinite]
      exact hmono _ _ hvec
    have hi := (hs.2 xt).trans hupper
    rw [hbase,← EReal.coe_toReal hnear.self_of_nhds (hF₀.1 _),
      ← EReal.coe_toReal hFt (hF₀.1 _),← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    have he : xt-x₀=t • (y-x₀) := by dsimp only [xt]; module
    rw [he,inner_smul_right] at hir
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ht).mpr
    dsimp only [M]
    linarith
  apply ge_of_tendsto hder.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),nhdsWithin_le_nhds hnt] with t ht ht1 hFt
  simpa only [Function.comp_def,zero_add,smul_eq_mul,l,AffineMap.lineMap_apply_zero] using hb t ht ht1 hFt
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem composite_segment_finite (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v)
    (x y : E n) (hx : ∀ i, F i x ≠ ⊤) (hy : ∀ i, F i y ≠ ⊤)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (ht : F₀ (a • gvec F x+b • gvec F y) ≠ ⊤) :
    compositeFn F F₀ (a • x+b • y) ≠ ⊤ := by
  classical
  let z := a • x+b • y
  have hbound (i : Fin m) : F i z ≤ (((a*(F i x).toReal+b*(F i y).toReal : ℝ)) : EReal) := by
    have ex := EReal.coe_toReal (hx i) ((hF i).1.1 x)
    have ey := EReal.coe_toReal (hy i) ((hF i).1.1 y)
    have hx' : (x,(F i x).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
      change F i x ≤ ((F i x).toReal : EReal); rw [ex]
    have hy' : (y,(F i y).toReal) ∈ {p : E n × ℝ | F i p.1 ≤ (p.2 : EReal)} := by
      change F i y ≤ ((F i y).toReal : EReal); rw [ey]
    exact (hF i).2 hx' hy' ha hb hab
  have hz : ∀ i, F i z ≠ ⊤ := fun i => ne_of_lt ((hbound i).trans_lt (EReal.coe_lt_top _))
  have hv : ∀ i, gvec F z i ≤ (a • gvec F x+b • gvec F y) i := by
    intro i
    have hi := hbound i
    rw [← EReal.coe_toReal (hz i) ((hF i).1.1 z)] at hi
    exact EReal.coe_le_coe_iff.mp hi
  have houter := hmono _ _ hv
  change compositeFn F F₀ z ≠ ⊤
  rw [compositeFn,if_pos hz]
  exact ne_of_lt (houter.trans_lt (lt_top_iff_ne_top.mpr ht))

theorem composite_domain_normal_eq (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v)
    (x₀ : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hnear : ∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤) :
    normalCone {x | compositeFn F F₀ x ≠ ⊤} x₀=
      normalCone {x | ∀ i, F i x ≠ ⊤} x₀ := by
  classical
  ext ν
  constructor
  · intro hn
    refine ⟨hx,?_⟩
    intro y hy
    let l : ℝ →ᵃ[ℝ] E m := AffineMap.lineMap (gvec F x₀) (gvec F y)
    have hl : Tendsto (fun t => l t) (𝓝 0) (𝓝 (gvec F x₀)) := by
      simpa only [l,AffineMap.lineMap_apply_zero] using
        (AffineMap.lineMap_continuous (p := gvec F x₀) (q := gvec F y)).tendsto (0 : ℝ)
    have hnt : ∀ᶠ t in 𝓝 (0 : ℝ), F₀ (l t) ≠ ⊤ := hl.eventually hnear
    have he : ∀ᶠ t in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < t ∧ t < 1 ∧ F₀ (l t) ≠ ⊤ := by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),nhdsWithin_le_nhds hnt] with t ht ht1 hFt
      exact ⟨ht,ht1,hFt⟩
    obtain ⟨t,ht,ht1,hFt⟩ := he.exists
    have hdom : compositeFn F F₀ ((1-t) • x₀+t • y) ≠ ⊤ := by
      apply composite_segment_finite F F₀ hF hmono x₀ y hx hy (1-t) t
        (by linarith) ht.le (by ring)
      simpa only [l,AffineMap.lineMap_apply_module] using hFt
    have hi := hn.2 _ hdom
    have hv : ((1-t) • x₀+t • y)-x₀=t • (y-x₀) := by module
    rw [hv,inner_smul_right] at hi
    nlinarith
  · intro hn
    have hxG : compositeFn F F₀ x₀ ≠ ⊤ := by
      rw [compositeFn,if_pos hx]; exact hnear.self_of_nhds
    refine ⟨hxG,?_⟩
    intro y hy
    change compositeFn F F₀ y ≠ ⊤ at hy
    have hyF : ∀ i, F i y ≠ ⊤ := by
      by_contra hnf
      simp only [compositeFn,if_neg hnf,ne_eq,not_true_eq_false] at hy
    exact hn.2 y hyF
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem composite_subgradient_iff_weighted_bound (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hF₀ : IsProperFn F₀ ∧ IsConvexFn F₀)
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v)
    (x₀ : E n) (hx : ∀ i, F i x₀ ≠ ⊤)
    (hnear : ∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤)
    (hd : DifferentiableAt ℝ (fun z : E m => (F₀ z).toReal) (gvec F x₀))
    (v : E n) : IsSubgradient (compositeFn F F₀) x₀ v ↔
      ∀ y : E n, (∀ i, F i y ≠ ⊤) → inner ℝ v (y-x₀) ≤
        inner ℝ (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) (gvec F y-gvec F x₀) := by
  constructor
  · exact composite_subgradient_weighted_bound F F₀ hF hF₀.1 hmono x₀ hx hnear hd v
  · intro hb
    classical
    have hp := original_composite_proper_at F F₀ hF₀.1 x₀ hx hnear
    have hft : F₀ (gvec F x₀) ≠ ⊤ := hnear.self_of_nhds
    have hs := convex_differentiable_subgradient F₀ hF₀.1 hF₀.2 _ hft hd
    have he₀ : compositeFn F F₀ x₀=F₀ (gvec F x₀) := by simp only [compositeFn,if_pos hx]
    have hxG : compositeFn F F₀ x₀ ≠ ⊤ := by rw [he₀]; exact hft
    refine ⟨hxG,?_⟩
    intro y
    by_cases hy : compositeFn F F₀ y=⊤
    · rw [hy]; exact le_top
    have ex := EReal.coe_toReal hxG (hp.1 x₀)
    have ey := EReal.coe_toReal hy (hp.1 y)
    have hyF := (composite_epi_finite F F₀ y (compositeFn F F₀ y).toReal (by rw [ey])).1
    have hey : compositeFn F F₀ y=F₀ (gvec F y) := by simp only [compositeFn,if_pos hyF]
    have hi := hs.2 (gvec F y)
    rw [← he₀,← hey,← ex,← ey,← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    have hb' := hb y hyF
    rw [← ex,← ey,← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    linarith
end BregmanIneqMultCodex

end

set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanIneqMultCodex

/-- Lemma A4, p. 224: the subdifferential chain rule. `G` is convex unconditionally;
properness needs a point of `dom G`, supplied by any `x₀` at which every inner value is
finite and `F₀` is finite near (hence differentiable at) the vector of inner values. -/
theorem solution {n m : ℕ} (F : Fin m → E n → EReal) (F₀ : E m → EReal)
    (hF : ∀ i, IsProperFn (F i) ∧ IsConvexFn (F i))
    (hri : ∃ x : E n, ∀ i,
      x ∈ intrinsicInterior ℝ {y : E n | F i y ≠ ⊤})
    (hF₀ : IsProperFn F₀ ∧ IsConvexFn F₀)
    (hmono : ∀ u v : E m, (∀ i, u i ≤ v i) → F₀ u ≤ F₀ v) :
    IsConvexFn (compositeFn F F₀) ∧
    ∀ x₀ : E n, (∀ i, F i x₀ ≠ ⊤) →
      (∀ᶠ z in 𝓝 (gvec F x₀), F₀ z ≠ ⊤) →
      DifferentiableAt ℝ (fun z : E m => (F₀ z).toReal) (gvec F x₀) →
      IsProperFn (compositeFn F F₀) ∧
      BregmanPPA.Convergence.subdiffOp (compositeFn F F₀) x₀ =
        {v | ∃ ν : E n,
          ν ∈ normalCone {x | compositeFn F F₀ x ≠ ⊤} x₀ ∧
          ∃ ξ : Fin m → E n,
            (∀ i, (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) i ≠ 0 →
              IsSubgradient (F i) x₀ (ξ i)) ∧
            v = ν + ∑ i, (gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)) i • ξ i} := by
  refine ⟨original_composite_convex F F₀ hF hF₀.2 hmono,?_⟩
  intro x₀ hx hnear hd
  refine ⟨original_composite_proper_at F F₀ hF₀.1 x₀ hx hnear,?_⟩
  ext v
  constructor
  · intro hs
    let w := gradient (fun z : E m => (F₀ z).toReal) (gvec F x₀)
    have hw : ∀ i, 0 ≤ w i := monotone_gradient_nonnegative F₀ hF₀.1 hF₀.2 hmono _ hnear.self_of_nhds hd
    have hb : ∀ y : E n, (∀ i, F i y ≠ ⊤) → inner ℝ v (y-x₀) ≤
        ∑ i, w i*((F i y).toReal-(F i x₀).toReal) := by
      intro y hy
      have hi := composite_subgradient_weighted_bound F F₀ hF hF₀.1 hmono x₀ hx hnear hd v hs y hy
      simpa only [w,PiLp.inner_apply,Real.inner_apply,PiLp.sub_apply,gvec,WithLp.equiv_symm_apply,WithLp.ofLp_toLp] using hi
    obtain ⟨ν,hν,ξ,hξ,he⟩ := qualified_weighted_decomposition F (fun i => w i) hF hw hri x₀ v hx hb
    have hnorm := composite_domain_normal_eq F F₀ hF hmono x₀ hx hnear
    rw [← hnorm] at hν
    exact ⟨ν,hν,ξ,hξ,he⟩
  · rintro ⟨ν,hν,ξ,hξ,rfl⟩
    exact composite_chain_rhs_subgradient F F₀ hF hF₀ hmono x₀ hx hnear hd ν hν ξ hξ




#print axioms solution
