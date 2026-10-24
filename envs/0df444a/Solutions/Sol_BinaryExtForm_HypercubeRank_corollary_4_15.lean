-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.corollary_4_15
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:06:46.93245+00:00
-- url     : https://prove2.me/submissions/23e24ec7-93e1-4b0c-aa11-6bb570eded74

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma binarization_convex {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) : Convex ℝ B := by
  obtain ⟨S,hS⟩ := hB.1
  rw [hS]
  exact convex_convexHull ℝ _

lemma binary_label {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d + 1) → ℝ}
    (hp : p ∈ B) (hb : IsBinaryY p) : ∃ m : ℕ, m ≤ k ∧ p 0 = m := by
  have hh : p 0 ∈ (fun p => p 0) '' {p | p ∈ B ∧ IsBinaryY p} := ⟨p,⟨hp,hb⟩,rfl⟩
  rw [hB.2.2.2] at hh
  exact hh

lemma binary_fiber_no_lt {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : ¬ u 0 < v 0 := by
  intro hlt
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  obtain ⟨a,ha,hua⟩ := binary_label hB hu hb
  obtain ⟨b,hbnd,hvb⟩ := binary_label hB hv hb'
  have hab : a < b := by exact_mod_cast (show (a:ℝ)<b by simpa [hua,hvb] using hlt)
  have hdiff : 1 ≤ v 0-u 0 := by
    have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
    rw [hua,hvb]
    linarith
  let t : ℝ := 1 / (2*(v 0-u 0))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by linarith : 0 < 2*(v 0-u 0))).mpr; linarith
  let p : Fin (d+1) → ℝ := (1-t) • u + t • v
  have hp : p ∈ B := binarization_convex hB hu hv (sub_nonneg.mpr ht1) ht.le (by ring)
  have hpy (i : Fin d) : p i.succ = u i.succ := by
    have hh : u i.succ = v i.succ := congrFun hy i
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [← hh]
    ring
  have hpb : IsBinaryY p := by
    intro i
    rw [hpy]
    exact hb i
  obtain ⟨m,hm,hpm⟩ := binary_label hB hp hpb
  have hp0 : p 0 = u 0+1/2 := by
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul,t]
    field_simp
    ring
  have ham : a < m := by
    have hh : (a : ℝ) < m := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  have hma : m < a+1 := by
    have hh : (m : ℝ) < (a : ℝ) + 1 := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  omega

lemma binary_fiber_unique {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : u = v := by
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  have hx : u 0 = v 0 := le_antisymm
    (le_of_not_gt (binary_fiber_no_lt hB hv hu hb' hy.symm))
    (le_of_not_gt (binary_fiber_no_lt hB hu hv hb hy))
  ext i
  refine Fin.cases hx (fun j => congrFun hy j) i

end BinaryExtForm.HypercubeRank.FiberProof

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma binary_point_extreme {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d+1) → ℝ}
    (hp : p ∈ B) (hpbin : IsBinaryY p) : p ∈ Set.extremePoints ℝ B := by
  refine ⟨hp,?_⟩
  intro u hu v hv hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have hy : yproj u = yproj p := by
    ext i
    have hcoord : a*u i.succ+b*v i.succ=p i.succ := congrFun heq i.succ
    obtain ⟨hu0,hu1⟩ := hB.2.2.1 u hu i
    obtain ⟨hv0,hv1⟩ := hB.2.2.1 v hv i
    rcases hpbin i with h0|h1
    · change u i.succ=p i.succ
      rw [h0]
      rw [h0] at hcoord
      nlinarith [mul_nonneg hb.le hv0]
    · change u i.succ=p i.succ
      rw [h1]
      rw [h1] at hcoord
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hv1)]
  exact (binary_fiber_unique hB hp hu hpbin hy.symm).symm

end BinaryExtForm.HypercubeRank.FiberProof

namespace BinaryExtForm.HypercubeRank.PolytopeProof

lemma polytope_convex {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsPolytope B) : Convex ℝ B := by
  obtain ⟨S,rfl⟩ := hB
  exact convex_convexHull ℝ _

lemma polytope_compact {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsPolytope B) : IsCompact B := by
  obtain ⟨S,rfl⟩ := hB
  exact S.finite_toSet.isCompact_convexHull ℝ

lemma polytope_extreme_hull {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsPolytope B) :
    convexHull ℝ (Set.extremePoints ℝ B) = B := by
  obtain ⟨S,hS⟩ := hB
  have hfin : (Set.extremePoints ℝ B).Finite := by
    rw [hS]
    exact S.finite_toSet.subset extremePoints_convexHull_subset
  have hcl : IsClosed (convexHull ℝ (Set.extremePoints ℝ B)) := hfin.isClosed_convexHull ℝ
  have hh := closure_convexHull_extremePoints (polytope_compact ⟨S,hS⟩) (polytope_convex ⟨S,hS⟩)
  simpa only [hcl.closure_eq] using hh

end BinaryExtForm.HypercubeRank.PolytopeProof

namespace BinaryExtForm.HypercubeRank.ProjectionProof

open FiberProof PolytopeProof

private def projectLinear (d : ℕ) : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun := yproj
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma projection_continuous (d : ℕ) : Continuous (@yproj d) :=
  continuous_pi fun i => continuous_apply i.succ

private lemma projection_openSegment {d : ℕ} (u v : Fin (d + 1) → ℝ) :
    yproj '' openSegment ℝ u v = openSegment ℝ (yproj u) (yproj v) := by
  exact image_openSegment ℝ (projectLinear d).toAffineMap u v

private lemma projection_segment {d : ℕ} (u v : Fin (d + 1) → ℝ) :
    yproj '' segment ℝ u v = segment ℝ (yproj u) (yproj v) := by
  exact image_segment ℝ (projectLinear d).toAffineMap u v

private lemma integral_vertex_binary {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hI : IsIntegral B) {p : Fin (d + 1) → ℝ} (hp : p ∈ Set.extremePoints ℝ B) :
    IsBinaryY p := by
  rw [hI] at hp
  exact (extremePoints_convexHull_subset hp).2.2

private lemma binary_projection_extreme {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d + 1) → ℝ}
    (hp : p ∈ B) (hbin : IsBinaryY p) :
    yproj p ∈ Set.extremePoints ℝ (yproj '' B) := by
  refine ⟨⟨p, hp, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ ⟨a, b, ha, hb, hab, heq⟩
  ext i
  have hi : a * u i.succ + b * v i.succ = p i.succ := congrFun heq i
  obtain ⟨hu0, hu1⟩ := hB.2.2.1 u hu i
  obtain ⟨hv0, hv1⟩ := hB.2.2.1 v hv i
  change u i.succ = p i.succ
  rcases hbin i with h0 | h1
  · rw [h0] at hi ⊢
    nlinarith [mul_nonneg hb.le hv0]
  · rw [h1] at hi ⊢
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hv1)]

private lemma integral_projection_bij {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) (hI : IsIntegral B) :
    Set.BijOn yproj (Set.extremePoints ℝ B) (Set.extremePoints ℝ (yproj '' B)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact binary_projection_extreme hB hp.1 (integral_vertex_binary hI hp)
  · intro u hu v hv heq
    exact binary_fiber_unique hB hu.1 hv.1 (integral_vertex_binary hI hu) heq
  · let f : (Fin (d + 1) → ℝ) →ᴬ[ℝ] (Fin d → ℝ) :=
      { (projectLinear d).toAffineMap with cont := projection_continuous d }
    exact surjOn_extremePoints_image f (polytope_compact hB.1)

private lemma integral_adj_lift {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) (hI : IsIntegral B)
    {u v : Fin (d + 1) → ℝ} (hu : u ∈ Set.extremePoints ℝ B)
    (hv : v ∈ Set.extremePoints ℝ B)
    (hadj : Hirsch.Adj (yproj '' B) (yproj u) (yproj v)) : Hirsch.Adj B u v := by
  let F : Set (Fin (d + 1) → ℝ) := B ∩ yproj ⁻¹' segment ℝ (yproj u) (yproj v)
  have hFext : IsExtreme ℝ B F := by
    refine ⟨fun _ hp => hp.1, ?_⟩
    intro p hp q hq z hz hseg
    refine ⟨hp, ?_⟩
    apply hadj.2.left_mem_of_mem_openSegment ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ hz.2
    rw [← projection_openSegment]
    exact ⟨z, hseg, rfl⟩
  have hFc : IsCompact F := by
    have hclosed : IsClosed (segment ℝ (yproj u) (yproj v)) := by
      rw [← convexHull_pair]
      exact (Set.toFinite {yproj u, yproj v}).isClosed_convexHull ℝ
    exact (polytope_compact hB.1).inter_right (hclosed.preimage (projection_continuous d))
  have hFconv : Convex ℝ F := by
    intro p hp q hq a b ha hb hab
    refine ⟨polytope_convex hB.1 hp.1 hq.1 ha hb hab, ?_⟩
    exact convex_segment (yproj u) (yproj v) hp.2 hq.2 ha hb hab
  have hext : Set.extremePoints ℝ F ⊆ segment ℝ u v := by
    intro p hp
    have hpB := hFext.extremePoints_subset_extremePoints hp
    have hpy := binary_projection_extreme hB hpB.1 (integral_vertex_binary hI hpB)
    have hends := (mem_extremePoints_iff_forall_segment.mp hpy).2
      (yproj u) ⟨u, hu.1, rfl⟩ (yproj v) ⟨v, hv.1, rfl⟩ hp.1.2
    rcases hends with hpu | hpv
    · have heq := binary_fiber_unique hB hu.1 hpB.1 (integral_vertex_binary hI hu) hpu
      simpa only [← heq] using left_mem_segment ℝ u v
    · have heq := binary_fiber_unique hB hv.1 hpB.1 (integral_vertex_binary hI hv) hpv
      simpa only [← heq] using right_mem_segment ℝ u v
  have hFseg : F ⊆ segment ℝ u v := by
    have hclosed : IsClosed (segment ℝ u v) := by
      rw [← convexHull_pair]
      exact (Set.toFinite {u, v}).isClosed_convexHull ℝ
    have hh := closure_minimal (convexHull_min hext (convex_segment u v)) hclosed
    rwa [closure_convexHull_extremePoints hFc hFconv] at hh
  have hsegF : segment ℝ u v ⊆ F := hFconv.segment_subset
    ⟨hu.1, left_mem_segment ℝ _ _⟩ ⟨hv.1, right_mem_segment ℝ _ _⟩
  have hFeq : F = segment ℝ u v := Set.Subset.antisymm hFseg hsegF
  refine ⟨fun heq => hadj.1 (congrArg yproj heq), ?_⟩
  rwa [← hFeq]

private lemma linear_extreme_image_iff {m n : ℕ}
    (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) {B C : Set (Fin m → ℝ)}
    (hconv : Convex ℝ B) (hinj : Set.InjOn f B) (hCB : C ⊆ B) :
    IsExtreme ℝ (f '' B) (f '' C) ↔ IsExtreme ℝ B C := by
  have hmap (u v : Fin m → ℝ) :
      f '' openSegment ℝ u v = openSegment ℝ (f u) (f v) :=
    image_openSegment ℝ f.toAffineMap u v
  constructor
  · intro h
    refine ⟨hCB, ?_⟩
    intro p hp q hq z hz hseg
    have hh : f p ∈ f '' C := h.2 ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ ⟨z, hz, rfl⟩ (by
      rw [← hmap]; exact ⟨z, hseg, rfl⟩)
    obtain ⟨w, hw, heq⟩ := hh
    exact (hinj (hCB hw) hp heq) ▸ hw
  · intro h
    refine ⟨Set.image_mono hCB, ?_⟩
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
    rw [← hmap] at hseg
    obtain ⟨w, hw, heq⟩ := hseg
    have hwz : w = z := hinj (hconv.openSegment_subset hp hq hw) (hCB hz) heq
    subst w
    exact ⟨p, h.2 hp hq hz hw, rfl⟩

private lemma affine_projection_inj {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hA : IsAffineBin B) : Set.InjOn yproj B := by
  obtain ⟨a, β, hA⟩ := hA
  intro p hp q hq heq
  have hzero : p 0 = q 0 := by
    rw [hA p hp, hA q hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show p i.succ = q i.succ from congrFun heq i]
  ext i
  exact Fin.cases hzero (fun j => congrFun heq j) i

private lemma affine_projection_bij {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) (hA : IsAffineBin B) :
    Set.BijOn yproj (Set.extremePoints ℝ B) (Set.extremePoints ℝ (yproj '' B)) := by
  have hinj := affine_projection_inj hA
  have hext (p : Fin (d + 1) → ℝ) (hp : p ∈ B) :
      yproj p ∈ Set.extremePoints ℝ (yproj '' B) ↔ p ∈ Set.extremePoints ℝ B := by
    have hh := linear_extreme_image_iff (projectLinear d) (polytope_convex hB.1) hinj
      (Set.singleton_subset_iff.mpr hp)
    change IsExtreme ℝ (yproj '' B) (yproj '' {p}) ↔ IsExtreme ℝ B {p} at hh
    simpa only [Set.image_singleton, isExtreme_singleton] using hh
  refine ⟨fun p hp => (hext p hp.1).mpr hp,
    fun p hp q hq heq => hinj hp.1 hq.1 heq, ?_⟩
  intro y hy
  obtain ⟨p, hp, rfl⟩ := hy.1
  exact ⟨p, (hext p hp).mp hy, rfl⟩

private lemma affine_adj_iff {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) (hA : IsAffineBin B)
    {u v : Fin (d + 1) → ℝ} (hu : u ∈ B) (hv : v ∈ B) :
    Hirsch.Adj (yproj '' B) (yproj u) (yproj v) ↔ Hirsch.Adj B u v := by
  have hinj := affine_projection_inj hA
  have hext := linear_extreme_image_iff (projectLinear d) (polytope_convex hB.1) hinj
    ((polytope_convex hB.1).segment_subset hu hv)
  change IsExtreme ℝ (yproj '' B) (yproj '' segment ℝ u v) ↔
    IsExtreme ℝ B (segment ℝ u v) at hext
  rw [projection_segment] at hext
  exact and_congr (not_congr ⟨fun h => hinj hu hv h, congrArg yproj⟩) hext

end BinaryExtForm.HypercubeRank.ProjectionProof

open BinaryExtForm.HypercubeRank BinaryExtForm.HypercubeRank.ProjectionProof

theorem solution {d k : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B) :
    (IsIntegral B →
      Set.BijOn yproj (Set.extremePoints ℝ B) (Set.extremePoints ℝ (yproj '' B)) ∧
      ∀ u ∈ Set.extremePoints ℝ B, ∀ v ∈ Set.extremePoints ℝ B,
        Hirsch.Adj (yproj '' B) (yproj u) (yproj v) → Hirsch.Adj B u v) ∧
    (IsAffineBin B →
      Set.BijOn yproj (Set.extremePoints ℝ B) (Set.extremePoints ℝ (yproj '' B)) ∧
      ∀ u ∈ Set.extremePoints ℝ B, ∀ v ∈ Set.extremePoints ℝ B,
        (Hirsch.Adj (yproj '' B) (yproj u) (yproj v) ↔ Hirsch.Adj B u v)) := by
  constructor
  · intro hI
    exact ⟨integral_projection_bij hB hI, fun _ hu _ hv => integral_adj_lift hB hI hu hv⟩
  · intro hA
    exact ⟨affine_projection_bij hB hA, fun _ hu _ hv => affine_adj_iff hB hA hu.1 hv.1⟩
