-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:54:34.109919+00:00
-- url     : https://prove2.me/submissions/0d48a2b9-efae-462f-aaeb-4788ed5562e8

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model


namespace BinaryExtForm.HypercubeRank.SliceGeometry

open Set
open scoped Pointwise

noncomputable def directionCone {n : ℕ} (B : Set (Fin n → ℝ)) (p : Fin n → ℝ) (hp : p ∈ B) :
    PointedCone ℝ (Fin n → ℝ) :=
  (ConvexCone.hull ℝ ((fun q => q-p) '' B)).toPointedCone
    (ConvexCone.subset_hull ⟨p,hp,sub_self p⟩)

lemma direction_mem {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ} (hp : p ∈ B)
    {q : Fin n → ℝ} (hq : q ∈ B) : q-p ∈ directionCone B p hp :=
  ConvexCone.subset_hull ⟨q,hq,rfl⟩

lemma translated_convex {n : ℕ} {B : Set (Fin n → ℝ)} (hB : Convex ℝ B) (p : Fin n → ℝ) :
    Convex ℝ ((fun q => q-p) '' B) := by
  rintro _ ⟨q,hq,rfl⟩ _ ⟨r,hr,rfl⟩ a b ha hb hab
  refine ⟨a • q+b • r,hB hq hr ha hb hab,?_⟩
  simp only [smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul]

lemma direction_representation {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ}
    (hB : Convex ℝ B) (hp : p ∈ B) {v : Fin n → ℝ} (hv : v ∈ directionCone B p hp) :
    ∃ a : ℝ, 0 < a ∧ ∃ q ∈ B, v = a • (q-p) := by
  change v ∈ ConvexCone.hull ℝ ((fun q => q-p) '' B) at hv
  obtain ⟨a,ha,w,⟨q,hq,rfl⟩,heq⟩ := (ConvexCone.mem_hull_of_convex (translated_convex hB p)).mp hv
  exact ⟨a,ha,q,hq,heq.symm⟩

lemma twoSided_kernel {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ}
    (hB : Convex ℝ B) (hp : p ∈ B) (i : Fin n)
    (hext : p ∈ Set.extremePoints ℝ {q ∈ B | q i = p i})
    {v : Fin n → ℝ} (hv : v ∈ (directionCone B p hp).lineal) (hvi : v i = 0) : v = 0 := by
  obtain ⟨a,ha,q,hq,hvq⟩ := direction_representation hB hp hv.1
  obtain ⟨b,hb,r,hr,hvr⟩ := direction_representation hB hp hv.2
  have hqi : q i = p i := by
    have hh := congrFun hvq i
    simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,hvi] at hh
    nlinarith
  have hri : r i = p i := by
    have hh := congrFun hvr i
    simp only [Pi.neg_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,hvi] at hh
    nlinarith
  have hab : 0 < a+b := add_pos ha hb
  have hpseg : p ∈ openSegment ℝ q r := by
    refine ⟨a/(a+b),b/(a+b),div_pos ha hab,div_pos hb hab,?_,?_⟩
    · field_simp
    · ext j
      have hqj := congrFun hvq j
      have hrj := congrFun hvr j
      simp only [Pi.neg_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] at hqj hrj
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div]
      apply (div_eq_iff hab.ne').mpr
      nlinarith

  have hqp : q=p := hext.2 ⟨hq,hqi⟩ ⟨hr,hri⟩ hpseg
  simpa [hqp] using hvq

noncomputable def directionFace {n : ℕ} (B : Set (Fin n → ℝ)) (p : Fin n → ℝ) (hp : p ∈ B) :
    Set (Fin n → ℝ) := {q ∈ B | q-p ∈ (directionCone B p hp).lineal}

lemma mem_directionFace_self {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ} (hp : p ∈ B) :
    p ∈ directionFace B p hp := ⟨hp,by simp⟩

lemma directionFace_isExtreme {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ} (hp : p ∈ B) :
    IsExtreme ℝ B (directionFace B p hp) := by
  refine ⟨fun _ h => h.1,?_⟩
  rintro q hq r hr w hw ⟨a,b,ha,hb,hab,heq⟩
  refine ⟨hq,?_⟩
  apply (PointedCone.IsFaceOf.lineal (directionCone B p hp)).mem_of_smul_add_smul_mem_left
    (direction_mem hp hq) (direction_mem hp hr) ha hb
  have hh : a • (q-p)+b • (r-p) = w-p := by
    simp only [smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul,heq]
  rw [hh]
  exact hw.2

lemma directionFace_coord_injective {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ}
    (hB : Convex ℝ B) (hp : p ∈ B) (i : Fin n)
    (hext : p ∈ Set.extremePoints ℝ {q ∈ B | q i = p i})
    {q r : Fin n → ℝ} (hq : q ∈ directionFace B p hp) (hr : r ∈ directionFace B p hp)
    (hqr : q i = r i) : q=r := by
  apply sub_eq_zero.mp
  apply twoSided_kernel hB hp i hext
  · have hh := (directionCone B p hp).lineal.sub_mem hq.2 hr.2
    simpa only [sub_sub_sub_cancel_right] using hh
  · simp only [Pi.sub_apply,hqr,sub_self]

lemma directionFace_convex {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ}
    (hB : Convex ℝ B) (hp : p ∈ B) : Convex ℝ (directionFace B p hp) := by
  intro q hq r hr a b ha hb hab
  refine ⟨hB hq.1 hr.1 ha hb hab,?_⟩
  have hh := (directionCone B p hp).lineal.add_mem
    ((directionCone B p hp).lineal.smul_mem a hq.2)
    ((directionCone B p hp).lineal.smul_mem b hr.2)
  simpa only [smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul] using hh

lemma directionFace_compact {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ}
    (hB : IsCompact B) (hp : p ∈ B) : IsCompact (directionFace B p hp) := by
  exact hB.inter_right ((directionCone B p hp).lineal.closed_of_finiteDimensional.preimage
    (continuous_id.sub continuous_const))

lemma coord_min_extreme {n : ℕ} {F : Set (Fin n → ℝ)} (i : Fin n)
    (hinj : ∀ q ∈ F, ∀ r ∈ F, q i=r i → q=r)
    {u : Fin n → ℝ} (hu : u ∈ F) (hmin : ∀ q ∈ F, u i ≤ q i) :
    u ∈ Set.extremePoints ℝ F := by
  refine ⟨hu,?_⟩
  rintro q hq r hr ⟨a,b,ha,hb,hab,heq⟩
  apply hinj q hq u hu
  have hcoord := congrFun heq i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hcoord
  have hmul := congrArg (fun t : ℝ => t*u i) hab
  simp only [add_mul,one_mul] at hmul
  have hqmin := hmin q hq
  have hrmin := hmin r hr
  nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hrmin)]

lemma coord_max_extreme {n : ℕ} {F : Set (Fin n → ℝ)} (i : Fin n)
    (hinj : ∀ q ∈ F, ∀ r ∈ F, q i=r i → q=r)
    {v : Fin n → ℝ} (hv : v ∈ F) (hmax : ∀ q ∈ F, q i ≤ v i) :
    v ∈ Set.extremePoints ℝ F := by
  refine ⟨hv,?_⟩
  rintro q hq r hr ⟨a,b,ha,hb,hab,heq⟩
  apply hinj q hq v hv
  have hcoord := congrFun heq i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hcoord
  have hmul := congrArg (fun t : ℝ => t*v i) hab
  simp only [add_mul,one_mul] at hmul
  have hqmax := hmax q hq
  have hrmax := hmax r hr
  nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hrmax)]

end BinaryExtForm.HypercubeRank.SliceGeometry


namespace BinaryExtForm.HypercubeRank.SliceGeometry

lemma vertex_of_section_on_edge {n : ℕ} {B : Set (Fin n → ℝ)} {p : Fin n → ℝ}
    (hcompact : IsCompact B) (hconv : Convex ℝ B) (i : Fin n)
    (hp : p ∈ Set.extremePoints ℝ {q ∈ B | q i = p i})
    (hnot : p ∉ Set.extremePoints ℝ B) :
    ∃ u v, Hirsch.Adj B u v ∧ u i < p i ∧ p i < v i ∧ p ∈ openSegment ℝ u v := by
  let F := directionFace B p hp.1.1
  have hFcomp : IsCompact F := directionFace_compact hcompact hp.1.1
  have hFconv : Convex ℝ F := directionFace_convex hconv hp.1.1
  have hFext : IsExtreme ℝ B F := directionFace_isExtreme hp.1.1
  have hpF : p ∈ F := mem_directionFace_self hp.1.1
  have hinj : ∀ q ∈ F, ∀ r ∈ F, q i = r i → q=r := by
    intro q hq r hr heq
    exact directionFace_coord_injective hconv hp.1.1 i hp hq hr heq
  obtain ⟨u,hu,hmin⟩ := hFcomp.exists_isMinOn ⟨p,hpF⟩ (continuous_apply i).continuousOn
  obtain ⟨v,hv,hmax⟩ := hFcomp.exists_isMaxOn ⟨p,hpF⟩ (continuous_apply i).continuousOn
  have huext : u ∈ Set.extremePoints ℝ B := hFext.extremePoints_subset_extremePoints
    (coord_min_extreme i hinj hu (fun q hq => hmin hq))
  have hvext : v ∈ Set.extremePoints ℝ B := hFext.extremePoints_subset_extremePoints
    (coord_max_extreme i hinj hv (fun q hq => hmax hq))
  have hune : u i ≠ p i := by
    intro heq
    have hup := hinj u hu p hpF heq
    exact hnot (hup ▸ huext)
  have hvne : v i ≠ p i := by
    intro heq
    have hvp := hinj v hv p hpF heq
    exact hnot (hvp ▸ hvext)
  have hult : u i < p i := lt_of_le_of_ne (hmin hpF) hune
  have hplt : p i < v i := lt_of_le_of_ne (hmax hpF) hvne.symm
  have huv : u i < v i := hult.trans hplt
  have hpos : 0 < v i-u i := sub_pos.mpr huv
  have hseg : segment ℝ u v = F := by
    apply Set.Subset.antisymm (hFconv.segment_subset hu hv)
    intro q hq
    let a : ℝ := (v i-q i)/(v i-u i)
    let b : ℝ := (q i-u i)/(v i-u i)
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr (hmax hq)) hpos.le
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr (hmin hq)) hpos.le
    have hab : a+b=1 := by
      dsimp [a,b]
      rw [← add_div]
      apply (div_eq_one_iff_eq hpos.ne').mpr
      ring
    have hw : a • u+b • v ∈ F := hFconv hu hv ha hb hab
    have hcoord : (a • u+b • v) i = q i := by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,a,b]
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div]
      apply (div_eq_iff hpos.ne').mpr
      ring
    exact ⟨a,b,ha,hb,hab,hinj _ hw q hq hcoord⟩
  refine ⟨u,v,⟨?_,?_⟩,hult,hplt,?_⟩
  · intro heq
    exact huv.ne (congrFun heq i)
  · rw [hseg]
    exact hFext
  · apply mem_openSegment_of_ne_left_right
    · intro heq
      exact hune (congrFun heq i)
    · intro heq
      exact hvne (congrFun heq i)
    · rw [hseg]
      exact hpF

end BinaryExtForm.HypercubeRank.SliceGeometry


namespace BinaryExtForm.HypercubeRank.CoverProof

lemma segment_left_extreme {n : ℕ} (u v : Fin n → ℝ) :
    u ∈ Set.extremePoints ℝ (segment ℝ u v) := by
  by_cases huv : u=v
  · subst v
    simp
  have hi : ∃ i, u i ≠ v i := Function.ne_iff.mp huv
  obtain ⟨i,hi⟩ := hi
  refine ⟨left_mem_segment ℝ u v,?_⟩
  intro p hp q hq hu
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hp
  obtain ⟨c,d,hc,hd,hcd,rfl⟩ := hq
  obtain ⟨e,f,he,hf,hef,hvec⟩ := hu
  have heq := congrFun hvec i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at heq
  have hm : (e*b+f*d)*(v i-u i)=0 := by
    calc
      _ = (e*(a*u i+b*v i)+f*(c*u i+d*v i))-u i := by
        have ha' : a=1-b := by linarith
        have hc' : c=1-d := by linarith
        have he' : e=1-f := by linarith
        rw [ha',hc',he']
        ring
      _ = 0 := by rw [heq]; ring
  have hzero : e*b+f*d=0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hi.symm)
  have hbd : b=0 := by nlinarith [mul_nonneg hf.le hd]
  have ha' : a=1 := by linarith
  simp [ha',hbd]

lemma adj_endpoints {n : ℕ} {B : Set (Fin n → ℝ)} {u v : Fin n → ℝ}
    (h : Hirsch.Adj B u v) :
    u ∈ Set.extremePoints ℝ B ∧ v ∈ Set.extremePoints ℝ B := by
  refine ⟨h.2.extremePoints_subset_extremePoints (segment_left_extreme u v),?_⟩
  apply h.2.extremePoints_subset_extremePoints
  rw [segment_symm]
  exact segment_left_extreme v u

end BinaryExtForm.HypercubeRank.CoverProof


namespace BinaryExtForm.HypercubeRank.SliceElementary

/-- A nonconstant coordinate determines a point of a segment uniquely. -/
lemma segment_coord_injective {ι : Type*} (u v : ι → ℝ) (i : ι)
    (hne : u i ≠ v i) {p q : ι → ℝ}
    (hp : p ∈ segment ℝ u v) (hq : q ∈ segment ℝ u v)
    (heq : p i = q i) : p = q := by
  obtain ⟨a, b, _ha, _hb, hab, rfl⟩ := hp
  obtain ⟨c, d, _hc, _hd, hcd, rfl⟩ := hq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heq
  have ha' : a = 1 - b := by linarith
  have hc' : c = 1 - d := by linarith
  have hm : (b - d) * (v i - u i) = 0 := by
    calc
      _ = (a * u i + b * v i) - (c * u i + d * v i) := by
        rw [ha', hc']
        ring
      _ = 0 := sub_eq_zero.mpr heq
  have hbd : b = d := sub_eq_zero.mp
    ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hne.symm))
  have hac : a = c := by linarith
  rw [hac, hbd]

/-- A level strictly between the endpoint coordinates cuts the open segment once. -/
lemma existsUnique_openSegment_coord {ι : Type*} (u v : ι → ℝ) (i : ι) (f : ℝ)
    (hu : u i < f) (hv : f < v i) :
    ∃! p, p ∈ openSegment ℝ u v ∧ p i = f := by
  have hden : 0 < v i - u i := by linarith
  let t : ℝ := (f - u i) / (v i - u i)
  have ht : 0 < t := div_pos (sub_pos.mpr hu) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have htmul : t * (v i - u i) = f - u i :=
    div_mul_cancel₀ _ hden.ne'
  let p : ι → ℝ := (1 - t) • u + t • v
  have hp : p ∈ openSegment ℝ u v :=
    ⟨1 - t, t, sub_pos.mpr ht1, ht, by ring, rfl⟩
  have hpf : p i = f := by
    change (1 - t) * u i + t * v i = f
    nlinarith [htmul]
  refine ⟨p, ⟨hp, hpf⟩, ?_⟩
  intro q hq
  exact segment_coord_injective u v i (ne_of_lt (hu.trans hv))
    (openSegment_subset_segment ℝ u v hq.1)
    (openSegment_subset_segment ℝ u v hp) (hq.2.trans hpf.symm)

/-- Intersecting an edge with a nonconstant coordinate level gives an extreme point. -/
lemma edge_coord_extreme {ι : Type*} (B : Set (ι → ℝ)) (u v : ι → ℝ)
    (hAdj : Hirsch.Adj B u v) (i : ι) (hne : u i ≠ v i) (f : ℝ)
    {p : ι → ℝ} (hp : p ∈ segment ℝ u v) (hpf : p i = f) :
    p ∈ Set.extremePoints ℝ {x | x ∈ B ∧ x i = f} := by
  refine ⟨⟨hAdj.2.subset hp, hpf⟩, ?_⟩
  intro x hx y hy hpxy
  have hxseg : x ∈ segment ℝ u v :=
    hAdj.2.left_mem_of_mem_openSegment hx.1 hy.1 hp hpxy
  exact segment_coord_injective u v i hne hxseg hp (hx.2.trans hpf.symm)

/-- The exact uniqueness direction of Lemma 4.3, independent of naturality. -/
lemma crossing_edge_unique {d : ℕ} (B : Set (Fin (d + 1) → ℝ))
    (α : ℕ) (f : ℝ) (hf₁ : (α : ℝ) < f) (hf₂ : f < (α : ℝ) + 1)
    (u v : Fin (d + 1) → ℝ) (_hAdj : Hirsch.Adj B u v)
    (hu : u 0 ≤ α) (hv : (α : ℝ) + 1 ≤ v 0) :
    ∃! p, p ∈ openSegment ℝ u v ∧ p 0 = f :=
  existsUnique_openSegment_coord u v 0 f (hu.trans_lt hf₁) (hf₂.trans_le hv)

/-- Every interior intersection of a crossing edge is a vertex of the slice. -/
lemma crossing_edge_slice_extreme {d : ℕ} (B : Set (Fin (d + 1) → ℝ))
    (α : ℕ) (f : ℝ) (hf₁ : (α : ℝ) < f) (hf₂ : f < (α : ℝ) + 1)
    (u v : Fin (d + 1) → ℝ) (hAdj : Hirsch.Adj B u v)
    (hu : u 0 ≤ α) (hv : (α : ℝ) + 1 ≤ v 0)
    {p : Fin (d + 1) → ℝ} (hp : p ∈ openSegment ℝ u v) (hpf : p 0 = f) :
    p ∈ Set.extremePoints ℝ (slice B f) :=
  edge_coord_extreme B u v hAdj 0
    (ne_of_lt ((hu.trans_lt hf₁).trans (hf₂.trans_le hv))) f
    (openSegment_subset_segment ℝ u v hp) hpf

end BinaryExtForm.HypercubeRank.SliceElementary

open BinaryExtForm.HypercubeRank

/-- Vertices of a fractional slice are precisely the crossing edge intersections. -/
theorem solution {d k : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B)
    (hN : IsNatural B) (α : ℕ) (_hα : α < k) (f : ℝ)
    (hf₁ : (α : ℝ) < f) (hf₂ : f < α + 1) :
    Set.extremePoints ℝ (slice B f) =
      {p | ∃ u v, Hirsch.Adj B u v ∧ u 0 ≤ α ∧ (α : ℝ) + 1 ≤ v 0 ∧
        p ∈ openSegment ℝ u v ∧ p 0 = f} ∧
    ∀ u v, Hirsch.Adj B u v → u 0 ≤ α → (α : ℝ) + 1 ≤ v 0 →
      ∃! p, p ∈ openSegment ℝ u v ∧ p 0 = f := by
  obtain ⟨S,hS⟩ := hB.1
  have hcompact : IsCompact B := by
    rw [hS]
    exact S.finite_toSet.isCompact_convexHull ℝ
  have hconv : Convex ℝ B := by
    rw [hS]
    exact convex_convexHull ℝ _
  refine ⟨?_,?_⟩
  · ext p
    constructor
    · intro hp
      have hpf : p 0 = f := hp.1.2
      have hnot : p ∉ Set.extremePoints ℝ B := by
        intro hext
        obtain ⟨m,hm⟩ := hN p hext
        have hlow : (α : ℤ) < m := by exact_mod_cast (show (α : ℝ) < (m : ℝ) by linarith)
        have hhigh : m < (α : ℤ)+1 := by exact_mod_cast (show (m : ℝ) < (α : ℝ)+1 by linarith)
        omega
      have hp' : p ∈ Set.extremePoints ℝ {q ∈ B | q 0 = p 0} := by
        simpa only [slice, hpf] using hp
      obtain ⟨u,v,hadj,hu,hv,hseg⟩ :=
        SliceGeometry.vertex_of_section_on_edge hcompact hconv 0 hp' hnot
      obtain ⟨huext,hvext⟩ := CoverProof.adj_endpoints hadj
      obtain ⟨a,ha⟩ := hN u huext
      obtain ⟨b,hb⟩ := hN v hvext
      have haup : a < (α : ℤ)+1 := by
        exact_mod_cast (show (a : ℝ) < (α : ℝ)+1 by linarith)
      have hblow : (α : ℤ) < b := by
        exact_mod_cast (show (α : ℝ) < (b : ℝ) by linarith)
      have haup' : a ≤ (α : ℤ) := by omega
      have hblow' : (α : ℤ)+1 ≤ b := by omega
      refine ⟨u,v,hadj,?_,?_,hseg,hpf⟩
      · rw [ha]
        exact_mod_cast haup'
      · rw [hb]
        exact_mod_cast hblow'
    · rintro ⟨u,v,hadj,hu,hv,hseg,hpf⟩
      exact SliceElementary.crossing_edge_slice_extreme B α f hf₁ hf₂ u v hadj hu hv hseg hpf
  · intro u v hadj hu hv
    exact SliceElementary.crossing_edge_unique B α f hf₁ hf₂ u v hadj hu hv
