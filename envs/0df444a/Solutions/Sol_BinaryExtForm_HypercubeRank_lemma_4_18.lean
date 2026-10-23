-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.lemma_4_18
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:42:00.222989+00:00
-- url     : https://prove2.me/submissions/823dc21f-f8d2-4944-bd96-992468ca2062

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Theorems.Thm_BinaryExtForm_HypercubeRank_observation_4_8

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


namespace BinaryExtForm.HypercubeRank.HitRankProof

open FiberProof PolytopeProof

lemma vertex_binary {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) {u : Fin (d + 1) → ℝ}
    (hu : u ∈ Set.extremePoints ℝ B) : IsBinaryY u := by
  have hy : yproj u ∈ yproj '' Set.extremePoints ℝ B := ⟨u, hu, rfl⟩
  rw [hB.2.1] at hy
  exact hy

lemma vertex_label {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) {u : Fin (d + 1) → ℝ}
    (hu : u ∈ Set.extremePoints ℝ B) : ∃ m : ℕ, m + 1 ≤ 2 ^ d ∧ u 0 = m := by
  have hx : u 0 ∈ (fun p => p 0) '' Set.extremePoints ℝ B := ⟨u, hu, rfl⟩
  rw [hB.2.2] at hx
  exact hx

lemma hypercube_natural {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) : IsNatural B := by
  intro p hp
  obtain ⟨m, _, hm⟩ := vertex_label hB hp
  exact ⟨(m : ℤ), by simpa using hm⟩

lemma hypercube_x_bounds {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) : ∀ p ∈ B, 0 ≤ p 0 ∧ p 0 ≤ (2 ^ d - 1 : ℕ) := by
  have hsub : Set.extremePoints ℝ B ⊆
      {p : Fin (d + 1) → ℝ | 0 ≤ p 0 ∧ p 0 ≤ (2 ^ d - 1 : ℕ)} := by
    intro p hp
    obtain ⟨m, hm, heq⟩ := vertex_label hB hp
    change 0 ≤ p 0 ∧ p 0 ≤ (2 ^ d - 1 : ℕ)
    rw [heq]
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast (show m ≤ 2 ^ d - 1 by omega)⟩
  have hconv : Convex ℝ {p : Fin (d + 1) → ℝ | 0 ≤ p 0 ∧ p 0 ≤ (2 ^ d - 1 : ℕ)} := by
    intro p hp q hq a b ha hb hab
    constructor
    · exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
    · change a * p 0 + b * q 0 ≤ _
      calc
        _ ≤ a * (2 ^ d - 1 : ℕ) + b * (2 ^ d - 1 : ℕ) :=
          add_le_add (mul_le_mul_of_nonneg_left hp.2 ha) (mul_le_mul_of_nonneg_left hq.2 hb)
        _ = _ := by rw [← add_mul, hab, one_mul]
  have hh := convexHull_min hsub hconv
  rwa [polytope_extreme_hull hB.1.1] at hh

lemma boundary_mix_left (a b x y c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hc : c = 0 ∨ c = 1)
    (he : a * x + b * y = c) : x = c := by
  rcases hc with rfl | rfl
  · have hby := mul_nonneg hb.le hy.1
    nlinarith
  · have hby := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    nlinarith

lemma cube_edge_adj {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ Set.extremePoints ℝ B) (hv : v ∈ Set.extremePoints ℝ B)
    (i : Fin d) (hdelta : DiffersOnlyAt u v i) : Hirsch.Adj B u v := by
  classical
  let F : Set (Fin (d + 1) → ℝ) := {p | p ∈ B ∧ ∀ k : Fin d, k ≠ i → p k.succ = u k.succ}
  have hFext : IsExtreme ℝ B F := by
    refine ⟨fun _ hp => hp.1, ?_⟩
    rintro p hp q hq z hz ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hp, ?_⟩
    intro k hki
    have he := hz.2 k hki
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
    exact boundary_mix_left a b (p k.succ) (q k.succ) (u k.succ) ha hb hab
      (hB.1.2.2.1 p hp k) (hB.1.2.2.1 q hq k) (vertex_binary hB hu k) he
  have hFc : IsCompact F := by
    have hc : IsClosed {p : Fin (d + 1) → ℝ | ∀ k : Fin d, k ≠ i → p k.succ = u k.succ} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply k.succ) continuous_const
    exact (polytope_compact hB.1.1).inter_right hc
  have hFconv : Convex ℝ F := by
    intro p hp q hq a b ha hb hab
    refine ⟨polytope_convex hB.1.1 hp.1 hq.1 ha hb hab, ?_⟩
    intro k hki
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp.2 k hki, hq.2 k hki]
    rw [← add_mul, hab, one_mul]
  have hext : Set.extremePoints ℝ F ⊆ segment ℝ u v := by
    intro p hp
    have hpB := hFext.extremePoints_subset_extremePoints hp
    have hpi : p i.succ = u i.succ ∨ p i.succ = v i.succ := by
      have hu' := vertex_binary hB hu i
      have hv' := vertex_binary hB hv i
      have hp' := vertex_binary hB hpB i
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
        rcases hp' with hp' | hp' <;> simp_all [DiffersOnlyAt]
    rcases hpi with hpi | hpi
    · have heq : p = u := binary_fiber_unique hB.1 hpB.1 hu.1 (vertex_binary hB hpB) (by
        ext k
        by_cases hki : k = i
        · subst k; exact hpi
        · exact hp.1.2 k hki)
      simpa only [heq] using left_mem_segment ℝ u v
    · have heq : p = v := binary_fiber_unique hB.1 hpB.1 hv.1 (vertex_binary hB hpB) (by
        ext k
        by_cases hki : k = i
        · subst k; exact hpi
        · exact (hp.1.2 k hki).trans (hdelta.2 k hki))
      simpa only [heq] using right_mem_segment ℝ u v
  have hFseg : F ⊆ segment ℝ u v := by
    have hclosed : IsClosed (segment ℝ u v) := by
      rw [← convexHull_pair]
      exact (Set.toFinite {u, v}).isClosed_convexHull ℝ
    have hh := closure_minimal (convexHull_min hext (convex_segment u v)) hclosed
    rwa [closure_convexHull_extremePoints hFc hFconv] at hh
  have hsegF : segment ℝ u v ⊆ F := hFconv.segment_subset
    ⟨hu.1, fun _ _ => rfl⟩ ⟨hv.1, fun k hk => (hdelta.2 k hk).symm⟩
  have hFeq : F = segment ℝ u v := Set.Subset.antisymm hFseg hsegF
  refine ⟨fun heq => hdelta.1 (congrFun heq i.succ), ?_⟩
  rwa [← hFeq]

end BinaryExtForm.HypercubeRank.HitRankProof

namespace BinaryExtForm.HypercubeRank.HitRankProof

lemma bool_cut_crossing {ι : Type*} [DecidableEq ι] (P : (ι → Bool) → Prop) (s : Finset ι) :
    ∀ y z : ι → Bool, (∀ k, k ∉ s → y k = z k) → P y → ¬ P z →
      ∃ i ∈ s, ∃ a b : ι → Bool,
        P a ∧ ¬ P b ∧ a i ≠ b i ∧ ∀ k, k ≠ i → a k = b k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y z heq hy hz
    have hyz : y = z := funext fun k => heq k (Finset.notMem_empty k)
    exact (hz (hyz ▸ hy)).elim
  | @insert i s his ih =>
    intro y z heq hy hz
    let w : ι → Bool := Function.update y i (z i)
    have hwz : ∀ k, k ∉ s → w k = z k := by
      intro k hk
      by_cases hki : k = i
      · subst k; simp [w]
      · simpa [w, hki] using heq k (by simp [hk, hki])
    by_cases hw : P w
    · obtain ⟨j, hj, a, b, hab⟩ := ih w z hwz hw hz
      exact ⟨j, Finset.mem_insert_of_mem hj, a, b, hab⟩
    · refine ⟨i, Finset.mem_insert_self _ _, y, w, hy, hw, ?_, ?_⟩
      · intro he
        have hyi : y i = z i := by simpa [w] using he
        have hwy : w = y := by simp [w, ← hyi]
        exact hw (hwy ▸ hy)
      · intro k hki
        simp [w, hki]

lemma threshold_crossing_coordinate {d : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) (α : ℕ) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ Set.extremePoints ℝ B) (hv : v ∈ Set.extremePoints ℝ B)
    (huα : u 0 ≤ α) (hvα : (α : ℝ) + 1 ≤ v 0) :
    ∃ i : Fin d, u i.succ ≠ v i.succ ∧
      ∃ a ∈ Set.extremePoints ℝ B, ∃ b ∈ Set.extremePoints ℝ B,
        DiffersOnlyAt a b i ∧ a 0 ≤ α ∧ (α : ℝ) + 1 ≤ b 0 := by
  classical
  have hp_exists (y : Fin d → Bool) : ∃ p ∈ Set.extremePoints ℝ B,
      ∀ i, p i.succ = if y i then 1 else 0 := by
    have hy : (fun i => if y i then (1 : ℝ) else 0) ∈
        {y : Fin d → ℝ | ∀ i, y i = 0 ∨ y i = 1} := by
      intro i
      cases y i <;> simp
    rw [← hB.2.1] at hy
    obtain ⟨p, hp, heq⟩ := hy
    exact ⟨p, hp, fun i => congrFun heq i⟩
  choose p hp hpy using hp_exists
  let yu : Fin d → Bool := fun i => decide (u i.succ = 1)
  let yv : Fin d → Bool := fun i => decide (v i.succ = 1)
  have hpu : p yu = u := FiberProof.binary_fiber_unique hB.1 (hp yu).1 hu.1
    (vertex_binary hB (hp yu)) (by
      ext i
      change p yu i.succ = u i.succ
      rw [hpy]
      rcases vertex_binary hB hu i with h | h <;> simp [yu, h])
  have hpv : p yv = v := FiberProof.binary_fiber_unique hB.1 (hp yv).1 hv.1
    (vertex_binary hB (hp yv)) (by
      ext i
      change p yv i.succ = v i.succ
      rw [hpy]
      rcases vertex_binary hB hv i with h | h <;> simp [yv, h])
  let s : Finset (Fin d) := Finset.univ.filter fun i => yu i ≠ yv i
  obtain ⟨i, hi, a, b, ha, hb, habi, hab⟩ :=
    bool_cut_crossing (fun y => p y 0 ≤ (α : ℝ)) s yu yv
      (fun k hk => by simpa [s] using hk) (by simpa [hpu] using huα)
      (by rw [hpv]; linarith)
  refine ⟨i, ?_, p a, hp a, p b, hp b, ⟨?_, ?_⟩, ha, ?_⟩
  · have hh : yu i ≠ yv i := (Finset.mem_filter.mp hi).2
    intro heq
    apply hh
    simp only [yu, yv, heq]
  · rw [hpy, hpy]
    cases hai : a i <;> cases hbi : b i <;> simp_all
  · intro k hki
    rw [hpy, hpy, hab k hki]
  · obtain ⟨m, _, hm⟩ := vertex_label hB (hp b)
    have hαm : α < m := by
      exact_mod_cast (show (α : ℝ) < (m : ℝ) by rw [← hm]; exact lt_of_not_ge hb)
    rw [hm]
    exact_mod_cast (show α + 1 ≤ m by omega)

end BinaryExtForm.HypercubeRank.HitRankProof

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

namespace BinaryExtForm.HypercubeRank.HitRankProof

lemma indicator_iff_ne {d : ℕ} {u v : Fin (d + 1) → ℝ}
    (hu : IsBinaryY u) (hv : IsBinaryY v) (i : Fin d) :
    indicator u v i ↔ u i.succ ≠ v i.succ := by
  rcases hu i with hu | hu <;> rcases hv i with hv | hv <;> simp [indicator, hu, hv]

lemma hit_mem_of_cover {d ℓ : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) (α : Fin ℓ → ℕ) (Z : Finset (Fin d))
    (hZ : ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) → ∃ i ∈ Z, indicator u v i)
    (i : Fin d) (hi : typeHit B α i) : i ∈ Z := by
  obtain ⟨j, u, hu, v, hv, hdelta, huα, hvα⟩ := hi
  have hedge : IsAlphaEdge B (α j) u v :=
    ⟨cube_edge_adj hB hu hv i hdelta, Or.inl ⟨huα, hvα⟩⟩
  obtain ⟨k, hkZ, hk⟩ := hZ u v ⟨j, hedge⟩
  have hki : k = i := by
    by_contra hki
    exact ((indicator_iff_ne (vertex_binary hB hu) (vertex_binary hB hv) k).mp hk)
      (hdelta.2 k hki)
  simpa only [hki] using hkZ

lemma hit_coordinates_cover {d ℓ : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) (α : Fin ℓ → ℕ) :
    ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) →
      ∃ i : Fin d, typeHit B α i ∧ indicator u v i := by
  intro u v hedge
  obtain ⟨j, hadj, hcross⟩ := hedge
  obtain ⟨hu, hv⟩ := CoverProof.adj_endpoints hadj
  rcases hcross with ⟨huα, hvα⟩ | ⟨hvα, huα⟩
  · obtain ⟨i, hi, a, ha, b, hb, hab, haα, hbα⟩ :=
      threshold_crossing_coordinate hB (α j) hu hv huα hvα
    exact ⟨i, ⟨j, a, ha, b, hb, hab, haα, hbα⟩,
      (indicator_iff_ne (vertex_binary hB hu) (vertex_binary hB hv) i).mpr hi⟩
  · obtain ⟨i, hi, a, ha, b, hb, hab, haα, hbα⟩ :=
      threshold_crossing_coordinate hB (α j) hv hu hvα huα
    exact ⟨i, ⟨j, a, ha, b, hb, hab, haα, hbα⟩,
      (indicator_iff_ne (vertex_binary hB hu) (vertex_binary hB hv) i).mpr hi.symm⟩

lemma cover_minimum_eq_hits {d ℓ : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsHypercubeBinarization d B) (α : Fin ℓ → ℕ) :
    sInf {c : ℕ | ∃ Z : Finset (Fin d), Z.card = c ∧
      ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) → ∃ i ∈ Z, indicator u v i} =
      Set.ncard {i : Fin d | typeHit B α i} := by
  classical
  let H : Finset (Fin d) := Finset.univ.filter (typeHit B α)
  have hHcover : ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) →
      ∃ i ∈ H, indicator u v i := by
    intro u v huv
    obtain ⟨i, hi, hind⟩ := hit_coordinates_cover hB α u v huv
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hind⟩
  have hleast : IsLeast {c : ℕ | ∃ Z : Finset (Fin d), Z.card = c ∧
      ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) → ∃ i ∈ Z, indicator u v i} H.card := by
    refine ⟨⟨H, rfl, hHcover⟩, ?_⟩
    rintro c ⟨Z, hZcard, hZcover⟩
    rw [← hZcard]
    apply Finset.card_le_card
    intro i hi
    exact hit_mem_of_cover hB α Z hZcover i (Finset.mem_filter.mp hi).2
  have hcard : H.card = Set.ncard {i : Fin d | typeHit B α i} := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [H]
  exact hleast.csInf_eq.trans hcard

end BinaryExtForm.HypercubeRank.HitRankProof

open BinaryExtForm.HypercubeRank

/-- The original hypercube hit-count formula, reduced to the existing set-cover rank theorem. -/
theorem solution {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar : Fin ℓ → ℝ) (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1) :
    rk B xbar = Set.ncard {i : Fin d | typeHit B α i} := by
  rw [observation_4_8 B hB.1 (HitRankProof.hypercube_natural hB)
    (HitRankProof.hypercube_x_bounds hB) α (fun j => by have := hα j; omega) xbar hx]
  exact HitRankProof.cover_minimum_eq_hits hB α
