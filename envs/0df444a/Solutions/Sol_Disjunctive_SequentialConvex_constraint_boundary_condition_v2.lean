-- Prove2me | solution 1 for Disjunctive.SequentialConvex.constraint_boundary_condition_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:30:52.787913+00:00
-- url     : https://prove2.me/submissions/0a2f57dd-9ff8-4464-991b-4387b3b451ad

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic_v2

namespace DK88
open Set

section generic
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The point of the line through `a`, `v` at level `c0` of `f`. -/
noncomputable def cross (f : E →ₗ[ℝ] ℝ) (c0 : ℝ) (a v : E) : E := a + ((c0 - f a) / (f v - f a)) • (v - a)

lemma cross_convex (f : E →ₗ[ℝ] ℝ) (c0 : ℝ) (a : E) {K : Set E} (hK : Convex ℝ K) :
    Convex ℝ {v | f a < f v ∧ cross f c0 a v ∈ K} := by
  rintro v1 ⟨h1, k1⟩ v2 ⟨h2, k2⟩ s t hs ht hst
  have hfv : f (s • v1 + t • v2) - f a = s * (f v1 - f a) + t * (f v2 - f a) := by
    simp only [map_add, map_smul, smul_eq_mul]
    have : f a = (s + t) * f a := by rw [hst, one_mul]
    linarith [this]
  have hpos : 0 < s * (f v1 - f a) + t * (f v2 - f a) := by
    rcases hs.lt_or_eq with hs' | hs'
    · have := mul_pos hs' (sub_pos.2 h1)
      nlinarith [mul_nonneg ht (sub_pos.2 h2).le]
    · subst hs'; simp at hst; subst hst
      simpa using sub_pos.2 h2
  refine ⟨by linarith, ?_⟩
  set Δ := s * (f v1 - f a) + t * (f v2 - f a) with hΔ
  have hd1 : f v1 - f a ≠ 0 := (sub_pos.2 h1).ne'
  have hd2 : f v2 - f a ≠ 0 := (sub_pos.2 h2).ne'
  have := hK k1 k2 (a := s * (f v1 - f a) / Δ) (b := t * (f v2 - f a) / Δ)
    (div_nonneg (mul_nonneg hs (sub_pos.2 h1).le) hpos.le)
    (div_nonneg (mul_nonneg ht (sub_pos.2 h2).le) hpos.le)
    (by rw [← add_div, div_self hpos.ne'])
  convert this using 1
  simp only [cross]
  rw [hfv]
  have e1 : s * (f v1 - f a) / Δ * ((c0 - f a) / (f v1 - f a)) = s * ((c0 - f a) / Δ) := by
    field_simp
  have e2 : t * (f v2 - f a) / Δ * ((c0 - f a) / (f v2 - f a)) = t * ((c0 - f a) / Δ) := by
    field_simp
  have e3 : s * (f v1 - f a) / Δ + t * (f v2 - f a) / Δ = 1 := by
    rw [← add_div, div_self hpos.ne']
  have : s • v1 + t • v2 - a = s • (v1 - a) + t • (v2 - a) := by
    have h' : s • v1 + t • v2 - a = s • (v1 - a) + t • (v2 - a) + ((s + t) - 1) • a := by module
    rw [h', hst, sub_self, zero_smul, add_zero]
  rw [this]
  calc a + ((c0 - f a) / Δ) • (s • (v1 - a) + t • (v2 - a))
      = (s * (f v1 - f a) / Δ + t * (f v2 - f a) / Δ) • a +
        ((s * (f v1 - f a) / Δ * ((c0 - f a) / (f v1 - f a))) • (v1 - a) +
         (t * (f v2 - f a) / Δ * ((c0 - f a) / (f v2 - f a))) • (v2 - a)) := by
        rw [e1, e2, e3, one_smul, smul_add, smul_smul, smul_smul, mul_comm s, mul_comm t]
    _ = _ := by simp only [smul_add, smul_smul]; module

lemma cross_swap (f : E →ₗ[ℝ] ℝ) (c0 : ℝ) {u v : E} (h : f v ≠ f u) :
    cross f c0 u v = cross (-f) (-c0) v u := by
  simp only [cross, LinearMap.neg_apply]
  have hne : f v - f u ≠ 0 := sub_ne_zero.2 h
  have : (-c0 - -f v) / (-f u - -f v) = 1 - (c0 - f u) / (f v - f u) := by
    rw [show -c0 - -f v = f v - c0 by ring, show -f u - -f v = f v - f u by ring,
      eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hne]; ring
  rw [this, sub_smul, one_smul]
  have : u - v = -(v - u) := by abel
  rw [this, smul_neg]; abel

lemma mem_of_seg (f : E →ₗ[ℝ] ℝ) (c0 : ℝ) {K : Set E} (hK : Convex ℝ K) {u v w : E}
    (hw : w ∈ segment ℝ u v) (hfw : c0 ≤ f w) (hfu : f u < c0) (hc : cross f c0 u v ∈ K)
    (hv : v ∈ K) : w ∈ K := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  have hfw' : f (a • u + b • v) = f u + b * (f v - f u) := by
    simp only [map_add, map_smul, smul_eq_mul]; rw [show a = 1 - b by linarith]; ring
  rw [hfw'] at hfw
  have hvu : 0 < f v - f u := by
    by_contra hcon; push Not at hcon; nlinarith
  set κ := (c0 - f u) / (f v - f u) with hκ
  have hκb : κ ≤ b := by rw [hκ, div_le_iff₀ hvu]; linarith
  have hκ0 : 0 < κ := div_pos (by linarith) hvu
  have hb1 : b ≤ 1 := by linarith
  have hw : a • u + b • v = u + b • (v - u) := by
    rw [show a = 1 - b by linarith]; module
  rw [hw]
  rcases (hκb.trans hb1).lt_or_eq with hk1 | hk1
  · have := hK hc hv (a := (1 - b) / (1 - κ)) (b := (b - κ) / (1 - κ))
      (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))
      (by field_simp; ring)
    convert this using 1
    simp only [cross, ← hκ]
    have h1k : 1 - κ ≠ 0 := by linarith
    have : ((1 - b) / (1 - κ)) • (u + κ • (v - u)) + ((b - κ) / (1 - κ)) • v
        = ((1 - b) / (1 - κ) + (b - κ) / (1 - κ)) • u +
          ((1 - b) / (1 - κ) * κ + (b - κ) / (1 - κ)) • (v - u) := by module
    rw [this]
    have e1 : (1 - b) / (1 - κ) + (b - κ) / (1 - κ) = 1 := by field_simp; ring
    have e2 : (1 - b) / (1 - κ) * κ + (b - κ) / (1 - κ) = b := by field_simp; ring
    rw [e1, e2, one_smul]
  · have hb : b = 1 := by linarith
    subst hb; simpa using hv

lemma cross_mem_segment (f : E →ₗ[ℝ] ℝ) (c0 : ℝ) {c e : E} (hc : f c < c0) (he : c0 ≤ f e) :
    cross f c0 c e ∈ segment ℝ c e := by
  have hd : 0 < f e - f c := by linarith
  refine ⟨1 - (c0 - f c) / (f e - f c), (c0 - f c) / (f e - f c), ?_,
    div_nonneg (by linarith) hd.le, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one hd]; linarith
  · simp only [cross]; module

lemma main_L3 (f : E →ₗ[ℝ] ℝ) (c0 : ℝ) {K : Set E} (hK : Convex ℝ K) (P : Set E)
    (h1 : ∀ e ∈ P, c0 ≤ f e → e ∈ K)
    (h2 : ∀ c ∈ P, f c < c0 → ∀ e ∈ P, c0 ≤ f e → cross f c0 c e ∈ K) :
    ∀ w ∈ convexHull ℝ P, c0 ≤ f w → w ∈ K := by
  intro w hw hfw
  set Pm := {p ∈ P | f p < c0}
  set Pp := {p ∈ P | c0 ≤ f p}
  have hP : P = Pm ∪ Pp := by
    ext p; simp only [Pm, Pp, mem_union, mem_sep_iff]
    constructor
    · intro hp; rcases lt_or_ge (f p) c0 with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hlt_conv : Convex ℝ {x : E | f x < c0} := convex_halfSpace_lt f.isLinear c0
  have hge_conv : Convex ℝ {x : E | c0 ≤ f x} := convex_halfSpace_ge f.isLinear c0
  have hPpK : convexHull ℝ Pp ⊆ K := convexHull_min (fun e he => h1 e he.1 he.2) hK
  have hPm_lt : convexHull ℝ Pm ⊆ {x | f x < c0} := convexHull_min (fun e he => he.2) hlt_conv
  have hPp_ge : convexHull ℝ Pp ⊆ {x | c0 ≤ f x} := convexHull_min (fun e he => he.2) hge_conv
  rcases Pp.eq_empty_or_nonempty with hpe | hpne
  · rw [hP, hpe, union_empty] at hw
    have := hPm_lt hw; simp at this; linarith
  rcases Pm.eq_empty_or_nonempty with hme | hmne
  · rw [hP, hme, empty_union] at hw; exact hPpK hw
  rw [hP, convexHull_union hmne hpne, mem_convexJoin] at hw
  obtain ⟨u, hu, v, hv, hwuv⟩ := hw
  have hfu : f u < c0 := hPm_lt hu
  have hfv : c0 ≤ f v := hPp_ge hv
  -- Step B
  have hB : ∀ c ∈ Pm, convexHull ℝ Pp ⊆ {v | f c < f v ∧ cross f c0 c v ∈ K} := by
    intro c hc
    refine convexHull_min ?_ (cross_convex f c0 c hK)
    intro e he
    exact ⟨by linarith [hc.2, he.2], h2 c hc.1 hc.2 e he.1 he.2⟩
  -- Step C
  have hC : convexHull ℝ Pm ⊆ {u | (-f) v < (-f) u ∧ cross (-f) (-c0) v u ∈ K} := by
    refine convexHull_min ?_ (cross_convex (-f) (-c0) v hK)
    intro c hc
    have := hB c hc hv
    refine ⟨by simp only [LinearMap.neg_apply]; linarith [this.1], ?_⟩
    rw [← cross_swap f c0 this.1.ne']
    exact this.2
  have hcu := hC hu
  have hfuv : f v ≠ f u := by
    have := hcu.1; simp only [LinearMap.neg_apply] at this; exact (by linarith : f u < f v).ne'
  obtain ⟨-, hcu2⟩ := hcu
  rw [← cross_swap f c0 hfuv] at hcu2
  exact mem_of_seg f c0 hK hwuv hfw hfu hcu2 (hPpK hv)

end generic

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma intr_sub_int {s : Set E} (h : affineSpan ℝ s = ⊤) : intrinsicInterior ℝ s ⊆ interior s := by
  apply interior_maximal intrinsicInterior_subset
  have ho : IsOpen ((affineSpan ℝ s : Set E)) := by rw [h]; exact isOpen_univ
  exact ho.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior

end

lemma seg_param {E : Type*} [AddCommGroup E] [Module ℝ E] (c e : E) {t k : ℝ} (ht : 0 ≤ t)
    (htk : t ≤ k) (hk : k ≤ 1) :
    c + k • (e - c) ∈ segment ℝ (c + t • (e - c)) e := by
  rcases (htk.trans hk).lt_or_eq with h1 | h1
  · refine ⟨(1 - k) / (1 - t), (k - t) / (1 - t), div_nonneg (by linarith) (by linarith),
      div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
    have h1t : 1 - t ≠ 0 := by linarith
    have : ((1 - k) / (1 - t)) • (c + t • (e - c)) + ((k - t) / (1 - t)) • e
        = ((1 - k) / (1 - t) + (k - t) / (1 - t)) • c +
          ((1 - k) / (1 - t) * t + (k - t) / (1 - t)) • (e - c) := by module
    rw [this]
    have e1 : (1 - k) / (1 - t) + (k - t) / (1 - t) = 1 := by field_simp; ring
    have e2 : (1 - k) / (1 - t) * t + (k - t) / (1 - t) = k := by field_simp; ring
    rw [e1, e2, one_smul]
  · have hk1 : k = 1 := by linarith
    subst h1; subst hk1
    simp only [one_smul, add_sub_cancel]
    exact right_mem_segment ℝ _ _

end DK88

open Disjunctive.SequentialConvex in
theorem solution {n : ℕ} (Fjm1 : Set (Fin n → ℝ)) {Qj : Type*}
    [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    (convexHull ℝ (convexHull ℝ Fjm1 ∩ Dj d d0) = convexHull ℝ (Fjm1 ∩ Dj d d0)) ↔
      (∀ x ∈ Fjm1 ∩ Dbarj d d0, ∀ y ∈ Fjm1 ∩ Dj d d0,
        segment ℝ x y ∩ intrinsicFrontier ℝ (Dbarj d d0) ⊆ convexHull ℝ (Fjm1 ∩ Dj d d0)) := by
  set D := Dj d d0
  set Db := Dbarj d d0
  set K := convexHull ℝ (Fjm1 ∩ D)
  have hKc : Convex ℝ K := convex_convexHull ℝ _
  have memD : ∀ x, x ∈ D ↔ ∃ i, d0 i ≤ d i ⬝ᵥ x := by
    intro x; simp [D, Dj, HalfspaceGE]
  have memDb : ∀ x, x ∈ Db ↔ ∀ i, d i ⬝ᵥ x ≤ d0 i := by
    intro x; simp [Db, Dbarj, HalfspaceLE]
  set U : Set (Fin n → ℝ) := {x | ∀ i, d i ⬝ᵥ x < d0 i}
  have hUo : IsOpen U := by
    have : U = ⋂ i, {x | d i ⬝ᵥ x < d0 i} := by ext; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have hUD : U ⊆ Db := fun x hx => (memDb x).2 fun i => (hx i).le
  have hDbc : IsClosed Db := by
    have : Db = ⋂ i, {x | d i ⬝ᵥ x ≤ d0 i} := by ext; simp [memDb]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hnotD : ∀ x, x ∉ D → x ∈ U := by
    intro x hx i; by_contra h; push Not at h; exact hx ((memD x).2 ⟨i, h⟩)
  have hfr : ∀ z ∈ intrinsicFrontier ℝ Db, z ∉ intrinsicInterior ℝ Db := by
    intro z hz
    rw [← closure_sdiff_intrinsicInterior] at hz
    exact hz.2
  constructor
  · intro h35 x hx y hy z ⟨hzs, hzf⟩
    have hzF : z ∈ convexHull ℝ Fjm1 := segment_subset_convexHull hx.1 hy.1 hzs
    have hzD : z ∈ D := by
      by_contra hzD
      have : z ∈ interior Db := interior_maximal hUD hUo (hnotD z hzD)
      exact hfr z hzf (interior_subset_intrinsicInterior this)
    rw [← h35]
    exact subset_convexHull ℝ _ ⟨hzF, hzD⟩
  · intro h36
    have key : convexHull ℝ Fjm1 ∩ D ⊆ K := by
      rintro w ⟨hwF, hwD⟩
      obtain ⟨i, hi⟩ := (memD w).1 hwD
      let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun x => d i ⬝ᵥ x, map_add' := fun x y => dotProduct_add _ _ _,
          map_smul' := fun c x => by simp [dotProduct_smul] }
      have hf : ∀ x, f x = d i ⬝ᵥ x := fun x => rfl
      refine DK88.main_L3 f (d0 i) hKc Fjm1 ?_ ?_ w hwF (by rw [hf]; exact hi)
      · intro e he hfe
        exact subset_convexHull ℝ _ ⟨he, (memD e).2 ⟨i, hfe⟩⟩
      · intro c hc hfc e he hfe
        have heK : e ∈ Fjm1 ∩ D := ⟨he, (memD e).2 ⟨i, hfe⟩⟩
        by_cases hcD : c ∈ D
        · exact segment_subset_convexHull (show c ∈ Fjm1 ∩ D from ⟨hc, hcD⟩) heK
            (DK88.cross_mem_segment f _ hfc hfe)
        have hcU := hnotD c hcD
        -- exit point
        have hd : 0 < f e - f c := by linarith
        set κ := (d0 i - f c) / (f e - f c) with hκ
        have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one hd]; linarith
        have hκ0 : 0 ≤ κ := div_nonneg (by linarith) hd.le
        let p : ℝ → (Fin n → ℝ) := fun t => c + t • (e - c)
        have hpc : Continuous p := by fun_prop
        set T := {t ∈ Set.Icc (0:ℝ) 2 | p t ∈ Db}
        have hTκ : ∀ t ∈ T, t ≤ κ := by
          intro t ht
          have := ((memDb _).1 ht.2) i
          rw [← hf] at this
          simp only [p, map_add, map_smul, map_sub, smul_eq_mul] at this
          rw [hκ, le_div_iff₀ hd]; linarith
        have hTc : IsClosed T := by
          have := (isClosed_Icc (a := (0:ℝ)) (b := 2)).inter (hDbc.preimage hpc)
          convert this using 1
          ext t; simp [T]
        have hT0 : (0:ℝ) ∈ T := ⟨⟨le_refl _, by norm_num⟩, by simpa [p] using hUD hcU⟩
        have hTb : BddAbove T := ⟨2, fun t ht => ht.1.2⟩
        set ts := sSup T
        have htsT : ts ∈ T := hTc.csSup_mem ⟨0, hT0⟩ hTb
        have hts0 : 0 ≤ ts := le_csSup hTb hT0
        have htsκ : ts ≤ κ := hTκ ts htsT
        have hzfr : p ts ∈ intrinsicFrontier ℝ Db := by
          rw [← closure_sdiff_intrinsicInterior]
          refine ⟨subset_closure htsT.2, fun hint => ?_⟩
          have hspan : affineSpan ℝ Db = ⊤ :=
            top_le_iff.1 ((hUo.affineSpan_eq_top ⟨c, hcU⟩).symm.le.trans (affineSpan_mono ℝ hUD))
          have hint' := DK88.intr_sub_int hspan hint
          have hop : IsOpen (p ⁻¹' interior Db) := isOpen_interior.preimage hpc
          obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hop ts hint'
          set t' := ts + min (δ / 2) (1 / 2)
          have hm1 : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
          have hm2 : min (δ / 2) (1 / 2) ≤ δ / 2 := min_le_left _ _
          have hm3 : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
          have ht'T : t' ∈ T := by
            refine ⟨⟨by linarith, by linarith⟩, interior_subset (hball ?_)⟩
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
          have := le_csSup hTb ht'T
          linarith
        have hzseg : p ts ∈ segment ℝ c e := by
          have := DK88.seg_param c e (le_refl 0) hts0 (htsκ.trans hκ1)
          simpa [p] using this
        have hzK : p ts ∈ K := h36 c ⟨hc, (memDb c).2 fun j => (hcU j).le⟩ e heK ⟨hzseg, hzfr⟩
        have hyseg : DK88.cross f (d0 i) c e ∈ segment ℝ (p ts) e := by
          have := DK88.seg_param c e hts0 htsκ hκ1
          simpa [p, DK88.cross, ← hκ] using this
        exact hKc.segment_subset hzK (subset_convexHull ℝ _ heK) hyseg
    apply Set.Subset.antisymm
    · exact convexHull_min key hKc
    · exact convexHull_mono (fun x hx => ⟨subset_convexHull ℝ _ hx.1, hx.2⟩)
