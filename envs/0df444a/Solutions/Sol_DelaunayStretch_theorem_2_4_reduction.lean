-- Prove2me | solution 1 for DelaunayStretch.theorem_2_4_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T01:02:47.847038+00:00
-- url     : https://prove2.me/submissions/f2d9ec4b-8048-44f1-b0dc-21d8265f33fa

import Theorems.Thm_DelaunayStretch_lemma_2_3_one_disk
import Theorems.Thm_DelaunayStretch_lemma_A_3_A_4_generated_chain

open DelaunayStretch

/-- `walkLength` is additive under `append`. -/
theorem t24_walkLength_append {G : SimpleGraph ℂ} {a b c : ℂ} (w₁ : G.Walk a b)
    (w₂ : G.Walk b c) : walkLength (w₁.append w₂) = walkLength w₁ + walkLength w₂ := by
  unfold walkLength
  rw [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

/-- `walkLength` is invariant under `copy`. -/
theorem t24_walkLength_copy {G : SimpleGraph ℂ} {a b a' b' : ℂ} (w : G.Walk a b)
    (ha : a = a') (hb : b = b') : walkLength (w.copy ha hb) = walkLength w := by
  subst ha hb; rfl

/-- `walkLength` is invariant under mapping by a distance-preserving graph homomorphism. -/
theorem t24_walkLength_map {G G' : SimpleGraph ℂ} (f : G →g G')
    (hf : ∀ a b, dist (f a) (f b) = dist a b) {a b : ℂ} (w : G.Walk a b) :
    walkLength (w.map f) = walkLength w := by
  unfold walkLength
  rw [SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _
  simp [SimpleGraph.Hom.mapDart_apply, hf]

/-- The walk along one edge. -/
theorem t24_walkLength_edge {G : SimpleGraph ℂ} {a b : ℂ} (h : G.Adj a b) :
    walkLength h.toWalk = dist a b := by
  simp [walkLength, SimpleGraph.Adj.toWalk]

/-- Affine maps preserve collinearity. -/
theorem t24_collinear_image (g : ℂ →ᵃ[ℝ] ℂ) (s : Set ℂ) (h : Collinear ℝ s) :
    Collinear ℝ (g '' s) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p₀, v, hv⟩ := h
  refine ⟨g p₀, g.linear v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := hv p hp
  exact ⟨r, by rw [AffineMap.map_vadd, LinearMap.map_smul]⟩

/-- Delaunay triangulations are invariant under affine isometries of the plane. -/
theorem t24_delaunay_image (e : ℂ ≃ᵃⁱ[ℝ] ℂ) {S : Finset ℂ} {D : Finset (Finset ℂ)}
    (hD : IsDelaunayTriangulation S D) :
    IsDelaunayTriangulation (S.image e) (D.image (Finset.image e)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hD
  have hinj : Function.Injective e := e.injective
  have hconv : ∀ s : Set ℂ, e '' convexHull ℝ s = convexHull ℝ (e '' s) := fun s =>
    AffineMap.image_convexHull e.toAffineEquiv.toAffineMap s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
    obtain ⟨hc, nc, sub⟩ := h1 T hT
    refine ⟨by rw [Finset.card_image_of_injective _ hinj, hc], ?_,
      Finset.image_subset_image sub⟩
    intro hcol
    apply nc
    rw [Finset.coe_image] at hcol
    have := t24_collinear_image e.symm.toAffineEquiv.toAffineMap _ hcol
    convert this using 1
    ext x
    simp
  · rw [Finset.set_biUnion_finset_image]
    simp_rw [Finset.coe_image, ← hconv]
    rw [← Set.image_iUnion₂, h2, hconv]
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨T, hT, haT⟩ := h3 a ha
    exact ⟨T.image e, Finset.mem_image_of_mem _ hT, Finset.mem_image_of_mem _ haT⟩
  · intro T1' hT1' T2' hT2' hne
    obtain ⟨T1, hT1, rfl⟩ := Finset.mem_image.1 hT1'
    obtain ⟨T2, hT2, rfl⟩ := Finset.mem_image.1 hT2'
    have hne' : T1 ≠ T2 := by rintro rfl; exact hne rfl
    rw [Finset.coe_image, Finset.coe_image, ← hconv, ← hconv, ← Set.image_inter hinj,
      h4 T1 hT1 T2 hT2 hne', ← Set.image_inter hinj, hconv]
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
    obtain ⟨o, r, hp, hq⟩ := h5 T hT
    refine ⟨e o, r, ?_, ?_⟩
    · intro p hp'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp'
      rw [e.dist_map]; exact hp a ha
    · intro q hq'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hq'
      rw [e.dist_map]; exact hq a ha

theorem t24_mem_image_symm (e : ℂ ≃ᵃⁱ[ℝ] ℂ) {T : Finset ℂ} {p : ℂ} (hp : p ∈ T.image e) :
    e.symm p ∈ T := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
  simpa using ha

/-- The inverse isometry is a homomorphism of the edge graphs. -/
noncomputable def t24_backHom (e : ℂ ≃ᵃⁱ[ℝ] ℂ) (D : Finset (Finset ℂ)) :
    delaunayGraph (D.image (Finset.image e)) →g delaunayGraph D where
  toFun := e.symm
  map_rel' := by
    intro p q h
    simp only [delaunayGraph, SimpleGraph.fromRel_adj] at h ⊢
    obtain ⟨hne, h⟩ := h
    refine ⟨fun h' => hne (e.symm.injective h'), ?_⟩
    rcases h with ⟨T', hT', hp, hq⟩ | ⟨T', hT', hq, hp⟩
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
      exact Or.inl ⟨T, hT, t24_mem_image_symm e hp, t24_mem_image_symm e hq⟩
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
      exact Or.inr ⟨T, hT, t24_mem_image_symm e hq, t24_mem_image_symm e hp⟩

theorem t24_backHom_apply (e : ℂ ≃ᵃⁱ[ℝ] ℂ) (D : Finset (Finset ℂ)) (z : ℂ) :
    t24_backHom e D z = e.symm z := rfl

/-- Transport a walk in the image triangulation back. -/
theorem t24_walk_back (e : ℂ ≃ᵃⁱ[ℝ] ℂ) (D : Finset (Finset ℂ)) (u v : ℂ)
    (w : (delaunayGraph (D.image (Finset.image e))).Walk (e u) (e v)) :
    ∃ w' : (delaunayGraph D).Walk u v, walkLength w' = walkLength w := by
  refine ⟨(w.map (t24_backHom e D)).copy (by simp [t24_backHom_apply])
    (by simp [t24_backHom_apply]), ?_⟩
  rw [t24_walkLength_copy, t24_walkLength_map]
  intro a b
  simp [t24_backHom_apply]

/-- The rigid motion sending `u` to `0` and `v` to the positive real `‖v - u‖`. -/
theorem t24_rigid (u v : ℂ) :
    ∃ e : ℂ ≃ᵃⁱ[ℝ] ℂ, e u = 0 ∧ e v = ((‖v - u‖ : ℝ) : ℂ) := by
  let c : Circle := Circle.exp (-(v - u).arg)
  refine ⟨(AffineIsometryEquiv.vaddConst ℝ u).symm.trans (rotation c).toAffineIsometryEquiv,
    ?_, ?_⟩
  · simp
  · have hw := Complex.norm_mul_exp_arg_mul_I (v - u)
    have : (c : ℂ) * (v - u) = ((‖v - u‖ : ℝ) : ℂ) := by
      calc (c : ℂ) * (v - u)
          = Complex.exp (↑(-(v - u).arg) * Complex.I) *
              (↑‖v - u‖ * Complex.exp (↑(v - u).arg * Complex.I)) := by
            rw [hw]; rfl
        _ = ↑‖v - u‖ * Complex.exp (↑(-(v - u).arg) * Complex.I +
              ↑(v - u).arg * Complex.I) := by rw [Complex.exp_add]; ring
        _ = ↑‖v - u‖ := by push_cast; ring_nf; simp
    simpa [rotation_apply] using this

theorem t24_openSeg_sub (u v p : ℂ) (hp : p ∈ openSegment ℝ u v) :
    openSegment ℝ u p ⊆ openSegment ℝ u v := by
  simp only [openSegment_eq_image'] at hp ⊢
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
  rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
  refine ⟨s * t, ⟨mul_pos hs0 ht0, by nlinarith⟩, ?_⟩
  simp only [add_sub_cancel_left, smul_smul]

theorem t24_openSeg_sub' (u v p : ℂ) (hp : p ∈ openSegment ℝ u v) :
    openSegment ℝ p v ⊆ openSegment ℝ u v := by
  rw [openSegment_symm ℝ p v, openSegment_symm ℝ u v]
  apply t24_openSeg_sub
  rwa [openSegment_symm]

/-- The base case: no point of `S` in the open segment. -/
theorem t24_base (U : ℝ) (hU : ChainInequality U) (hU1 : 1 ≤ U) (S : Finset ℂ)
    (D : Finset (Finset ℂ)) (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S)
    (hv : v ∈ S) (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) :
    ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ U * dist u v := by
  have hd := dist_nonneg (x := u) (y := v)
  by_cases huv : u = v
  · subst huv
    exact ⟨SimpleGraph.Walk.nil, by simp [walkLength]⟩
  by_cases hedge : IsEdgeOf D u v
  · obtain ⟨hne, T, hT, huT, hvT⟩ := hedge
    have hadj : (delaunayGraph D).Adj u v := by
      simp only [delaunayGraph, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl ⟨T, hT, huT, hvT⟩⟩
    refine ⟨hadj.toWalk, ?_⟩
    rw [t24_walkLength_edge]
    nlinarith
  obtain ⟨e, heu, hev⟩ := t24_rigid u v
  have hinj : Function.Injective e := e.injective
  have hD' := t24_delaunay_image e hD
  have hopen' : ∀ p ∈ S.image e, p ∉ openSegment ℝ (e u) (e v) := by
    intro p hp hseg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    apply hopen a ha
    have himg := image_openSegment ℝ e.symm.toAffineEquiv.toAffineMap (e u) (e v)
    have h2 : e.symm.toAffineEquiv.toAffineMap (e a) ∈ openSegment ℝ
        (e.symm.toAffineEquiv.toAffineMap (e u)) (e.symm.toAffineEquiv.toAffineMap (e v)) :=
      himg ▸ ⟨e a, hseg, rfl⟩
    simpa using h2
  have hnot' : ¬ IsEdgeOf (D.image (Finset.image e)) (e u) (e v) := by
    rintro ⟨hne, T', hT', hu', hv'⟩
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
    exact hedge ⟨huv, T, hT, (hinj.mem_finset_image).1 hu', (hinj.mem_finset_image).1 hv'⟩
  have hpos : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm huv))
  obtain ⟨C, hC, hCu, hCv, w, hw⟩ := lemma_A_3_A_4_generated_chain (S.image e)
    (D.image (Finset.image e)) hD' (e u) (e v) (Finset.mem_image_of_mem _ hu)
    (Finset.mem_image_of_mem _ hv) hopen' hnot' (by simp [heu]) (by simp [hev])
    (by simp [heu, hev, hpos])
  obtain ⟨w', hw'⟩ := t24_walk_back e D u v w
  refine ⟨w', ?_⟩
  have h1 := hU C hC
  rw [hCu, hCv, e.dist_map] at h1
  rw [hw']
  exact hw.trans h1

open Classical in
theorem t24_induct (U : ℝ) (hU : ChainInequality U) (hU1 : 1 ≤ U) (S : Finset ℂ)
    (D : Finset (Finset ℂ)) (hD : IsDelaunayTriangulation S D) (n : ℕ) :
    ∀ u v : ℂ, u ∈ S → v ∈ S → (S.filter (fun p => p ∈ openSegment ℝ u v)).card ≤ n →
      ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ U * dist u v := by
  induction n with
  | zero =>
    intro u v hu hv hcard
    apply t24_base U hU hU1 S D hD u v hu hv
    intro p hp hseg
    have := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    have hmem : p ∈ S.filter (fun p => p ∈ openSegment ℝ u v) := Finset.mem_filter.2 ⟨hp, hseg⟩
    rw [this] at hmem
    simp at hmem
  | succ n ih =>
    intro u v hu hv hcard
    by_cases hex : ∃ p ∈ S, p ∈ openSegment ℝ u v
    · by_cases huv : u = v
      · subst huv
        exact ⟨SimpleGraph.Walk.nil, by simp [walkLength]⟩
      obtain ⟨p, hp, hseg⟩ := hex
      have hpu : p ≠ u := by
        rintro rfl
        exact huv ((left_mem_openSegment_iff).1 hseg)
      have hpv : p ≠ v := by
        rintro rfl
        exact huv ((right_mem_openSegment_iff).1 hseg)
      have hlt1 : (S.filter (fun q => q ∈ openSegment ℝ u p)).card ≤ n := by
        have : S.filter (fun q => q ∈ openSegment ℝ u p) ⊂
            S.filter (fun q => q ∈ openSegment ℝ u v) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨p, Finset.mem_filter.2 ⟨hp, hseg⟩, ?_⟩
            intro h
            exact hpu.symm ((right_mem_openSegment_iff).1 (Finset.mem_filter.1 h).2)
          · intro x hx
            rw [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, t24_openSeg_sub u v p hseg hx.2⟩
        have := Finset.card_lt_card this
        omega
      have hlt2 : (S.filter (fun q => q ∈ openSegment ℝ p v)).card ≤ n := by
        have : S.filter (fun q => q ∈ openSegment ℝ p v) ⊂
            S.filter (fun q => q ∈ openSegment ℝ u v) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨p, Finset.mem_filter.2 ⟨hp, hseg⟩, ?_⟩
            intro h
            exact hpv ((left_mem_openSegment_iff).1 (Finset.mem_filter.1 h).2)
          · intro x hx
            rw [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, t24_openSeg_sub' u v p hseg hx.2⟩
        have := Finset.card_lt_card this
        omega
      obtain ⟨w₁, hw₁⟩ := ih u p hu hp hlt1
      obtain ⟨w₂, hw₂⟩ := ih p v hp hv hlt2
      refine ⟨w₁.append w₂, ?_⟩
      rw [t24_walkLength_append]
      have hsplit := dist_add_dist_of_mem_segment (openSegment_subset_segment ℝ u v hseg)
      rw [← hsplit, mul_add]
      linarith
    · push Not at hex
      exact t24_base U hU hU1 S D hD u v hu hv hex

theorem solution (U : ℝ) (hU : ChainInequality U) (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S) :
    ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ U * dist u v := by
  classical
  have hU1 : 1 ≤ U := by
    have h := lemma_2_3_one_disk.2.2.1 U hU
    have := Real.pi_gt_three
    linarith
  exact t24_induct U hU hU1 S D hD _ u v hu hv le_rfl
