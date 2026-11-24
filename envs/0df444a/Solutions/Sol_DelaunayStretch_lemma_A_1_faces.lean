-- Prove2me | solution 1 for DelaunayStretch.lemma_A_1_faces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:07:47.326161+00:00
-- url     : https://prove2.me/submissions/5946e4d7-8e5b-4e33-b282-90f8c25b29fc

import Mathlib
import Definitions.Def_DelaunayStretch_face

set_option autoImplicit false

open DelaunayStretch

namespace LemmaA1

/-- Three distinct points determine the circle through them. -/
theorem sph_unique {a b c o o' : ℂ} {r r' : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : dist a o = r) (hb : dist b o = r) (hc : dist c o = r)
    (ha' : dist a o' = r') (hb' : dist b o' = r') (hc' : dist c o' = r') :
    o = o' ∧ r = r' := by
  by_contra hne
  have hs : (⟨o, r⟩ : EuclideanGeometry.Sphere ℂ) ≠ ⟨o', r'⟩ := by
    intro h
    apply hne
    simp only [EuclideanGeometry.Sphere.mk.injEq] at h
    exact h
  have := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
    Complex.finrank_real_complex hs hab
    (EuclideanGeometry.mem_sphere.2 ha) (EuclideanGeometry.mem_sphere.2 hb)
    (EuclideanGeometry.mem_sphere.2 hc) (EuclideanGeometry.mem_sphere.2 ha')
    (EuclideanGeometry.mem_sphere.2 hb') (EuclideanGeometry.mem_sphere.2 hc')
  rcases this with h | h
  · exact hac h.symm
  · exact hbc h.symm

/-- The circumcircle of a three-point set `T` is the circle through `T` of any center/radius. -/
theorem circumcircle_eq_of {T : Finset ℂ} (hT : T.card = 3) {o : ℂ} {r : ℝ}
    (h : ∀ p ∈ T, dist p o = r) : circumcircle T = {p | dist p o = r} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT
  ext p
  constructor
  · rintro ⟨o', r', h', hp⟩
    obtain ⟨h1, h2⟩ := sph_unique hab hac hbc (h' a (by simp)) (h' b (by simp)) (h' c (by simp))
      (h a (by simp)) (h b (by simp)) (h c (by simp))
    simp only [Set.mem_ofPred_eq]
    rw [← h1, ← h2]; exact hp
  · intro hp
    exact ⟨o, r, h, hp⟩

theorem dist_sq_coord (w o : ℂ) : dist w o ^ 2 = (w.re - o.re) ^ 2 + (w.im - o.im) ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  simp; ring

/-- power of a point (coordinates). -/
noncomputable def pw (o : ℂ) (r : ℝ) (w : ℂ) : ℝ := (w.re - o.re) ^ 2 + (w.im - o.im) ^ 2 - r ^ 2

theorem pw_eq_zero {o w : ℂ} {r : ℝ} (h : dist w o = r) : pw o r w = 0 := by
  unfold pw; rw [← dist_sq_coord, h]; ring

theorem pw_nonneg {o w : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : r ≤ dist w o) : 0 ≤ pw o r w := by
  unfold pw; rw [← dist_sq_coord]; nlinarith

theorem dist_of_pw_eq_zero {o w : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : pw o r w = 0) : dist w o = r := by
  unfold pw at h; rw [← dist_sq_coord] at h
  have h2 : dist w o ^ 2 = r ^ 2 := by linarith
  exact (pow_left_inj₀ dist_nonneg hr two_ne_zero).1 h2

theorem pw_sub (o o' : ℂ) (r r' : ℝ) (w : ℂ) :
    pw o r w - pw o' r' w = (2 * (o'.re - o.re)) * w.re + (2 * (o'.im - o.im)) * w.im +
      ((o.re ^ 2 + o.im ^ 2 - r ^ 2) - (o'.re ^ 2 + o'.im ^ 2 - r' ^ 2)) := by
  unfold pw; ring

theorem aff_sum (A : Finset ℂ) (μ : ℂ → ℝ) (hμ : ∑ y ∈ A, μ y = 1) (a b k : ℝ) :
    a * (∑ y ∈ A, μ y • y).re + b * (∑ y ∈ A, μ y • y).im + k =
      ∑ y ∈ A, μ y * (a * y.re + b * y.im + k) := by
  simp only [Complex.re_sum, Complex.im_sum, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_mul, hμ]
  rw [one_mul]
  congr 1; congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> ring

theorem aff_nonpos_hull {A : Finset ℂ} {g : ℂ → ℝ} {a b k : ℝ}
    (hg : ∀ w, g w = a * w.re + b * w.im + k) (hA : ∀ y ∈ A, g y ≤ 0) {x : ℂ}
    (hx : x ∈ convexHull ℝ (A : Set ℂ)) : g x ≤ 0 := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := Finset.mem_convexHull'.1 hx
  rw [hg, aff_sum A μ hμ1]
  apply Finset.sum_nonpos
  intro y hy
  rw [← hg]
  exact mul_nonpos_of_nonneg_of_nonpos (hμ0 y hy) (hA y hy)

theorem aff_face {A : Finset ℂ} {g : ℂ → ℝ} {a b k : ℝ}
    (hg : ∀ w, g w = a * w.re + b * w.im + k) (hA : ∀ y ∈ A, g y ≤ 0) {x : ℂ}
    (hx : x ∈ convexHull ℝ (A : Set ℂ)) (hx0 : g x = 0) :
    x ∈ convexHull ℝ ((A.filter (fun y => g y = 0) : Finset ℂ) : Set ℂ) := by
  classical
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := Finset.mem_convexHull'.1 hx
  rw [hg, aff_sum A μ hμ1] at hx0
  have hterm : ∀ y ∈ A, μ y * (a * y.re + b * y.im + k) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun y hy => by
      rw [← hg]; exact mul_nonpos_of_nonneg_of_nonpos (hμ0 y hy) (hA y hy))).1 hx0
    exact this
  have hz : ∀ y ∈ A, ¬ g y = 0 → μ y = 0 := by
    intro y hy hne
    rcases mul_eq_zero.1 (hterm y hy) with h | h
    · exact h
    · exact absurd (by rw [hg]; exact h) hne
  rw [Finset.mem_convexHull']
  refine ⟨μ, fun y hy => hμ0 y (Finset.mem_filter.1 hy).1, ?_, ?_⟩
  · rw [Finset.sum_filter_of_ne]; · exact hμ1
    intro y hy hne; by_contra h; exact hne (hz y hy h)
  · rw [Finset.sum_filter_of_ne]
    intro y hy hne; by_contra h; exact hne (by rw [hz y hy h, zero_smul])


theorem aff_not_interior {X : Set ℂ} {g : ℂ → ℝ} {a b k : ℝ}
    (hg : ∀ w, g w = a * w.re + b * w.im + k) (hab : ¬ (a = 0 ∧ b = 0))
    (hX : ∀ y ∈ X, g y ≤ 0) {w : ℂ} (hw : g w = 0) : w ∉ interior X := by
  intro hint
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hn : 0 < a ^ 2 + b ^ 2 := by
    by_contra h
    apply hab
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  set n : ℂ := ⟨a, b⟩
  set t : ℝ := δ / (2 * ‖n‖)
  have hnpos : 0 < ‖n‖ := by
    apply norm_pos_iff.2
    intro h0
    apply hab
    have h1 : n.re = 0 := by rw [h0]; rfl
    have h2 : n.im = 0 := by rw [h0]; rfl
    exact ⟨h1, h2⟩
  have ht : 0 < t := by positivity
  have hmem : w + (t : ℂ) * n ∈ X := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    simp only [t]
    field_simp
    linarith
  have := hX _ hmem
  rw [hg] at this hw
  simp [n, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at this
  nlinarith [mul_pos ht hn]

theorem aff_null {a b k : ℝ} (hab : ¬ (a = 0 ∧ b = 0)) :
    MeasureTheory.volume {w : ℂ | a * w.re + b * w.im + k = 0} = 0 := by
  have hn : 0 < a ^ 2 + b ^ 2 := by
    by_contra h
    apply hab
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  let L : ℂ →ₗ[ℝ] ℝ := a • Complex.reLm + b • Complex.imLm
  have hL : ∀ w, L w = a * w.re + b * w.im := by
    intro w; simp [L]
  set w0 : ℂ := ⟨-k / (a ^ 2 + b ^ 2) * a, -k / (a ^ 2 + b ^ 2) * b⟩
  have hw0' : a * w0.re + b * w0.im = -k := by
    simp only [w0]; field_simp; ring
  have hw0 : L w0 = -k := by rw [hL]; exact hw0'
  let s : AffineSubspace ℝ ℂ := AffineSubspace.mk' w0 (LinearMap.ker L)
  have hs : (s : Set ℂ) = {w : ℂ | a * w.re + b * w.im + k = 0} := by
    ext w
    simp only [SetLike.mem_coe, s, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub,
      Set.mem_ofPred_eq, hL, Complex.sub_re, Complex.sub_im]
    constructor <;> intro h <;> linarith
  rw [← hs]
  apply MeasureTheory.Measure.addHaar_affineSubspace
  intro htop
  have : w0 + (⟨a, b⟩ : ℂ) ∈ s := by rw [htop]; exact AffineSubspace.mem_top _ _ _
  rw [← SetLike.mem_coe, hs] at this
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.add_im] at this
  have h2 := hw0
  rw [hL] at h2
  nlinarith


/-- A line `{a·re + b·im = c}` meets a circle in at most two points. -/
theorem line_circle {x y z o : ℂ} {r a b : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : dist x o = r) (hy : dist y o = r) (hz : dist z o = r)
    (h1 : a * x.re + b * x.im = a * y.re + b * y.im)
    (h2 : a * x.re + b * x.im = a * z.re + b * z.im) : a = 0 ∧ b = 0 := by
  set o' : ℂ := ⟨o.re + a, o.im + b⟩
  have key : ∀ p : ℂ, dist p o' ^ 2 =
      dist p o ^ 2 - 2 * (a * (p.re - o.re) + b * (p.im - o.im)) + a ^ 2 + b ^ 2 := by
    intro p; rw [dist_sq_coord, dist_sq_coord]; simp only [o']; ring
  have hy' : dist y o' = dist x o' := by
    apply (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1
    rw [key, key, hx, hy]; linarith
  have hz' : dist z o' = dist x o' := by
    apply (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1
    rw [key, key, hx, hz]; linarith
  obtain ⟨h, -⟩ := sph_unique hxy hxz hyz hx hy hz rfl hy' hz'
  have hre : o.re = o'.re := by rw [← h]
  have him : o.im = o'.im := by rw [← h]
  simp only [o'] at hre him
  constructor <;> linarith

theorem hull_sub_closedBall {A : Set ℂ} {o : ℂ} {r : ℝ} (hA : ∀ p ∈ A, dist p o ≤ r) :
    convexHull ℝ A ⊆ Metric.closedBall o r :=
  convexHull_min (fun p hp => Metric.mem_closedBall.2 (hA p hp)) (convex_closedBall o r)

theorem extreme_closedBall {o p : ℂ} {r : ℝ} (hp : dist p o = r) :
    p ∈ Set.extremePoints ℝ (Metric.closedBall o r) := by
  rw [mem_extremePoints]
  refine ⟨Metric.mem_closedBall.2 hp.le, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hseg
  by_cases h12 : x₁ = x₂
  · subst h12
    rw [openSegment_same] at hseg
    exact ⟨hseg.symm, hseg.symm⟩
  · exfalso
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hseg
    have := strictConvex_closedBall ℝ o r hx₁ hx₂ h12 hs ht hst
    rw [interior_closedBall'] at this
    rw [Metric.mem_ball] at this
    linarith

theorem extreme_of_sphere {A : Set ℂ} {o : ℂ} {r : ℝ} (hA : ∀ p ∈ A, dist p o = r) {p : ℂ}
    (hp : p ∈ A) : p ∈ Set.extremePoints ℝ (convexHull ℝ A) := by
  apply inter_extremePoints_subset_extremePoints_of_subset
    (hull_sub_closedBall (fun q hq => (hA q hq).le))
  exact ⟨subset_convexHull ℝ A hp, extreme_closedBall (hA p hp)⟩

theorem clm_coord (f : StrongDual ℝ ℂ) (w : ℂ) : f w = f 1 * w.re + f Complex.I * w.im := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem affineSpan_triangle {T : Finset ℂ} (hT : T.card = 3) (hnc : ¬ Collinear ℝ (T : Set ℂ)) :
    affineSpan ℝ (T : Set ℂ) = ⊤ := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT
  have hc : ((({a, b, c} : Finset ℂ)) : Set ℂ) = {a, b, c} := by simp
  rw [hc] at hnc ⊢
  have hind := affineIndependent_iff_not_collinear_set.2 hnc
  have := (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
    (by simp [Complex.finrank_real_complex])
  rw [← this]
  congr 1
  ext x; simp [Matrix.range_cons, Matrix.range_empty]; tauto


section Ctx

variable {S : Finset ℂ} {D : Finset (Finset ℂ)} {o : Finset ℂ → ℂ} {r : Finset ℂ → ℝ}

/-- vertex set of the face, as a finset. -/
noncomputable def verts (S : Finset ℂ) (o : ℂ) (r : ℝ) : Finset ℂ :=
  by classical exact S.filter (fun p => dist p o = r)

theorem mem_verts {S : Finset ℂ} {o p : ℂ} {r : ℝ} :
    p ∈ verts S o r ↔ p ∈ S ∧ dist p o = r := by
  classical
  unfold verts; convert Finset.mem_filter

theorem r_nonneg (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : 0 ≤ r T := by
  have hc := (hD.1 T hT).1
  obtain ⟨p, hp⟩ : T.Nonempty := by rw [← Finset.card_pos, hc]; norm_num
  rw [← (hor T hT).1 p hp]; exact dist_nonneg

theorem circ_D (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : circumcircle T = {p | dist p (o T) = r T} :=
  circumcircle_eq_of (hD.1 T hT).1 (hor T hT).1

theorem face_D (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : face S T = convexHull ℝ (verts S (o T) (r T) : Set ℂ) := by
  unfold face
  rw [circ_D hD hor hT]
  congr 1
  ext p; simp [mem_verts]

theorem T_sub_verts (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : T ⊆ verts S (o T) (r T) := by
  intro p hp
  exact mem_verts.2 ⟨(hD.1 T hT).2.2 hp, (hor T hT).1 p hp⟩

theorem face_interior (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : (interior (face S T)).Nonempty := by
  rw [face_D hD hor hT, interior_convexHull_nonempty_iff_affineSpan_eq_top]
  apply eq_top_iff.2
  rw [← affineSpan_triangle (hD.1 T hT).1 (hD.1 T hT).2.1]
  apply affineSpan_mono
  exact_mod_cast T_sub_verts hD hor hT

theorem psi_nonpos (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T T' : Finset ℂ} (hT : T ∈ D) (hT' : T' ∈ D) {x : ℂ} (hx : x ∈ face S T) :
    pw (o T) (r T) x - pw (o T') (r T') x ≤ 0 := by
  rw [face_D hD hor hT] at hx
  refine aff_nonpos_hull (g := fun w => pw (o T) (r T) w - pw (o T') (r T') w)
    (fun w => pw_sub _ _ _ _ w) ?_ hx
  intro y hy
  obtain ⟨hyS, hyd⟩ := mem_verts.1 hy
  show pw (o T) (r T) y - pw (o T') (r T') y ≤ 0
  rw [pw_eq_zero hyd]
  have := pw_nonneg (r_nonneg hD hor hT') ((hor T' hT').2 y hyS)
  linarith

theorem face_sub_ball (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : face S T ⊆ Metric.closedBall (o T) (r T) := by
  rw [face_D hD hor hT]
  exact hull_sub_closedBall (fun p hp => (mem_verts.1 hp).2.le)

/-- Part (1a). -/
theorem ext_face (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) :
    Set.extremePoints ℝ (face S T) = (S : Set ℂ) ∩ circumcircle T := by
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  intro p hp
  apply extreme_of_sphere (o := o T) (r := r T) _ hp
  intro q hq
  have := hq.2
  rw [circ_D hD hor hT] at this
  exact this

/-- Part (1b). -/
theorem hull_sub_face_iff (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T T' : Finset ℂ} (hT : T ∈ D) (hT' : T' ∈ D) :
    convexHull ℝ (T' : Set ℂ) ⊆ face S T ↔ circumcircle T' = circumcircle T := by
  constructor
  · intro h
    rw [circ_D hD hor hT]
    apply circumcircle_eq_of (hD.1 T' hT').1
    intro p hp
    have h1 := Metric.mem_closedBall.1
      (face_sub_ball hD hor hT (h (subset_convexHull ℝ _ (by exact_mod_cast hp))))
    have h2 := (hor T hT).2 p ((hD.1 T' hT').2.2 hp)
    linarith
  · intro h
    unfold face
    apply convexHull_mono
    intro p hp
    refine ⟨(hD.1 T' hT').2.2 hp, ?_⟩
    rw [← h, circ_D hD hor hT']
    exact (hor T' hT').1 p hp

theorem hull_sub_own_face (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) : convexHull ℝ (T : Set ℂ) ⊆ face S T :=
  (hull_sub_face_iff hD hor hT hT).2 rfl


theorem same_circ_of_psi (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T T' : Finset ℂ} (hT : T ∈ D) (hT' : T' ∈ D) (ho : o T' = o T) {y : ℂ}
    (hy : pw (o T) (r T) y - pw (o T') (r T') y = 0) : r T' = r T := by
  unfold pw at hy
  rw [ho] at hy
  have h2 : r T' ^ 2 = r T ^ 2 := by linarith
  exact (pow_left_inj₀ (r_nonneg hD hor hT') (r_nonneg hD hor hT) two_ne_zero).1 h2

/-- Part (1c): the triangles with the same circumcircle cover the face. -/
theorem cover_face (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) {x : ℂ} (hx : x ∈ face S T) :
    ∃ T' ∈ D, circumcircle T' = circumcircle T ∧ x ∈ convexHull ℝ (T' : Set ℂ) := by
  classical
  by_contra hne
  push Not at hne
  set G : Set ℂ := ⋃ T' ∈ D.filter (fun T' => circumcircle T' = circumcircle T),
    convexHull ℝ (T' : Set ℂ) with hGdef
  have hGc : IsClosed G :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
      (fun T' _ => (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (T'.finite_toSet) :
        IsCompact (convexHull ℝ (T' : Set ℂ))).isClosed)
  have hxG : x ∉ G := by
    simp only [hGdef, Set.mem_iUnion, Finset.mem_filter, not_exists]
    rintro T' ⟨hT', hc⟩
    exact hne T' hT' hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl x hxG
  have hcl : x ∈ closure (interior (face S T)) := by
    have hcv : Convex ℝ (face S T) := convex_convexHull ℝ _
    rw [hcv.closure_interior_eq_closure_of_nonempty_interior (face_interior hD hor hT)]
    exact subset_closure hx
  obtain ⟨y0, hy0int, hy0d⟩ := Metric.mem_closure_iff.1 hcl ε hε
  set U : Set ℂ := Metric.ball x ε ∩ interior (face S T) with hU
  have hUo : IsOpen U := Metric.isOpen_ball.inter isOpen_interior
  have hUne : U.Nonempty := ⟨y0, Metric.mem_ball.2 (by rw [dist_comm]; exact hy0d), hy0int⟩
  set Z : Finset ℂ → Set ℂ := fun T' =>
    {w | o T' ≠ o T ∧ pw (o T) (r T) w - pw (o T') (r T') w = 0} with hZ
  have hZ0 : ∀ T' ∈ D, MeasureTheory.volume (Z T') = 0 := by
    intro T' _
    by_cases ho : o T' = o T
    · have : Z T' = ∅ := by
        ext w; simp [hZ, ho]
      rw [this, MeasureTheory.measure_empty]
    · have : Z T' = {w : ℂ | (2 * ((o T').re - (o T).re)) * w.re +
          (2 * ((o T').im - (o T).im)) * w.im +
          (((o T).re ^ 2 + (o T).im ^ 2 - r T ^ 2) - ((o T').re ^ 2 + (o T').im ^ 2 - r T' ^ 2))
            = 0} := by
        ext w; simp only [hZ, Set.mem_ofPred_eq, pw_sub, ho, ne_eq, not_false_eq_true, true_and]
      rw [this]
      apply aff_null
      rintro ⟨h1, h2⟩
      apply ho
      apply Complex.ext <;> linarith
  have hUZ : U ⊆ ⋃ T' ∈ D, Z T' := by
    intro y hy
    have hyF : y ∈ face S T := interior_subset hy.2
    have hyS : y ∈ convexHull ℝ (S : Set ℂ) := convexHull_mono Set.inter_subset_left hyF
    rw [← hD.2.1] at hyS
    obtain ⟨T', hT', hyT'⟩ := Set.mem_iUnion₂.1 hyS
    have h1 := psi_nonpos hD hor hT hT' hyF
    have h2 := psi_nonpos hD hor hT' hT (hull_sub_own_face hD hor hT' hyT')
    have h0 : pw (o T) (r T) y - pw (o T') (r T') y = 0 := by linarith
    refine Set.mem_iUnion₂.2 ⟨T', hT', ?_, h0⟩
    intro ho
    have hr := same_circ_of_psi hD hor hT hT' ho h0
    have hc : circumcircle T' = circumcircle T := by
      rw [circ_D hD hor hT, circ_D hD hor hT', ho, hr]
    apply hball hy.1
    simp only [hGdef, Set.mem_iUnion, Finset.mem_filter]
    exact ⟨T', ⟨hT', hc⟩, hyT'⟩
  have hnull : MeasureTheory.volume U = 0 := by
    apply MeasureTheory.measure_mono_null hUZ
    refine le_antisymm ?_ bot_le
    calc MeasureTheory.volume (⋃ T' ∈ D, Z T') ≤ ∑ T' ∈ D, MeasureTheory.volume (Z T') :=
          MeasureTheory.measure_biUnion_finset_le D Z
      _ = 0 := Finset.sum_eq_zero hZ0
  exact (hUo.measure_pos MeasureTheory.volume hUne).ne' hnull


theorem mem_circ_D (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) {p : ℂ} : p ∈ circumcircle T ↔ dist p (o T) = r T := by
  rw [circ_D hD hor hT]; rfl

/-- Part (2): every edge of a face is an edge of `D`. -/
theorem face_edge (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T : Finset ℂ} (hT : T ∈ D) {x y : ℂ} (hxy : IsFaceEdge (face S T) x y) :
    IsEdgeOf D x y := by
  classical
  obtain ⟨hx, hy, hne, hseg⟩ := hxy
  have hxF : x ∈ face S T := hx.1
  have hyF : y ∈ face S T := hy.1
  rw [ext_face hD hor hT] at hx hy
  have hxd : dist x (o T) = r T := (mem_circ_D hD hor hT).1 hx.2
  have hyd : dist y (o T) = r T := (mem_circ_D hD hor hT).1 hy.2
  set z := midpoint ℝ x y with hz
  have hzF : z ∈ frontier (face S T) := hseg (midpoint_mem_segment x y)
  have hzF' : z ∈ face S T :=
    (convex_convexHull ℝ _).segment_subset hxF hyF (midpoint_mem_segment x y)
  have hzint : z ∉ interior (face S T) := hzF.2
  have hcv : Convex ℝ (face S T) := convex_convexHull ℝ _
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hcv.interior isOpen_interior hzint
  have hfF : ∀ a ∈ face S T, f a ≤ f z := by
    intro a ha
    have : a ∈ closure (interior (face S T)) := by
      rw [hcv.closure_interior_eq_closure_of_nonempty_interior (face_interior hD hor hT)]
      exact subset_closure ha
    exact closure_minimal (fun b hb => (hf b hb).le) (isClosed_le f.continuous continuous_const)
      this
  have hfz : f z = (f x + f y) / 2 := by
    rw [hz, midpoint_eq_smul_add, map_smul, map_add, smul_eq_mul]
    simp only [invOf_eq_inv]; ring
  have hfx := hfF x hxF
  have hfy := hfF y hyF
  have hfx' : f x = f z := by linarith
  have hfy' : f y = f z := by linarith
  have hf0 : ¬ (f 1 = 0 ∧ f Complex.I = 0) := by
    rintro ⟨h1, h2⟩
    obtain ⟨w, hw⟩ := face_interior hD hor hT
    have := hf w hw
    rw [clm_coord f w, clm_coord f z, h1, h2] at this
    simp at this
  obtain ⟨T', hT', hcT', hzT'⟩ := cover_face hD hor hT hzF'
  have hT'd : ∀ q ∈ T', dist q (o T) = r T := by
    intro q hq
    rw [← mem_circ_D hD hor hT, ← hcT', mem_circ_D hD hor hT']
    exact (hor T' hT').1 q hq
  have hT'F : ∀ q ∈ T', q ∈ face S T := by
    intro q hq
    exact (hull_sub_face_iff hD hor hT hT').2 hcT' (subset_convexHull ℝ _ (by exact_mod_cast hq))
  have hg : ∀ w, (fun w => f w - f z) w = f 1 * w.re + f Complex.I * w.im + (- f z) := by
    intro w; simp only; rw [clm_coord f w]; ring
  have hface := aff_face hg (fun q hq => by show f q - f z ≤ 0; linarith [hfF q (hT'F q hq)]) hzT'
    (by simp)
  have hfil : ∀ q ∈ T'.filter (fun w => f w - f z = 0), q = x ∨ q = y := by
    intro q hq
    rw [Finset.mem_filter] at hq
    by_contra hc
    push Not at hc
    apply hf0
    refine line_circle hne hc.1.symm hc.2.symm hxd hyd (hT'd q hq.1) ?_ ?_
    · rw [← clm_coord, ← clm_coord]; linarith
    · rw [← clm_coord, ← clm_coord]; linarith
  have key : ∀ u v : ℂ, (∀ q ∈ T'.filter (fun w => f w - f z = 0), q = u ∨ q = v) →
      u ∉ T' → z = v := by
    intro u v huv hu
    have hsub : ((T'.filter (fun w => f w - f z = 0) : Finset ℂ) : Set ℂ) ⊆ {v} := by
      intro q hq
      rcases huv q hq with h | h
      · exact absurd (h ▸ (Finset.mem_filter.1 hq).1) hu
      · exact h
    have := convexHull_mono hsub hface
    rw [convexHull_singleton] at this
    exact this
  refine ⟨hne, T', hT', ?_, ?_⟩
  · by_contra hxT
    have := key x y hfil hxT
    exact hne ((midpoint_eq_right_iff ℝ).1 this)
  · by_contra hyT
    have := key y x (fun q hq => (hfil q hq).symm) hyT
    exact hne ((midpoint_eq_left_iff ℝ).1 this)


/-- Part (3): two distinct faces are disjoint, or meet in a common vertex, or in a common edge. -/
theorem face_inter (hD : IsDelaunayTriangulation S D)
    (hor : ∀ T ∈ D, (∀ p ∈ T, dist p (o T) = r T) ∧ ∀ q ∈ S, r T ≤ dist q (o T))
    {T T' : Finset ℂ} (hT : T ∈ D) (hT' : T' ∈ D) (hne : face S T ≠ face S T') :
    face S T ∩ face S T' = ∅ ∨
      (∃ p : ℂ, p ∈ Set.extremePoints ℝ (face S T) ∧ p ∈ Set.extremePoints ℝ (face S T') ∧
        face S T ∩ face S T' = {p}) ∨
      (∃ x y : ℂ, IsFaceEdge (face S T) x y ∧ IsFaceEdge (face S T') x y ∧
        face S T ∩ face S T' = segment ℝ x y) := by
  classical
  set g : ℂ → ℝ := fun w => pw (o T) (r T) w - pw (o T') (r T') w with hgdef
  have hg := pw_sub (o T) (o T') (r T) (r T')
  have hgF : ∀ w ∈ face S T, g w ≤ 0 := fun w hw => psi_nonpos hD hor hT hT' hw
  have hgF' : ∀ w ∈ face S T', 0 ≤ g w := by
    intro w hw
    have := psi_nonpos hD hor hT' hT hw
    simp only [hgdef]; linarith
  have hg0 : ∀ w ∈ face S T ∩ face S T', g w = 0 :=
    fun w hw => le_antisymm (hgF w hw.1) (hgF' w hw.2)
  by_cases hemp : face S T ∩ face S T' = ∅
  · left; exact hemp
  right
  obtain ⟨w0, hw0⟩ := Set.nonempty_iff_ne_empty.2 hemp
  have ho : o T ≠ o T' := by
    intro ho
    have hr := same_circ_of_psi hD hor hT hT' ho.symm (hg0 w0 hw0)
    apply hne
    rw [face_D hD hor hT, face_D hD hor hT', ho, hr]
  have hab : ¬ (2 * ((o T').re - (o T).re) = 0 ∧ 2 * ((o T').im - (o T).im) = 0) := by
    rintro ⟨h1, h2⟩
    apply ho
    apply Complex.ext <;> linarith
  have hab' : ¬ (-(2 * ((o T').re - (o T).re)) = 0 ∧ -(2 * ((o T').im - (o T).im)) = 0) := by
    rintro ⟨h1, h2⟩
    exact hab ⟨by linarith, by linarith⟩
  set P : Finset ℂ := (verts S (o T) (r T)).filter (fun p => dist p (o T') = r T') with hPdef
  have hPv : ∀ p ∈ P, p ∈ S ∧ dist p (o T) = r T ∧ dist p (o T') = r T' := by
    intro p hp
    rw [hPdef, Finset.mem_filter, mem_verts] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hP : face S T ∩ face S T' = convexHull ℝ (P : Set ℂ) := by
    ext w
    constructor
    · intro hw
      have hgw := hg0 w hw
      have hwF := hw.1
      rw [face_D hD hor hT] at hwF
      have := aff_face (A := verts S (o T) (r T)) hg (fun y hy => hgF y
        (by rw [face_D hD hor hT]; exact subset_convexHull ℝ _ (by exact_mod_cast hy))) hwF hgw
      refine convexHull_mono ?_ this
      intro q hq
      have hq' := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
      have hqv := mem_verts.1 hq'.1
      have h2 : g q = 0 := hq'.2
      simp only [hgdef, pw_eq_zero hqv.2] at h2
      have h3 : pw (o T') (r T') q = 0 := by linarith
      rw [Finset.mem_coe, hPdef, Finset.mem_filter]
      exact ⟨hq'.1, dist_of_pw_eq_zero (r_nonneg hD hor hT') h3⟩
    · intro hw
      constructor
      · rw [face_D hD hor hT]
        refine convexHull_mono ?_ hw
        intro q hq
        exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).1
      · rw [face_D hD hor hT']
        refine convexHull_mono ?_ hw
        intro q hq
        have := hPv q (Finset.mem_coe.1 hq)
        exact Finset.mem_coe.2 (mem_verts.2 ⟨this.1, this.2.2⟩)
  have hPcard : P.card ≤ 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hc
    exact ho (sph_unique hab hac hbc (hPv a ha).2.1 (hPv b hb).2.1 (hPv c hc).2.1
      (hPv a ha).2.2 (hPv b hb).2.2 (hPv c hc).2.2).1
  have hPne : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hemp
    rw [hP, h, Finset.coe_empty, convexHull_empty]
  have hext : ∀ p ∈ P, p ∈ Set.extremePoints ℝ (face S T) ∧
      p ∈ Set.extremePoints ℝ (face S T') := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hPv p hp
    rw [ext_face hD hor hT, ext_face hD hor hT']
    exact ⟨⟨h1, (mem_circ_D hD hor hT).2 h2⟩, ⟨h1, (mem_circ_D hD hor hT').2 h3⟩⟩
  have hpos := hPne.card_pos
  by_cases hc1 : P.card = 1
  · left
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc1
    have hpP : p ∈ P := by rw [hp]; exact Finset.mem_singleton_self p
    refine ⟨p, (hext p hpP).1, (hext p hpP).2, ?_⟩
    rw [hP, hp, Finset.coe_singleton, convexHull_singleton]
  · right
    have hc2 : P.card = 2 := by omega
    obtain ⟨x, y, hxy, hp⟩ := Finset.card_eq_two.1 hc2
    have hxP : x ∈ P := by rw [hp]; simp
    have hyP : y ∈ P := by rw [hp]; simp
    have hseg : face S T ∩ face S T' = segment ℝ x y := by
      rw [hP, hp, Finset.coe_pair, convexHull_pair]
    have hg' : ∀ w, (fun w => - g w) w = -(2 * ((o T').re - (o T).re)) * w.re +
        -(2 * ((o T').im - (o T).im)) * w.im +
        -(((o T).re ^ 2 + (o T).im ^ 2 - r T ^ 2) - ((o T').re ^ 2 + (o T').im ^ 2 - r T' ^ 2)) := by
      intro w; simp only [hgdef]; rw [hg w]; ring
    refine ⟨x, y, ⟨(hext x hxP).1, (hext y hyP).1, hxy, ?_⟩,
      ⟨(hext x hxP).2, (hext y hyP).2, hxy, ?_⟩, hseg⟩
    · intro w hw
      rw [← hseg] at hw
      exact ⟨subset_closure hw.1, aff_not_interior hg hab hgF (hg0 w hw)⟩
    · intro w hw
      rw [← hseg] at hw
      refine ⟨subset_closure hw.2, aff_not_interior hg' hab' ?_ (by simp [hg0 w hw])⟩
      intro y hy
      have := hgF' y hy
      show -g y ≤ 0
      linarith

end Ctx

end LemmaA1

open LemmaA1 in
theorem solution (S : Finset ℂ) (D : Finset (Finset ℂ)) (hD : IsDelaunayTriangulation S D) :
    (∀ T ∈ D,
      Set.extremePoints ℝ (face S T) = (S : Set ℂ) ∩ circumcircle T ∧
      (∀ T' ∈ D, convexHull ℝ (T' : Set ℂ) ⊆ face S T ↔ circumcircle T' = circumcircle T) ∧
      (⋃ T' ∈ D, ⋃ (_ : circumcircle T' = circumcircle T), convexHull ℝ (T' : Set ℂ)) =
        face S T) ∧
    (⋃ T ∈ D, face S T) = convexHull ℝ (S : Set ℂ) ∧
    (∀ F : Set ℂ, IsFace S D F → ∀ x y : ℂ, IsFaceEdge F x y → IsEdgeOf D x y) ∧
    (∀ F F' : Set ℂ, IsFace S D F → IsFace S D F' → F ≠ F' →
      F ∩ F' = ∅ ∨
      (∃ p : ℂ, p ∈ Set.extremePoints ℝ F ∧ p ∈ Set.extremePoints ℝ F' ∧ F ∩ F' = {p}) ∨
      (∃ x y : ℂ, IsFaceEdge F x y ∧ IsFaceEdge F' x y ∧ F ∩ F' = segment ℝ x y)) := by
  choose! o r hor using hD.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT
    refine ⟨ext_face hD hor hT, fun T' hT' => hull_sub_face_iff hD hor hT hT', ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨T', hT', hc, hx⟩ := hx
      exact (hull_sub_face_iff hD hor hT hT').2 hc hx
    · intro x hx
      obtain ⟨T', hT', hc, hx'⟩ := cover_face hD hor hT hx
      simp only [Set.mem_iUnion]
      exact ⟨T', hT', hc, hx'⟩
  · apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨T, hT, hx⟩ := hx
      exact convexHull_mono Set.inter_subset_left hx
    · rw [← hD.2.1]
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨T, hT, hx⟩ := hx
      exact ⟨T, hT, hull_sub_own_face hD hor hT hx⟩
  · rintro F ⟨T, hT, rfl⟩ x y hxy
    exact face_edge hD hor hT hxy
  · rintro F F' ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩ hne
    exact face_inter hD hor hT hT' hne
