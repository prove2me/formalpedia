-- Prove2me | solution 2 for ConeLifts.Factorization.factorization_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T13:58:42.998362+00:00
-- url     : https://prove2.me/submissions/3ac9e20e-48d6-4533-9a12-1e7145b0b63e

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Factorization_HasLift
import Definitions.Def_ConeLifts_Factorization_HasProperLift
import Definitions.Def_ConeLifts_Factorization_SlackFactorizable
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Shared_dualCone
import Theorems.Thm_ConeLifts_Factorization_extremePoint_polar_isGreatest
import Theorems.Thm_ConeLifts_Factorization_mem_of_liftSpace

-- carved verbatim out of submission c2988123-48d8-40e6-b580-efccba79babc, lines 863-869

section
open scoped InnerProductSpace
open ConeLifts
open ConeLifts.Factorization

theorem aux_ft_dual_sep {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (p : EuclideanSpace ℝ (Fin m)) (hp : p ∉ K) :
    ∃ k ∈ ConeLifts.Shared.dualCone K, ⟪p, k⟫_ℝ < 0 := by
  obtain ⟨g, μ, hgK, hgp⟩ := geometric_hahn_banach_closed_point hK.2.1 hK.1 hp
  have hμ : 0 < μ := by simpa using hgK 0 hK.2.2.1
  have hg0 : ∀ x ∈ K, g x ≤ 0 := by
    intro x hx
    by_contra hpos
    push_neg at hpos
    have h := hgK ((2 * μ / g x) • x) (hK.2.2.2 _ (by positivity) x hx)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at h
    linarith
  refine ⟨-(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm g, ?_, ?_⟩
  · intro x hx
    rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    linarith [hg0 x hx]
  · rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    linarith

theorem aux_ft_strong {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (w₀ : EuclideanSpace ℝ (Fin m)) (hw₀L : w₀ ∈ L) (hw₀K : w₀ ∈ interior K)
    (a : EuclideanSpace ℝ (Fin m))
    (h1 : ∀ w ∈ K, w ∈ L → ⟪a, w⟫_ℝ ≤ 1) :
    ∃ z ∈ L.directionᗮ, z - a ∈ ConeLifts.Shared.dualCone K ∧ ⟪w₀, z⟫_ℝ ≤ 1 := by
  set D := L.direction with hD
  set γ := 1 - ⟪a, w₀⟫_ℝ with hγ
  have hγ0 : 0 ≤ γ := by have := h1 w₀ (interior_subset hw₀K) hw₀L; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w₀ hw₀K
  have hbK : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ < ε → w₀ + v ∈ K := by
    intro v hv
    apply interior_subset; apply hball
    rw [Metric.mem_ball, dist_eq_norm]; simpa using hv
  have hkb : ∀ k ∈ ConeLifts.Shared.dualCone K, ε / 2 * ‖k‖ ≤ ⟪w₀, k⟫_ℝ := by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    have hkn : 0 < ‖k‖ := norm_pos_iff.mpr hk0
    have hmem := hbK (-(ε / 2 / ‖k‖) • k) (by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hkn.ne']
      linarith)
    have h := hk _ hmem
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    have : ε / 2 / ‖k‖ * ‖k‖ ^ 2 = ε / 2 * ‖k‖ := by field_simp
    nlinarith
  by_contra hno
  push_neg at hno
  set B : Set (EuclideanSpace ℝ (Fin m)) :=
    {k | k ∈ ConeLifts.Shared.dualCone K ∧ ⟪w₀, k⟫_ℝ ≤ γ} with hBdef
  set T : Set (EuclideanSpace ℝ (Fin m)) := {x | x + a ∈ Dᗮ} with hTdef
  have hdualclosed : IsClosed (ConeLifts.Shared.dualCone K) := by
    have : ConeLifts.Shared.dualCone K = ⋂ x ∈ K, {y | 0 ≤ ⟪x, y⟫_ℝ} := by
      ext y; simp [ConeLifts.Shared.dualCone]
    rw [this]
    exact isClosed_biInter fun x _ =>
      isClosed_le continuous_const (continuous_const.inner continuous_id)
  have hdualconv : Convex ℝ (ConeLifts.Shared.dualCone K) := by
    intro y hy z hz s t hs ht hst x hx
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have := hy x hx; have := hz x hx
    positivity
  have hBconv : Convex ℝ B := by
    intro y hy z hz s t hs ht hst
    refine ⟨hdualconv hy.1 hz.1 hs ht hst, ?_⟩
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith [hy.2, hz.2]
  have hBcomp : IsCompact B := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have hB' : B = ConeLifts.Shared.dualCone K ∩ {k | ⟪w₀, k⟫_ℝ ≤ γ} := rfl
      rw [hB']
      exact hdualclosed.inter (isClosed_le (continuous_const.inner continuous_id) continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨2 * γ / ε, fun k hk => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hε]
      have := hkb k hk.1
      linarith [hk.2]
  have hTconv : Convex ℝ T := by
    intro y hy z hz s t hs ht hst
    simp only [hTdef, Set.mem_setOf_eq] at hy hz ⊢
    have : s • y + t • z + a = s • (y + a) + t • (z + a) := by
      calc s • y + t • z + a = s • y + t • z + (s + t) • a := by rw [hst, one_smul]
        _ = s • (y + a) + t • (z + a) := by rw [add_smul, smul_add, smul_add]; abel
    rw [this]
    exact Dᗮ.add_mem (Dᗮ.smul_mem _ hy) (Dᗮ.smul_mem _ hz)
  have hTclosed : IsClosed T :=
    (Submodule.isClosed_orthogonal D).preimage (continuous_id.add continuous_const)
  have hdisj : Disjoint B T := by
    rw [Set.disjoint_left]
    intro k hkB hkT
    have h := hno (k + a) hkT (by simpa using hkB.1)
    rw [inner_add_right] at h
    have := real_inner_comm a w₀
    linarith [hkB.2]
  obtain ⟨f, u, v, hfB, huv, hfT⟩ :=
    geometric_hahn_banach_compact_closed hBconv hBcomp hTconv hTclosed hdisj
  have h0B : (0 : EuclideanSpace ℝ (Fin m)) ∈ B :=
    ⟨fun x _ => by simp, by simp [hγ0]⟩
  have hu : 0 < u := by simpa using hfB 0 h0B
  have haT : -a ∈ T := by simp [hTdef]
  have hfa := hfT (-a) haT
  have hfD : ∀ d ∈ Dᗮ, f d = 0 := by
    intro d hd
    by_contra hne
    have hmem : -a + ((v - f (-a)) / f d) • d ∈ T := by
      simp only [hTdef, Set.mem_setOf_eq]
      rw [show -a + ((v - f (-a)) / f d) • d + a = ((v - f (-a)) / f d) • d by abel]
      exact Dᗮ.smul_mem _ hd
    have := hfT _ hmem
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  set w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm f with hwdef
  have hfw : ∀ x, f x = ⟪w, x⟫_ℝ := fun x => by
    rw [hwdef, InnerProductSpace.toDual_symm_apply]
  have hwD : w ∈ D := by
    rw [← Submodule.orthogonal_orthogonal D, Submodule.mem_orthogonal]
    intro d hd
    rw [real_inner_comm, ← hfw]; exact hfD d hd
  have hwa : u < -⟪w, a⟫_ℝ := by
    have := hfa; rw [hfw, inner_neg_right] at this; linarith
  have hLmem : ∀ s : ℝ, w₀ + s • w ∈ L := by
    intro s
    have := AffineSubspace.vadd_mem_of_mem_direction (D.smul_mem s hwD) hw₀L
    rw [vadd_eq_add, add_comm] at this
    exact this
  rcases hγ0.lt_or_eq with hγpos | hγz
  · set t := u / γ with htdef
    have htpos : 0 < t := by positivity
    have hpK : t • w₀ - w ∈ K := by
      by_contra hpK
      obtain ⟨k, hk, hpk⟩ := aux_ft_dual_sep K hK _ hpK
      have hq : 0 ≤ ⟪w₀, k⟫_ℝ := hk w₀ (interior_subset hw₀K)
      rw [inner_sub_left, real_inner_smul_left] at hpk
      rcases hq.lt_or_eq with hqpos | hqz
      · have hmem : (γ / ⟪w₀, k⟫_ℝ) • k ∈ B := by
          refine ⟨fun x hx => ?_, ?_⟩
          · rw [real_inner_smul_right]; exact mul_nonneg (by positivity) (hk x hx)
          · rw [real_inner_smul_right, div_mul_cancel₀ _ hqpos.ne']
        have := hfB _ hmem
        rw [hfw, real_inner_smul_right] at this
        have h2 : ⟪w, k⟫_ℝ < t * ⟪w₀, k⟫_ℝ := by
          rw [htdef, div_mul_eq_mul_div, lt_div_iff₀ hγpos]
          rw [div_mul_eq_mul_div, div_lt_iff₀ hqpos] at this
          linarith
        linarith
      · have hwk : ⟪w, k⟫_ℝ ≤ 0 := by
          by_contra hpos
          push_neg at hpos
          have hmem : (u / ⟪w, k⟫_ℝ) • k ∈ B := by
            refine ⟨fun x hx => ?_, ?_⟩
            · rw [real_inner_smul_right]; exact mul_nonneg (by positivity) (hk x hx)
            · rw [real_inner_smul_right, ← hqz, mul_zero]; exact hγ0
          have := hfB _ hmem
          rw [hfw, real_inner_smul_right, div_mul_cancel₀ _ hpos.ne'] at this
          linarith
        rw [← hqz] at hpk
        linarith
    have hq : (1 / t) • (t • w₀ - w) = w₀ + (-(1 / t)) • w := by
      rw [smul_sub, smul_smul, one_div_mul_cancel htpos.ne', one_smul, neg_smul, sub_eq_add_neg]
    have hmK := hK.2.2.2 (1 / t) (by positivity) _ hpK
    rw [hq] at hmK
    have := h1 _ hmK (hLmem _)
    rw [inner_add_right, real_inner_smul_right, ← real_inner_comm a w] at this
    have h3 : -(1 / t) * ⟪w, a⟫_ℝ ≤ γ := by linarith
    have h4 : -⟪w, a⟫_ℝ ≤ γ * t := by
      have e : t * (-(1 / t) * ⟪w, a⟫_ℝ) = -⟪w, a⟫_ℝ := by field_simp
      have := mul_le_mul_of_nonneg_left h3 htpos.le
      linarith
    rw [htdef, mul_div_cancel₀ _ hγpos.ne'] at h4
    linarith
  · have hs : 0 < ε / 2 / (‖w‖ + 1) := by positivity
    have hmK : w₀ + (-(ε / 2 / (‖w‖ + 1))) • w ∈ K := by
      apply hbK
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs]
      have : ε / 2 / (‖w‖ + 1) * ‖w‖ ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg w]
      linarith
    have := h1 _ hmK (hLmem _)
    rw [inner_add_right, real_inner_smul_right, ← real_inner_comm a w] at this
    have h5 : 0 ≤ ⟪w, a⟫_ℝ := by
      have : -(ε / 2 / (‖w‖ + 1)) * ⟪w, a⟫_ℝ ≤ 0 := by linarith
      nlinarith
    linarith

end

section
open scoped InnerProductSpace
open ConeLifts
open ConeLifts.Factorization
open scoped InnerProductSpace Pointwise
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem aux_cxe_relint {K : Set E} {y v : E} (hy : y ∈ K)
    (hyi : y ∈ interior (K + ((vectorSpan ℝ K)ᗮ : Set E))) (hv : v ∈ vectorSpan ℝ K) :
    ∃ ε > (0:ℝ), y + ε • v ∈ K := by
  set W := vectorSpan ℝ K with hWdef
  have hc : Continuous fun t : ℝ => y + t • v := by fun_prop
  have hev : ∀ᶠ t in nhds (0:ℝ), y + t • v ∈ interior (K + (Wᗮ : Set E)) := by
    have h := hc.tendsto 0
    simp only [zero_smul, add_zero] at h
    exact h (isOpen_interior.mem_nhds hyi)
  obtain ⟨t, ht, htpos⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Ioi 0))).exists
  refine ⟨t, htpos, ?_⟩
  obtain ⟨k, hk, w, hw, hkw⟩ := Set.mem_add.mp (interior_subset ht)
  have hwW : w ∈ W := by
    have h1 : y - k ∈ W := by
      have := vsub_mem_vectorSpan ℝ hy hk
      simpa [vsub_eq_sub] using this
    have h2 : w = (y - k) + t • v := by
      calc w = (k + w) - k := by abel
        _ = (y - k) + t • v := by rw [hkw]; abel
    rw [h2]
    exact W.add_mem h1 (W.smul_mem t hv)
  have hw0 : w = 0 := by
    have := Submodule.inner_right_of_mem_orthogonal hwW hw
    exact inner_self_eq_zero.mp this
  rw [← hkw, hw0, add_zero]
  exact hk

theorem aux_cxe_face {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {z : E} (hz : z ∈ K)
    (hzi : z ∉ interior (K + ((vectorSpan ℝ K)ᗮ : Set E))) :
    ∃ F : Set E, IsExtreme ℝ K F ∧ IsCompact F ∧ Convex ℝ F ∧ z ∈ F ∧
      finrank ℝ (vectorSpan ℝ F) < finrank ℝ (vectorSpan ℝ K) := by
  set W := vectorSpan ℝ K with hWdef
  set S := K + (Wᗮ : Set E) with hSdef
  have hSc : Convex ℝ S := hKc.add (Wᗮ).convex
  have hsub : K ⊆ S := fun k hk => Set.mem_add.mpr ⟨k, hk, 0, Wᗮ.zero_mem, add_zero k⟩
  have hSspan : affineSpan ℝ S = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E ⟨z, hsub hz⟩]
    rw [eq_top_iff, ← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := W)]
    refine sup_le (vectorSpan_mono ℝ hsub) ?_
    intro w hw
    have h1 : z + w ∈ S := Set.add_mem_add hz hw
    have h2 : z ∈ S := hsub hz
    have := vsub_mem_vectorSpan ℝ h1 h2
    simpa [vsub_eq_sub] using this
  have hSint : (interior S).Nonempty := (hSc.interior_nonempty_iff_affineSpan_eq_top).mpr hSspan
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hSc.interior isOpen_interior hzi
  have hfS : ∀ y ∈ S, f y ≤ f z := by
    have : closure (interior S) ⊆ {y | f y ≤ f z} :=
      closure_minimal (fun y hy => (hf y hy).le) (isClosed_le f.continuous continuous_const)
    rw [hSc.closure_interior_eq_closure_of_nonempty_interior hSint] at this
    exact fun y hy => this (subset_closure hy)
  have hfW : ∀ w ∈ Wᗮ, f w = 0 := by
    intro w hw
    have h := hfS (z + f w • w) (Set.add_mem_add hz (Wᗮ.smul_mem _ hw))
    rw [map_add, map_smul, smul_eq_mul] at h
    nlinarith [mul_self_nonneg (f w)]
  obtain ⟨y0, hy0⟩ := hSint
  obtain ⟨k0, hk0, w0, hw0, hkw0⟩ := Set.mem_add.mp (interior_subset hy0)
  have hk0lt : f k0 < f z := by
    have := hf y0 hy0
    rw [← hkw0, map_add, hfW w0 hw0, add_zero] at this
    exact this
  have hexp : IsExposed ℝ K (f.toExposed K) := ContinuousLinearMap.toExposed.isExposed
  refine ⟨f.toExposed K, hexp.isExtreme, hexp.isCompact hK, hexp.convex hKc,
    ⟨hz, fun y hy => hfS y (hsub hy)⟩, ?_⟩
  apply Submodule.finrank_lt_finrank_of_lt
  have hle : vectorSpan ℝ (f.toExposed K) ≤ W := vectorSpan_mono ℝ (fun y hy => hy.1)
  have hker : vectorSpan ℝ (f.toExposed K) ≤ LinearMap.ker (f : E →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub,
      map_sub]
    have h1 := ha.2 b hb.1
    have h2 := hb.2 a ha.1
    linarith
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hmem : k0 - z ∈ W := by simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hk0 hz
  rw [← heq] at hmem
  have := hker hmem
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub] at this
  linarith

theorem aux_cxe_main : ∀ (d : ℕ) (K : Set E), finrank ℝ (vectorSpan ℝ K) = d → IsCompact K →
    Convex ℝ K → K ⊆ convexHull ℝ (K.extremePoints ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K hd hK hKc x hx
  set W := vectorSpan ℝ K with hWdef
  have hfr : ∀ z ∈ K, z ∉ interior (K + (Wᗮ : Set E)) →
      z ∈ convexHull ℝ (K.extremePoints ℝ) := by
    intro z hz hzi
    obtain ⟨F, hFe, hFc, hFcv, hzF, hFd⟩ := aux_cxe_face hK hKc hz hzi
    have := ih _ (lt_of_lt_of_eq hFd hd) F rfl hFc hFcv hzF
    exact convexHull_mono hFe.extremePoints_subset_extremePoints this
  by_cases hxi : x ∈ interior (K + (Wᗮ : Set E))
  swap
  · exact hfr x hx hxi
  obtain ⟨e, he⟩ := hK.extremePoints_nonempty ⟨x, hx⟩
  have heK : e ∈ K := he.1
  by_cases hxe : x = e
  · exact subset_convexHull ℝ _ (hxe ▸ he)
  set v := x - e with hv
  have hvW : v ∈ W := by simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hx heK
  have hvne : v ≠ 0 := sub_ne_zero.mpr hxe
  set T := {t : ℝ | 0 ≤ t ∧ e + t • v ∈ K} with hT
  have h1T : (1:ℝ) ∈ T := ⟨zero_le_one, by simpa [hv] using hx⟩
  have hTclosed : IsClosed T := by
    apply IsClosed.inter (isClosed_le continuous_const continuous_id)
    exact hK.isClosed.preimage (by fun_prop)
  obtain ⟨R, hR⟩ : ∃ R, ∀ k ∈ K, dist k e ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall e).mp hK.isBounded
    exact ⟨R, fun k hk => hR hk⟩
  have hTbdd : BddAbove T := by
    refine ⟨R / ‖v‖, fun t ht => ?_⟩
    have := hR _ ht.2
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at this
    rw [le_div_iff₀ (norm_pos_iff.mpr hvne)]
    exact this
  have ht1 := hTclosed.csSup_mem ⟨1, h1T⟩ hTbdd
  set t1 := sSup T with ht1def
  have ht1ge : 1 ≤ t1 := le_csSup hTbdd h1T
  have hyK : e + t1 • v ∈ K := ht1.2
  have hyi : e + t1 • v ∉ interior (K + (Wᗮ : Set E)) := by
    intro hyi
    obtain ⟨ε, hε, hεK⟩ := aux_cxe_relint hyK hyi hvW
    have hmem : t1 + ε ∈ T := ⟨by linarith, by rw [add_smul, ← add_assoc]; exact hεK⟩
    have := le_csSup hTbdd hmem
    linarith
  have hy := hfr _ hyK hyi
  have he' : e ∈ convexHull ℝ (K.extremePoints ℝ) := subset_convexHull ℝ _ he
  have ht1pos : 0 < t1 := by linarith
  have hcomb : (1 - 1/t1) • e + (1/t1) • (e + t1 • v) = x := by
    rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ ht1pos.ne', one_smul, hv]
    module
  rw [← hcomb]
  refine convex_convexHull ℝ _ he' hy ?_ ?_ ?_
  · rw [sub_nonneg, div_le_one ht1pos]; exact ht1ge
  · positivity
  · ring

theorem aux_cxe_eq {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) :
    K = convexHull ℝ (K.extremePoints ℝ) :=
  Subset.antisymm (aux_cxe_main _ K rfl hK hKc) (convexHull_min extremePoints_subset hKc)

end

section
open scoped InnerProductSpace
open ConeLifts
open ConeLifts.Factorization

lemma aux_eul_polar_convex {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (ConeLifts.Shared.polar C) := by
  intro y1 hy1 y2 hy2 a b ha hb hab x hx
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := hy1 x hx
  have h2 := hy2 x hx
  nlinarith

lemma aux_eul_polar_closed {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (ConeLifts.Shared.polar C) := by
  have : ConeLifts.Shared.polar C = ⋂ x ∈ C, {y | ⟪x, y⟫_ℝ ≤ 1} := by
    ext y; simp [ConeLifts.Shared.polar]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma aux_eul_polar_bounded {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C) :
    Bornology.IsBounded (ConeLifts.Shared.polar C) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hC)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 / δ, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hy0 : y = 0
  · simp [hy0]; positivity
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hx : (δ / 2 / ‖y‖) • y ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hyn.ne']
    linarith
  have := hy _ hx
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at this
  have h2 : δ / 2 / ‖y‖ * ‖y‖ ^ 2 = δ / 2 * ‖y‖ := by
    field_simp
  rw [h2] at this
  rw [le_div_iff₀ hδ]
  nlinarith

theorem aux_eul_main {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (w : EuclideanSpace ℝ (Fin n))
    (hw : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ⟪w, y⟫_ℝ = 0) :
    w = 0 := by
  set P := ConeLifts.Shared.polar C
  have hPc : IsCompact P := Metric.isCompact_of_isClosed_isBounded
    (aux_eul_polar_closed C) (aux_eul_polar_bounded C hC.2.2)
  have hPconv : Convex ℝ P := aux_eul_polar_convex C
  let H : Set (EuclideanSpace ℝ (Fin n)) := {y | ⟪w, y⟫_ℝ = 0}
  have hHc : IsClosed H := isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hHconv : Convex ℝ H := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    simp only [H, Set.mem_setOf_eq] at hy1 hy2 ⊢
    rw [inner_add_right, inner_smul_right, inner_smul_right, hy1, hy2]
    ring
  have hPH : P ⊆ H := by
    rw [← closure_convexHull_extremePoints hPc hPconv]
    exact closure_minimal (convexHull_min (fun y hy => hw y hy) hHconv) hHc
  obtain ⟨R, hR⟩ := hC.1.isBounded.exists_norm_le
  set R' := max R 0 + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  set ε := 1 / (R' * (‖w‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεw : ε • w ∈ P := by
    intro x hx
    rw [real_inner_smul_right]
    have h1 : ⟪x, w⟫_ℝ ≤ ‖x‖ * ‖w‖ := real_inner_le_norm x w
    have h2 : ‖x‖ ≤ R' := by
      have := hR x hx
      have := le_max_left R 0
      linarith
    have h3 : ⟪x, w⟫_ℝ ≤ R' * (‖w‖ + 1) := by
      calc ⟪x, w⟫_ℝ ≤ ‖x‖ * ‖w‖ := h1
        _ ≤ R' * ‖w‖ := by gcongr
        _ ≤ R' * (‖w‖ + 1) := by nlinarith
    have h4 : ε * (R' * (‖w‖ + 1)) = 1 := by
      rw [hε]; field_simp
    nlinarith
  have := hPH hεw
  simp only [H, Set.mem_setOf_eq, real_inner_smul_right] at this
  have h5 : ⟪w, w⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hεpos.ne'
    · exact h
  exact inner_self_eq_zero.mp h5

theorem aux_ft_const {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (h : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ⟪x, y⟫_ℝ = t) : x = 0 := by
  have hPc : IsCompact (ConeLifts.Shared.polar C) := Metric.isCompact_of_isClosed_isBounded
    (aux_eul_polar_closed C) (aux_eul_polar_bounded C hC.2.2)
  have hPH : ConeLifts.Shared.polar C ⊆ {y | ⟪x, y⟫_ℝ = t} := by
    rw [← closure_convexHull_extremePoints hPc (aux_eul_polar_convex C)]
    refine closure_minimal (convexHull_min (fun y hy => h y hy) ?_)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    intro y1 hy1 y2 hy2 a b ha hb hab
    simp only [Set.mem_setOf_eq] at hy1 hy2 ⊢
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hy1, hy2, ← add_mul, hab,
      one_mul]
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ ConeLifts.Shared.polar C := fun z _ => by simp
  have ht : t = 0 := by
    have := hPH h0
    simp only [Set.mem_setOf_eq, inner_zero_right] at this
    linarith
  exact aux_eul_main C hC x (fun y hy => (h y hy).trans ht)

theorem aux_ft_forward {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (h : HasProperLift K C) : SlackFactorizable K C := by
  obtain ⟨L, π, hCπ, w₀, hw₀K, hw₀L⟩ := h
  have hZ : ∀ y : EuclideanSpace ℝ (Fin n), ∃ z : EuclideanSpace ℝ (Fin m),
      y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C) →
        (z ∈ L.directionᗮ ∧ z - LinearMap.adjoint π y ∈ ConeLifts.Shared.dualCone K ∧
          ⟪w₀, z⟫_ℝ = 1) := by
    intro y
    by_cases hy : y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    have h1 : ∀ w ∈ K, w ∈ L → ⟪LinearMap.adjoint π y, w⟫_ℝ ≤ 1 := by
      intro w hwK hwL
      rw [LinearMap.adjoint_inner_left, real_inner_comm]
      exact hy.1 (π w) (hCπ ▸ ⟨w, ⟨hwK, hwL⟩, rfl⟩)
    obtain ⟨z, hzD, hzK, hz1⟩ := aux_ft_strong K hK L w₀ hw₀L hw₀K _ h1
    refine ⟨z, fun _ => ⟨hzD, hzK, le_antisymm hz1 ?_⟩⟩
    obtain ⟨⟨x, hxC, hx1⟩, _⟩ := ConeLifts.Factorization.extremePoint_polar_isGreatest hn C hC y hy
    rw [hCπ] at hxC
    obtain ⟨w, ⟨hwK, hwL⟩, rfl⟩ := hxC
    have hd : w - w₀ ∈ L.direction := AffineSubspace.vsub_mem_direction hwL hw₀L
    have h0 := Submodule.inner_right_of_mem_orthogonal hd hzD
    rw [inner_sub_left] at h0
    have h2 := hzK w hwK
    rw [inner_sub_right] at h2
    have e1 : ⟪w, LinearMap.adjoint π y⟫_ℝ = ⟪y, π w⟫_ℝ := by
      rw [real_inner_comm, LinearMap.adjoint_inner_left]
    simp only at hx1
    linarith
  choose Z hZ using hZ
  have hW : ∀ x : EuclideanSpace ℝ (Fin n), ∃ w : EuclideanSpace ℝ (Fin m),
      x ∈ C → (w ∈ K ∧ w ∈ L ∧ π w = x) := by
    intro x
    by_cases hx : x ∈ C
    · rw [hCπ] at hx
      obtain ⟨w, ⟨h1, h2⟩, h3⟩ := hx
      exact ⟨w, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose W hW using hW
  refine ⟨W, fun y => Z y - LinearMap.adjoint π y, fun x hx => (hW x hx.1).1,
    fun y hy => (hZ y hy).2.1, ?_⟩
  intro x hx y hy
  obtain ⟨hwK, hwL, hwx⟩ := hW x hx.1
  obtain ⟨hzD, -, hz1⟩ := hZ y hy
  have hd : W x - w₀ ∈ L.direction := AffineSubspace.vsub_mem_direction hwL hw₀L
  have h0 := Submodule.inner_right_of_mem_orthogonal hd hzD
  rw [inner_sub_left] at h0
  have e1 : ⟪W x, LinearMap.adjoint π y⟫_ℝ = ⟪y, π (W x)⟫_ℝ := by
    rw [real_inner_comm, LinearMap.adjoint_inner_left]
  rw [hwx] at e1
  rw [inner_sub_right, e1]
  have := real_inner_comm x y
  linarith

theorem aux_ft_converse {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (h : SlackFactorizable K C) : HasLift K C := by
  obtain ⟨A, B, hA, hB, hAB⟩ := h
  let g : Submodule ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    { carrier := {p | ∃ t : ℝ, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
        t - ⟪p.2, y⟫_ℝ = ⟪p.1, B y⟫_ℝ}
      add_mem' := by
        rintro p q ⟨t1, h1⟩ ⟨t2, h2⟩
        refine ⟨t1 + t2, fun y hy => ?_⟩
        simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
        linarith [h1 y hy, h2 y hy]
      zero_mem' := ⟨0, fun y _ => by simp⟩
      smul_mem' := by
        rintro c p ⟨t, h⟩
        refine ⟨c * t, fun y hy => ?_⟩
        simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_left]
        linear_combination c * (h y hy) }
  have hg : ∀ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (_hx : x ∈ g)
      (_hx' : x.fst = 0), x.snd = 0 := by
    rintro ⟨z, x⟩ ⟨t, ht⟩ hz
    simp only at hz ⊢
    apply aux_ft_const C hC x t
    intro y hy
    have := ht y hy
    simp only [hz, inner_zero_left] at this
    linarith
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend g.toLinearPMap.toFun
  have key : ∀ z x, (z, x) ∈ g → π z = x := by
    intro z x hzx
    rw [← Submodule.toLinearPMap_graph_eq g hg, LinearPMap.mem_graph_iff] at hzx
    obtain ⟨d, hd1, hd2⟩ := hzx
    simp only at hd1 hd2
    rw [← hd1, ← hd2]
    exact LinearMap.congr_fun hπ d
  let L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)) :=
    { carrier := {z | ∃ x : EuclideanSpace ℝ (Fin n),
        ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), 1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ}
      smul_vsub_vadd_mem' := by
        rintro c p1 p2 p3 ⟨x1, h1⟩ ⟨x2, h2⟩ ⟨x3, h3⟩
        refine ⟨c • (x1 - x2) + x3, fun y hy => ?_⟩
        simp only [vsub_eq_sub, vadd_eq_add, inner_add_left, inner_sub_left,
          real_inner_smul_left]
        linear_combination c * (h1 y hy) - c * (h2 y hy) + h3 y hy }
  have hLg : ∀ z x, (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      1 - ⟪x, y⟫_ℝ = ⟪z, B y⟫_ℝ) → π z = x := fun z x h => key z x ⟨1, h⟩
  refine ⟨L, π, Set.Subset.antisymm ?_ ?_⟩
  · refine (aux_cxe_eq hC.1 hC.2.1).subset.trans (convexHull_min ?_ ?_)
    · intro x hx
      exact ⟨A x, ⟨hA x hx, ⟨x, fun y hy => hAB x hx y hy⟩⟩, hLg _ _ (fun y hy => hAB x hx y hy)⟩
    · exact (hK.2.1.inter L.convex).linear_image π
  · rintro _ ⟨w, ⟨hwK, x, hx⟩, rfl⟩
    rw [hLg w x hx]
    exact ConeLifts.Factorization.mem_of_liftSpace C hC K hK hKint B hB x w hwK hx

theorem factorization_core {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty) :
    (HasProperLift K C → SlackFactorizable K C) ∧ (SlackFactorizable K C → HasLift K C) :=
  ⟨aux_ft_forward hn C hC K hK, aux_ft_converse C hC K hK hKint⟩

end

section
open scoped InnerProductSpace
open ConeLifts.Factorization

theorem solution {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty) :
    (HasProperLift K C → SlackFactorizable K C) ∧ (SlackFactorizable K C → HasLift K C) := by
  exact factorization_core hn C hC K hK hKint

end
