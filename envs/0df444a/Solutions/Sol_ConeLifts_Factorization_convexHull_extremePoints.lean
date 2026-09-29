-- Prove2me | solution 1 for ConeLifts.Factorization.convexHull_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:42:08.876197+00:00
-- url     : https://prove2.me/submissions/c6134854-1e77-4483-838d-4170ac66edd5

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar

namespace ConeLifts.Factorization

open scoped InnerProductSpace Pointwise
open Module Set

section aux_cxe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A point of `K` interior to the thickening `K + (vectorSpan K)ᗮ` can be moved a little in any
direction of `vectorSpan K` while staying in `K`. -/
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

/-- A point of `K` on the boundary of the thickening lies in a proper exposed face. -/
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

/-- Minkowski's theorem, by strong induction on the dimension of the vector span. -/
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

end aux_cxe

theorem aux_cxe_polar_convex {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (ConeLifts.Shared.polar C) := by
  intro y hy z hz a b ha hb hab
  simp only [ConeLifts.Shared.polar, Set.mem_ofPred_eq] at hy hz ⊢
  intro x hx
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := hy x hx
  have h2 := hz x hx
  nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h2)]

theorem aux_cxe_polar_compact {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C) :
    IsCompact (ConeLifts.Shared.polar C) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0
  apply Metric.isCompact_of_isClosed_isBounded
  · have : ConeLifts.Shared.polar C = ⋂ x ∈ C, {y | ⟪x, y⟫_ℝ ≤ 1} := by
      ext y; simp [ConeLifts.Shared.polar]
    rw [this]
    exact isClosed_biInter fun x _ =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2 / r, fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hy0 : y = 0
    · rw [hy0, norm_zero]; positivity
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hx : (r / (2 * ‖y‖)) • y ∈ C := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
      have : r / (2 * ‖y‖) * ‖y‖ = r / 2 := by field_simp
      rw [this]; linarith
    have h := hy _ hx
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    have h' : r / (2 * ‖y‖) * ‖y‖ ^ 2 = r * ‖y‖ / 2 := by field_simp
    rw [h'] at h
    rw [le_div_iff₀ hr]
    linarith

end ConeLifts.Factorization

open ConeLifts.Factorization

theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsConvexBody C) :
    C = convexHull ℝ (Set.extremePoints ℝ C) ∧
      ConeLifts.Shared.polar C = convexHull ℝ (Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :=
  ⟨aux_cxe_eq hC.1 hC.2.1, aux_cxe_eq (aux_cxe_polar_compact C hC.2.2) (aux_cxe_polar_convex C)⟩
