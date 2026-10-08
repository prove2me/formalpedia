-- Prove2me | solution 1 for ConeLifts.NonnegRank.booleanFactorization_iff_faceEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:41:13.963264+00:00
-- url     : https://prove2.me/submissions/40330f96-e7ec-4163-bc78-3995621d174c

import Mathlib
import Definitions.Def_ConeLifts_NonnegRank_IsPolytope
import Definitions.Def_ConeLifts_NonnegRank_Face
import Definitions.Def_ConeLifts_NonnegRank_HasBooleanFactorization
import Definitions.Def_ConeLifts_NonnegRank_nonnegRank

open scoped InnerProductSpace Pointwise

namespace ConeLifts.NonnegRank

open Module Set

section aux_nrk

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem aux_nrk_relint {K : Set E} {y v : E} (hy : y ∈ K)
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

theorem aux_nrk_face {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) {z : E} (hz : z ∈ K)
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

theorem aux_nrk_main : ∀ (d : ℕ) (K : Set E), finrank ℝ (vectorSpan ℝ K) = d → IsCompact K →
    Convex ℝ K → K ⊆ convexHull ℝ (K.extremePoints ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K hd hK hKc x hx
  set W := vectorSpan ℝ K with hWdef
  have hfr : ∀ z ∈ K, z ∉ interior (K + (Wᗮ : Set E)) →
      z ∈ convexHull ℝ (K.extremePoints ℝ) := by
    intro z hz hzi
    obtain ⟨F, hFe, hFc, hFcv, hzF, hFd⟩ := aux_nrk_face hK hKc hz hzi
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
    obtain ⟨ε, hε, hεK⟩ := aux_nrk_relint hyK hyi hvW
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

theorem aux_nrk_eq {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) :
    K ⊆ convexHull ℝ (K.extremePoints ℝ) :=
  aux_nrk_main _ K rfl hK hKc

end aux_nrk

theorem aux_nrk_polar_compact {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
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

/-- Separation: a point `v ∈ C \ F` of a polytope is separated from an exposed face `F` by an
extreme point of the polar. -/
theorem aux_nrk_sep {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsPolytope C)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : IsExposed ℝ C F)
    (v : EuclideanSpace ℝ (Fin n)) (hvC : v ∈ C) (hvF : v ∉ F) :
    ∃ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      (∀ x ∈ F, ⟪x, y⟫_ℝ = 1) ∧ ⟪v, y⟫_ℝ < 1 := by
  set P := ConeLifts.Shared.polar C with hP
  -- a point y0 of the polar with the desired property
  obtain ⟨y0, hy0P, hy0F, hy0v⟩ : ∃ y0 ∈ P, (∀ x ∈ F, ⟪x, y0⟫_ℝ = 1) ∧ ⟪v, y0⟫_ℝ < 1 := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · refine ⟨0, fun x _ => by simp, fun x hx => by simp [hFe] at hx, by simp⟩
    obtain ⟨l, hl⟩ := hF hFne
    obtain ⟨x0, hx0⟩ := hFne
    have hx0' := hx0
    rw [hl] at hx0'
    set M := l x0 with hM
    have hlv : l v < M := by
      rcases lt_or_eq_of_le (hx0'.2 v hvC) with h | h
      · exact h
      · exfalso; apply hvF; rw [hl]; refine ⟨hvC, fun z hz => ?_⟩; rw [h]; exact hx0'.2 z hz
    set u := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm l with hu
    have hlu : ∀ z, l z = ⟪z, u⟫_ℝ := by
      intro z; rw [real_inner_comm, hu, InnerProductSpace.toDual_symm_apply]
    have hMpos : 0 < M := by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hC.2
      have hune : u ≠ 0 := by
        intro h0
        have h1 := hlu v
        have h2 := hlu x0
        rw [h0, inner_zero_right] at h1 h2
        rw [hM] at hlv
        linarith
      have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hune
      have hx : (r / (2 * ‖u‖)) • u ∈ C := by
        apply interior_subset
        apply hball
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
        have : r / (2 * ‖u‖) * ‖u‖ = r / 2 := by field_simp
        rw [this]; linarith
      have h := hx0'.2 _ hx
      rw [hlu, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
      have : 0 < r / (2 * ‖u‖) * ‖u‖ ^ 2 := by positivity
      linarith
    refine ⟨M⁻¹ • u, ?_, ?_, ?_⟩
    · intro z hz
      rw [real_inner_smul_right, ← hlu]
      have := hx0'.2 z hz
      rw [inv_mul_le_one₀ hMpos]; exact this
    · intro x hx
      rw [hl] at hx
      rw [real_inner_smul_right, ← hlu]
      have h1 := hx.2 x0 hx0'.1
      have h2 := hx0'.2 x hx.1
      rw [show l x = M by linarith]
      exact inv_mul_cancel₀ hMpos.ne'
    · rw [real_inner_smul_right, ← hlu, inv_mul_lt_one₀ hMpos]; exact hlv
  -- the face G of the polar
  set G := {y ∈ P | ∀ x ∈ F, ⟪x, y⟫_ℝ = 1} with hG
  have hPc : IsCompact P := aux_nrk_polar_compact C hC.2
  have hFC : F ⊆ C := hF.subset
  have hGc : IsCompact G := by
    apply hPc.of_isClosed_subset _ (fun y hy => hy.1)
    have : G = P ∩ ⋂ x ∈ F, {y | ⟪x, y⟫_ℝ = 1} := by ext y; simp [hG]
    rw [this]
    exact hPc.isClosed.inter (isClosed_biInter fun x _ =>
      isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hGcv : Convex ℝ G := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 := hy1.1 z hz
      have h2 := hy2.1 z hz
      nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h2)]
    · intro x hx
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hy1.2 x hx,
        hy2.2 x hx]
      linarith
  have hGe : IsExtreme ℝ P G := by
    refine ⟨fun y hy => hy.1, ?_⟩
    intro y1 hy1 y2 hy2 y hy hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have key : ∀ x ∈ F, ⟪x, y1⟫_ℝ = 1 ∧ ⟪x, y2⟫_ℝ = 1 := by
      intro x hx
      have h := hy.2 x hx
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at h
      have h1 := hy1 x (hFC hx)
      have h2 := hy2 x (hFC hx)
      constructor <;> nlinarith
    exact ⟨hy1, fun x hx => (key x hx).1⟩
  by_contra hcon
  push Not at hcon
  have hall : G.extremePoints ℝ ⊆ {y | 1 ≤ ⟪v, y⟫_ℝ} := by
    intro y hy
    have hyP := hGe.extremePoints_subset_extremePoints hy
    exact hcon y hyP hy.1.2
  have hconv : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | 1 ≤ ⟪v, y⟫_ℝ} := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hy1 hy2 ⊢
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith
  have hy0G : y0 ∈ G := ⟨hy0P, hy0F⟩
  have := convexHull_min hall hconv (aux_nrk_eq hGc hGcv hy0G)
  simp only [Set.mem_ofPred_eq] at this
  linarith

theorem aux_nrk_polytope_compact {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) : IsCompact C ∧ Convex ℝ C := by
  obtain ⟨V, hV⟩ := hC.1
  rw [hV]
  exact ⟨V.finite_toSet.isCompact_convexHull (𝕜 := ℝ), convex_convexHull ℝ _⟩

/-- An exposed face is not contained in another face iff it has an extreme point outside it. -/
theorem aux_nrk_ext_out {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsPolytope C)
    (H F : Set (EuclideanSpace ℝ (Fin n))) (hH : IsExposed ℝ C H) (hF : IsExposed ℝ C F)
    (hHF : ¬ H ⊆ F) : ∃ v ∈ Set.extremePoints ℝ C, v ∈ H ∧ v ∉ F := by
  obtain ⟨hCc, hCcv⟩ := aux_nrk_polytope_compact C hC
  by_contra hcon
  push Not at hcon
  apply hHF
  have h1 : H.extremePoints ℝ ⊆ F := fun v hv =>
    hcon v (hH.isExtreme.extremePoints_subset_extremePoints hv) hv.1
  exact (aux_nrk_eq (hH.isCompact hCc) (hH.convex hCcv)).trans (convexHull_min h1 (hF.convex hCcv))

/-- Forward direction of Theorem 4.11. -/
theorem aux_nrk_forward {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) (k : ℕ) (hB : HasBooleanFactorization C k) :
    Nonempty (Face C ↪o Finset (Fin k)) := by
  classical
  obtain ⟨A, B, hAB⟩ := hB
  let φ : Face C → Finset (Fin k) := fun F =>
    Finset.univ.filter (fun i => ∃ x ∈ Set.extremePoints ℝ C, x ∈ F.1 ∧ i ∈ A x)
  refine ⟨OrderEmbedding.ofMapLEIff φ ?_⟩
  intro H F
  constructor
  · intro hle
    show H.1 ⊆ F.1
    by_contra hHF
    obtain ⟨v, hv, hvH, hvF⟩ := aux_nrk_ext_out C hC H.1 F.1 H.2 F.2 hHF
    obtain ⟨y, hy, hyF, hyv⟩ := aux_nrk_sep C hC F.1 F.2 v hv.1 hvF
    have hs : slackOperator v y ≠ 0 := by
      unfold slackOperator; linarith
    obtain ⟨i, hi⟩ := (hAB v hv y hy).1 hs
    rw [Finset.mem_inter] at hi
    have hiH : i ∈ φ H := Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, hvH, hi.1⟩
    have hiF := hle hiH
    obtain ⟨_, x, hx, hxF, hix⟩ := Finset.mem_filter.1 hiF
    have hs0 : slackOperator x y = 0 := by
      unfold slackOperator; rw [hyF x hxF]; ring
    have := mt (hAB x hx y hy).2 (not_not.2 hs0)
    exact this ⟨i, Finset.mem_inter.2 ⟨hix, hi.2⟩⟩
  · intro hle i hi
    obtain ⟨_, x, hx, hxH, hix⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, (show H.1 ⊆ F.1 from hle) hxH, hix⟩

/-- Extreme points of a polytope are exposed points. -/
theorem aux_nrk_exposed_pt {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Set.extremePoints ℝ C) :
    IsExposed ℝ C {x} := by
  classical
  obtain ⟨V, hV⟩ := hC.1
  set V' : Finset (EuclideanSpace ℝ (Fin n)) := V.filter (fun w => w ≠ x) with hV'
  set K := convexHull ℝ (V' : Set (EuclideanSpace ℝ (Fin n))) with hK
  have hKC : K ⊆ C := by
    rw [hV]; apply convexHull_mono; intro w hw
    simp only [hV', Finset.coe_filter, Set.mem_ofPred_eq] at hw; exact hw.1
  have hxK : x ∉ K := by
    intro hxK
    have h1 : x ∈ K.extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset hKC ⟨hxK, hx⟩
    have h2 := extremePoints_convexHull_subset h1
    simp [hV'] at h2
  obtain ⟨f, u, hfx, hfK⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((V'.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed) hxK
  intro _
  refine ⟨-f, ?_⟩
  -- the set S = {x} ∪ {f > f x} is convex and contains V
  set S := {w : EuclideanSpace ℝ (Fin n) | w = x ∨ f x < f w} with hS
  have hSc : Convex ℝ S := by
    intro w1 hw1 w2 hw2 a b ha hb hab
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0; simp at hab; subst hab; simpa using hw2
    rcases hb.eq_or_lt with hb0 | hb0
    · subst hb0; simp at hab; subst hab; simpa using hw1
    have e1 : f x ≤ f w1 := by
      rcases hw1 with h | h
      exacts [le_of_eq (congrArg f h.symm), h.le]
    have e2 : f x ≤ f w2 := by
      rcases hw2 with h | h
      exacts [le_of_eq (congrArg f h.symm), h.le]
    rcases hw1 with h1 | h1
    · rcases hw2 with h2 | h2
      · left; rw [h1, h2, ← add_smul, hab, one_smul]
      · right
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have hc : a * f x + b * f x = f x := by rw [← add_mul, hab, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_lt_mul_of_pos_left h2 hb0]
    · right
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have hc : a * f x + b * f x = f x := by rw [← add_mul, hab, one_mul]
      nlinarith [mul_lt_mul_of_pos_left h1 ha0, mul_le_mul_of_nonneg_left e2 hb]
  have hVS : (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ S := by
    intro w hw
    by_cases hwx : w = x
    · left; exact hwx
    · right
      have : w ∈ K := subset_convexHull ℝ _ (by rw [hV', Finset.coe_filter]; exact ⟨hw, hwx⟩)
      linarith [hfK w this]
  have hCS : C ⊆ S := by rw [hV]; exact convexHull_min hVS hSc
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, ContinuousLinearMap.neg_apply, neg_le_neg_iff]
  constructor
  · rintro rfl
    refine ⟨hx.1, fun w hw => ?_⟩
    rcases hCS hw with h | h
    · rw [h]
    · exact h.le
  · rintro ⟨hz, hzw⟩
    rcases hCS hz with h | h
    · exact h
    · have := hzw x hx.1; linarith

/-- The face of `C` cut out by `y ∈ C°`. -/
theorem aux_nrk_exposed_y {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ConeLifts.Shared.polar C) :
    IsExposed ℝ C {x ∈ C | ⟪x, y⟫_ℝ = 1} := by
  rintro ⟨x0, hx0C, hx0⟩
  refine ⟨innerSL ℝ y, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, innerSL_apply_apply]
  constructor
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, fun z hz => ?_⟩
    have e1 := real_inner_comm x y
    have e2 := real_inner_comm z y
    linarith [hy z hz]
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    have h1 := hx x0 hx0C
    have h2 := hy x hxC
    have e1 := real_inner_comm x y
    have e2 := real_inner_comm x0 y
    linarith

theorem booleanFactorization_iff_faceEmbedding_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) (k : ℕ) :
    HasBooleanFactorization C k ↔ Nonempty (Face C ↪o Finset (Fin k)) := by
  classical
  refine ⟨aux_nrk_forward C hC k, ?_⟩
  rintro ⟨φ⟩
  refine ⟨fun x => if h : IsExposed ℝ C {x} then φ (⟨{x}, h⟩ : Face C) else ∅,
    fun y => if h : IsExposed ℝ C {x ∈ C | ⟪x, y⟫_ℝ = 1} then
      Finset.univ \ φ (⟨{x ∈ C | ⟪x, y⟫_ℝ = 1}, h⟩ : Face C) else ∅, ?_⟩
  intro x hx y hy
  have hxe := aux_nrk_exposed_pt C hC x hx
  have hye := aux_nrk_exposed_y C y hy.1
  dsimp only
  rw [dif_pos hxe, dif_pos hye]
  have key : φ (⟨{x}, hxe⟩ : Face C) ≤ φ (⟨{x ∈ C | ⟪x, y⟫_ℝ = 1}, hye⟩ : Face C) ↔
      ⟪x, y⟫_ℝ = 1 := by
    refine (φ.le_iff_le).trans ?_
    show {x} ⊆ {x ∈ C | ⟪x, y⟫_ℝ = 1} ↔ _
    rw [Set.singleton_subset_iff]
    exact ⟨fun h => h.2, fun h => ⟨hx.1, h⟩⟩
  have hsl : slackOperator x y ≠ 0 ↔ ⟪x, y⟫_ℝ ≠ 1 := by
    unfold slackOperator; constructor <;> intro h h' <;> apply h <;> linarith
  rw [hsl]
  constructor
  · intro h
    by_contra hne
    apply h
    apply key.1
    intro i hi
    by_contra hit
    exact hne ⟨i, Finset.mem_inter.2 ⟨hi, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hit⟩⟩⟩
  · rintro ⟨i, hi⟩ heq
    have hst := key.2 heq
    rw [Finset.mem_inter, Finset.mem_sdiff] at hi
    exact hi.2.2 (hst hi.1)

/-- A nonnegative factorization yields a Boolean factorization of the support. -/
theorem aux_nrk_nonneg_bool {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (h : HasNonnegFactorization C k) : HasBooleanFactorization C k := by
  classical
  obtain ⟨A, B, hA, hB, hAB⟩ := h
  refine ⟨fun x => Finset.univ.filter (fun i => 0 < A x i),
    fun y => Finset.univ.filter (fun i => 0 < B y i), ?_⟩
  intro x hx y hy
  rw [hAB x hx y hy]
  constructor
  · intro hne
    by_contra hno
    apply hne
    apply Finset.sum_eq_zero
    intro i _
    rcases (hA x hx i).eq_or_lt with h1 | h1
    · rw [← h1, zero_mul]
    rcases (hB y hy i).eq_or_lt with h2 | h2
    · rw [← h2, mul_zero]
    exact absurd ⟨i, by simp [h1, h2]⟩ hno
  · rintro ⟨i, hi⟩
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hpos : 0 < A x i * B y i := mul_pos hi.1 hi.2
    have hle : A x i * B y i ≤ ∑ j, A x j * B y j :=
      Finset.single_le_sum (f := fun j => A x j * B y j)
        (fun j _ => mul_nonneg (hA x hx j) (hB y hy j)) (Finset.mem_univ i)
    linarith

theorem aux_nrk_emb {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsPolytope C) (k : ℕ)
    (h : HasNonnegFactorization C k) : Nonempty (Face C ↪o Finset (Fin k)) :=
  aux_nrk_forward C hC k (aux_nrk_nonneg_bool C k h)

theorem faceEmbeddingDim_le_nonnegRank_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) :
    ((sInf {k : ℕ | Nonempty (Face C ↪o Finset (Fin k))} : ℕ) : ℕ∞) ≤ nonnegRank C := by
  unfold nonnegRank
  refine le_iInf₂ fun k hk => ?_
  exact Nat.cast_le.2 (Nat.sInf_le (aux_nrk_emb C hC k hk))

theorem aux_nrk_attained {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (hk : (k : ℕ∞) = nonnegRank C) : HasNonnegFactorization C k := by
  by_cases hne : {m : ℕ | HasNonnegFactorization C m}.Nonempty
  · have hm := Nat.sInf_mem hne
    have heq : nonnegRank C = ((sInf {m : ℕ | HasNonnegFactorization C m} : ℕ) : ℕ∞) := by
      unfold nonnegRank
      refine le_antisymm (iInf₂_le _ hm) (le_iInf₂ fun j hj => Nat.cast_le.2 (Nat.sInf_le hj))
    rw [heq, Nat.cast_inj] at hk
    rw [hk]; exact hm
  · exfalso
    have : nonnegRank C = ⊤ := by
      unfold nonnegRank
      refine iInf₂_eq_top.2 fun j hj => absurd ⟨j, hj⟩ hne
    rw [this] at hk
    exact ENat.natCast_ne_top k hk

theorem nonnegRank_face_lattice_bounds_core {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) :
    (∀ 𝒜 : Finset (Face C), IsAntichain (· ≤ ·) (𝒜 : Set (Face C)) →
        ((sInf {k : ℕ | 𝒜.card ≤ k.choose (k / 2)} : ℕ) : ℕ∞) ≤ nonnegRank C) ∧
    (∀ k : ℕ, (k : ℕ∞) = nonnegRank C → Real.logb 2 (Nat.card (Face C) : ℝ) ≤ k) := by
  classical
  constructor
  · intro 𝒜 h𝒜
    unfold nonnegRank
    refine le_iInf₂ fun k hk => ?_
    obtain ⟨φ⟩ := aux_nrk_emb C hC k hk
    refine Nat.cast_le.2 (Nat.sInf_le ?_)
    show 𝒜.card ≤ k.choose (k / 2)
    have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (𝒜.map φ.toEmbedding)) := by
      intro a ha b hb hab hsub
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hne : a' ≠ b' := fun h => hab (by rw [h])
      exact h𝒜 ha' hb' hne ((φ.le_iff_le).1 hsub)
    have := hanti.sperner
    simpa using this
  · intro k hk
    obtain ⟨φ⟩ := aux_nrk_emb C hC k (aux_nrk_attained C k hk)
    have hcard : Nat.card (Face C) ≤ 2 ^ k := by
      have := Nat.card_le_card_of_injective φ φ.injective
      simpa [Nat.card_eq_fintype_card, Fintype.card_finset] using this
    rcases Nat.eq_zero_or_pos (Nat.card (Face C)) with h0 | hpos
    · rw [h0]; simp
    · calc Real.logb 2 (Nat.card (Face C) : ℝ) ≤ Real.logb 2 ((2:ℝ) ^ k) := by
            apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
            exact_mod_cast hcard
        _ = k := by simp [Real.logb_pow]

end ConeLifts.NonnegRank

open ConeLifts.NonnegRank


theorem solution {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsPolytope C) (k : ℕ) :
    HasBooleanFactorization C k ↔ Nonempty (Face C ↪o Finset (Fin k)) := by
  exact booleanFactorization_iff_faceEmbedding_core C hC k
