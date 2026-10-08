-- Prove2me | solution 1 for ConeLifts.Factorization.slater_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:53:46.577675+00:00
-- url     : https://prove2.me/submissions/c412c49e-5d8f-4e8d-98cf-923511387ef5

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace Pointwise

set_option autoImplicit false

namespace SlaterCert588

lemma slope_zero {b c : ℝ} (h : ∀ s : ℝ, s * b < c) : b = 0 := by
  by_contra hb
  have := h (c / b)
  rw [div_mul_cancel₀ c hb] at this
  exact lt_irrefl _ this

lemma nonpos_of_scale {b M : ℝ} (h : ∀ s : ℝ, 0 < s → s * b ≤ M) : b ≤ 0 := by
  by_contra hb
  push_neg at hb
  have := h ((|M| + 1) / b) (by positivity)
  rw [div_mul_cancel₀ _ hb.ne'] at this
  have := le_abs_self M
  linarith

lemma nonneg_of_scale {b M : ℝ} (h : ∀ s : ℝ, 0 < s → s * b ≤ M) : 0 ≤ M := by
  by_contra hM
  push_neg at hM
  have hb : b < 0 := by have := h 1 one_pos; linarith
  have := h (M / (2 * b)) (div_pos_of_neg_of_neg hM (by linarith))
  have e : M / (2 * b) * b = M / 2 := by
    rw [div_mul_eq_mul_div, mul_comm 2 b, ← div_div, mul_div_cancel_right₀ M hb.ne]
  rw [e] at this
  linarith

lemma exists_inner_eq_one {n : ℕ} (hn : 1 ≤ n) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsCompact C) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ C)
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :
    ∃ x ∈ C, ⟪x, c⟫_ℝ = 1 := by
  rw [mem_extremePoints] at hc
  obtain ⟨hcP, hext⟩ := hc
  obtain ⟨x0, hx0C, hmax⟩ := hCc.exists_isMaxOn (f := fun x => ⟪x, c⟫_ℝ) ⟨0, h0⟩
    (continuous_id.inner continuous_const).continuousOn
  rw [isMaxOn_iff] at hmax
  refine ⟨x0, hx0C, ?_⟩
  have hle : ⟪x0, c⟫_ℝ ≤ 1 := hcP x0 hx0C
  have hs0 : 0 ≤ ⟪x0, c⟫_ℝ := by
    have := hmax 0 h0
    simpa using this
  by_contra hne
  have hlt : ⟪x0, c⟫_ℝ < 1 := lt_of_le_of_ne hle hne
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 2 / (1 + ⟪x0, c⟫_ℝ) := ⟨_, rfl⟩
  have hlam1 : 1 < lam := by rw [hlam, lt_div_iff₀ (by linarith)]; linarith
  have hlamP : (lam • c) ∈ ConeLifts.Shared.polar C := by
    intro x hx
    have hx' : ⟪x, c⟫_ℝ ≤ ⟪x0, c⟫_ℝ := hmax x hx
    rw [inner_smul_right]
    have : lam * ⟪x0, c⟫_ℝ ≤ 1 := by
      rw [hlam, div_mul_eq_mul_div, div_le_one (by linarith)]; linarith
    nlinarith
  have h0P : (0 : EuclideanSpace ℝ (Fin n)) ∈ ConeLifts.Shared.polar C := by
    intro x _
    simp
  have hlam0 : lam ≠ 0 := by linarith
  have hseg : c ∈ openSegment ℝ (0 : EuclideanSpace ℝ (Fin n)) (lam • c) := by
    refine ⟨1 - lam⁻¹, lam⁻¹, ?_, by positivity, by ring, ?_⟩
    · have : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam1
      linarith
    · rw [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hc0 : (0 : EuclideanSpace ℝ (Fin n)) = c := (hext 0 h0P (lam • c) hlamP hseg).1
  -- now `0` is an extreme point of the polar: impossible since the polar contains a ball
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hCc.isBounded
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 :=
    ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ), by simp⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (|R| + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hRδ : |R| * δ ≤ 1 := by
    rw [hδdef, mul_one_div, div_le_one (by positivity)]; linarith
  have hyP : ∀ y' : EuclideanSpace ℝ (Fin n), ‖y'‖ ≤ δ →
      y' ∈ ConeLifts.Shared.polar C := by
    intro y' hy' x hx
    calc ⟪x, y'⟫_ℝ ≤ ‖x‖ * ‖y'‖ := real_inner_le_norm x y'
      _ ≤ |R| * δ := mul_le_mul (le_trans (hR x hx) (le_abs_self R)) hy' (norm_nonneg _)
          (abs_nonneg _)
      _ ≤ 1 := hRδ
  have hny : ‖δ • e‖ = δ := by rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hδ]
  have h1 := hyP (δ • e) hny.le
  have h2 := hyP (-(δ • e)) (by rw [norm_neg, hny])
  have hseg2 : c ∈ openSegment ℝ (δ • e) (-(δ • e)) := by
    rw [← hc0]
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_neg, add_neg_cancel]
  have hy0 := (hext (δ • e) h1 (-(δ • e)) h2 hseg2).1
  rw [← hc0] at hy0
  have : ‖δ • e‖ = 0 := by rw [hy0, norm_zero]
  linarith

end SlaterCert588

open ConeLifts.Factorization in open scoped InnerProductSpace in
theorem solution {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (w₀ : EuclideanSpace ℝ (Fin m)) (hw₀L : w₀ ∈ L) (hw₀K : w₀ ∈ interior K)
    (hCπ : C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))))
    (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)) :
    IsLeast {t : ℝ | ∃ z ∈ L.directionᗮ,
        z - LinearMap.adjoint π c ∈ ConeLifts.Shared.dualCone K ∧ t = ⟪w₀, z⟫_ℝ} 1 := by
  classical
  obtain ⟨hCc, hCconv, hC0⟩ := hC
  obtain ⟨hKcl, hKconv, hK0, hKsm⟩ := hK
  have hcP : c ∈ ConeLifts.Shared.polar C := (mem_extremePoints.1 hc).1
  set a := LinearMap.adjoint π c with ha
  have ha_inner : ∀ w, ⟪a, w⟫_ℝ = ⟪c, π w⟫_ℝ := fun w => LinearMap.adjoint_inner_left π w c
  have hprimal : ∀ w ∈ K, w ∈ L → ⟪a, w⟫_ℝ ≤ 1 := by
    intro w hwK hwL
    have hmem : π w ∈ C := by rw [hCπ]; exact ⟨w, ⟨hwK, hwL⟩, rfl⟩
    have := hcP (π w) hmem
    rw [ha_inner]
    linarith [real_inner_comm (π w) c]
  have hw0Kc : w₀ ∈ K := interior_subset hw₀K
  -- lower bound
  obtain ⟨xs, hxsC, hxs1⟩ :=
    SlaterCert588.exists_inner_eq_one hn C hCc (interior_subset hC0) c hc
  rw [hCπ] at hxsC
  obtain ⟨ws, ⟨hwsK, hwsL⟩, rfl⟩ := hxsC
  have hlower : ∀ z ∈ L.directionᗮ, z - a ∈ ConeLifts.Shared.dualCone K →
      1 ≤ ⟪w₀, z⟫_ℝ := by
    intro z hzL hzK
    have hd : ws - w₀ ∈ L.direction := by
      have := AffineSubspace.vsub_mem_direction hwsL hw₀L
      rwa [vsub_eq_sub] at this
    have h1 : ⟪ws - w₀, z⟫_ℝ = 0 := by
      rw [Submodule.mem_orthogonal] at hzL
      exact hzL _ hd
    have h2 : 0 ≤ ⟪ws, z - a⟫_ℝ := hzK ws hwsK
    rw [inner_sub_left] at h1
    rw [inner_sub_right] at h2
    have h3 : ⟪ws, a⟫_ℝ = 1 := by
      rw [real_inner_comm, ha_inner, real_inner_comm]; exact hxs1
    linarith
  -- separation
  obtain ⟨O, hOdef⟩ : ∃ O : Set (EuclideanSpace ℝ (Fin m) × ℝ),
      O = ⋃ l ∈ (L.direction : Set (EuclideanSpace ℝ (Fin m))),
        {p : EuclideanSpace ℝ (Fin m) × ℝ |
          p.1 + w₀ + l ∈ interior K ∧ p.2 < ⟪a, p.1 + w₀ + l⟫_ℝ} := ⟨_, rfl⟩
  have hOmem : ∀ p : EuclideanSpace ℝ (Fin m) × ℝ, p ∈ O ↔
      ∃ l ∈ L.direction, p.1 + w₀ + l ∈ interior K ∧ p.2 < ⟪a, p.1 + w₀ + l⟫_ℝ := by
    intro p
    rw [hOdef]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe, exists_prop]
  have hOopen : IsOpen O := by
    rw [hOdef]
    refine isOpen_biUnion fun l _ => ?_
    rw [Set.setOf_and]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_interior.preimage
        ((continuous_fst.add continuous_const).add continuous_const)
    · exact isOpen_lt continuous_snd
        (continuous_const.inner ((continuous_fst.add continuous_const).add continuous_const))
  have hKiconv : Convex ℝ (interior K) := hKconv.interior
  have hOconv : Convex ℝ O := by
    rw [convex_iff_forall_pos]
    intro p hp q hq s t hs ht hst
    rw [hOmem] at hp hq ⊢
    obtain ⟨l1, hl1, hp1, hp2⟩ := hp
    obtain ⟨l2, hl2, hq1, hq2⟩ := hq
    have hw : w₀ = s • w₀ + t • w₀ := by rw [← add_smul, hst, one_smul]
    have heq : (s • p + t • q).1 + w₀ + (s • l1 + t • l2) =
        s • (p.1 + w₀ + l1) + t • (q.1 + w₀ + l2) := by
      calc (s • p + t • q).1 + w₀ + (s • l1 + t • l2)
          = (s • p.1 + t • q.1) + (s • w₀ + t • w₀) + (s • l1 + t • l2) := by
            rw [← hw]; rfl
        _ = s • (p.1 + w₀ + l1) + t • (q.1 + w₀ + l2) := by
            simp only [smul_add]; abel
    refine ⟨s • l1 + t • l2,
      L.direction.add_mem (L.direction.smul_mem s hl1) (L.direction.smul_mem t hl2), ?_, ?_⟩
    · rw [heq]; exact hKiconv hp1 hq1 hs.le ht.le hst
    · rw [heq, inner_add_right, inner_smul_right, inner_smul_right]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [mul_lt_mul_of_pos_left hp2 hs, mul_lt_mul_of_pos_left hq2 ht]
  have h01 : ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) ∉ O := by
    rw [hOmem]
    rintro ⟨l, hl, h1, h2⟩
    simp only [zero_add] at h1 h2
    have hL : w₀ + l ∈ L := by
      have := AffineSubspace.vadd_mem_of_mem_direction hl hw₀L
      rwa [vadd_eq_add, add_comm] at this
    linarith [hprimal _ (interior_subset h1) hL]
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hOconv hOopen h01
  set α := f ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) with hα
  set φ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) ℝ) with hφ
  have hfdec : ∀ u : EuclideanSpace ℝ (Fin m), ∀ t : ℝ, f (u, t) = φ u + t * α := by
    intro u t
    have : (u, t) = (u, (0 : ℝ)) + t • ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  -- α > 0
  have hw0in : ((0 : EuclideanSpace ℝ (Fin m)), ⟪a, w₀⟫_ℝ - 1) ∈ O := by
    rw [hOmem]
    refine ⟨0, L.direction.zero_mem, ?_, ?_⟩
    · show 0 + w₀ + 0 ∈ interior K
      simpa using hw₀K
    · show ⟪a, w₀⟫_ℝ - 1 < ⟪a, 0 + w₀ + 0⟫_ℝ
      simp only [zero_add, add_zero]
      linarith
  have hαpos : 0 < α := by
    have h := hf _ hw0in
    rw [hfdec, map_zero] at h
    have := hprimal w₀ hw0Kc hw₀L
    by_contra hα0
    push_neg at hα0
    nlinarith
  have hαne : α ≠ 0 := hαpos.ne'
  -- φ vanishes on the direction
  have hφL : ∀ l ∈ L.direction, φ l = 0 := by
    intro l hl
    have key : ∀ s : ℝ, s * (-(φ l)) < α - (⟪a, w₀⟫_ℝ - 1) * α := by
      intro s
      have e : -(s • l) + w₀ + s • l = w₀ := by abel
      have hp : (-(s • l), ⟪a, w₀⟫_ℝ - 1) ∈ O := by
        rw [hOmem]
        refine ⟨s • l, L.direction.smul_mem s hl, ?_, ?_⟩
        · show -(s • l) + w₀ + s • l ∈ interior K
          rw [e]; exact hw₀K
        · show ⟪a, w₀⟫_ℝ - 1 < ⟪a, -(s • l) + w₀ + s • l⟫_ℝ
          rw [e]; linarith
      have h := hf _ hp
      rw [hfdec, map_neg, map_smul, smul_eq_mul] at h
      linarith
    have := SlaterCert588.slope_zero key
    linarith
  -- bound on the interior
  have hbound : ∀ x ∈ interior K, φ x + α * ⟪a, x⟫_ℝ ≤ α + φ w₀ := by
    intro x hx
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hp : (x - w₀, ⟪a, x⟫_ℝ - ε / α) ∈ O := by
      rw [hOmem]
      refine ⟨0, L.direction.zero_mem, ?_, ?_⟩
      · show x - w₀ + w₀ + 0 ∈ interior K
        rw [sub_add_cancel, add_zero]; exact hx
      · show ⟪a, x⟫_ℝ - ε / α < ⟪a, x - w₀ + w₀ + 0⟫_ℝ
        rw [sub_add_cancel, add_zero]
        have := div_pos hε hαpos
        linarith
    have h := hf _ hp
    rw [hfdec, map_sub] at h
    have e : (⟪a, x⟫_ℝ - ε / α) * α = ⟪a, x⟫_ℝ * α - ε := by
      rw [sub_mul, div_mul_cancel₀ ε hαne]
    rw [e] at h
    linarith
  have hKi_smul : ∀ s : ℝ, 0 < s → ∀ x ∈ interior K, s • x ∈ interior K := by
    intro s hs x hx
    have h1 : interior (s • K) = s • interior K := interior_smul₀ hs.ne' K
    have h2 : s • K ⊆ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hKsm s hs.le y hy
    apply interior_mono h2
    rw [h1]
    exact Set.smul_mem_smul_set hx
  have hscale : ∀ x ∈ interior K, ∀ s : ℝ, 0 < s →
      s * (φ x + α * ⟪a, x⟫_ℝ) ≤ α + φ w₀ := by
    intro x hx s hs
    have := hbound _ (hKi_smul s hs x hx)
    rw [map_smul, inner_smul_right, smul_eq_mul] at this
    have e : s * (φ x + α * ⟪a, x⟫_ℝ) = s * φ x + α * (s * ⟪a, x⟫_ℝ) := by ring
    rw [e]
    exact this
  have hM : 0 ≤ α + φ w₀ := SlaterCert588.nonneg_of_scale (hscale w₀ hw₀K)
  have hneg_int : ∀ x ∈ interior K, φ x + α * ⟪a, x⟫_ℝ ≤ 0 :=
    fun x hx => SlaterCert588.nonpos_of_scale (hscale x hx)
  have hneg : ∀ x ∈ K, φ x + α * ⟪a, x⟫_ℝ ≤ 0 := by
    have hcl : K ⊆ closure (interior K) := by
      rw [hKconv.closure_interior_eq_closure_of_nonempty_interior hKint]
      exact subset_closure
    have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin m) | φ x + α * ⟪a, x⟫_ℝ ≤ 0} :=
      isClosed_le (φ.continuous.add (continuous_const.mul
        (continuous_const.inner continuous_id))) continuous_const
    intro x hx
    exact closure_minimal (fun y hy => hneg_int y hy) hclosed (hcl hx)
  -- the dual certificate
  obtain ⟨ζ, hζ_inner⟩ : ∃ ζ : EuclideanSpace ℝ (Fin m), ∀ u, ⟪ζ, u⟫_ℝ = φ u :=
    ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm φ,
      fun u => InnerProductSpace.toDual_symm_apply⟩
  have hz1 : -(α⁻¹) • ζ ∈ L.directionᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [inner_smul_right, real_inner_comm, hζ_inner, hφL u hu, mul_zero]
  have hz2 : -(α⁻¹) • ζ - a ∈ ConeLifts.Shared.dualCone K := by
    intro x hx
    rw [inner_sub_right, inner_smul_right, real_inner_comm ζ x, hζ_inner,
      real_inner_comm a x]
    have hk := mul_le_mul_of_nonneg_left (hneg x hx) (inv_pos.2 hαpos).le
    rw [mul_zero, mul_add, ← mul_assoc, inv_mul_cancel₀ hαne, one_mul] at hk
    linarith
  have hz3 : ⟪w₀, -(α⁻¹) • ζ⟫_ℝ ≤ 1 := by
    rw [inner_smul_right, real_inner_comm, hζ_inner]
    have hk := mul_nonneg (inv_pos.2 hαpos).le hM
    rw [mul_add, inv_mul_cancel₀ hαne] at hk
    linarith
  refine ⟨⟨-(α⁻¹) • ζ, hz1, hz2, le_antisymm (hlower _ hz1 hz2) hz3⟩, ?_⟩
  rintro t ⟨z, hz, hzK, rfl⟩
  exact hlower z hz hzK
