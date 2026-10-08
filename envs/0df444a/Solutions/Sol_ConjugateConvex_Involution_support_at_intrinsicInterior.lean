-- Prove2me | solution 1 for ConjugateConvex.Involution.support_at_intrinsicInterior
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:58:19.903142+00:00
-- url     : https://prove2.me/submissions/a98a8ff5-6529-4ffb-967e-3884357e56cd

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun



namespace ConjugateConvex.Involution

theorem ci_mem_ri_iff {n : ℕ} {G : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ intrinsicInterior ℝ G ↔
      x ∈ G ∧ ∃ ε > 0, ∀ v ∈ (affineSpan ℝ G).direction, ‖v‖ < ε → x + v ∈ G := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hy
    obtain ⟨u, hu, hsub⟩ := hy
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨?_, ε, hε, fun v hv hvn => ?_⟩
    · exact hsub (show (y : Fin n → ℝ) ∈ u from mem_of_mem_nhds hu)
    · have hmem : v +ᵥ (y : Fin n → ℝ) ∈ affineSpan ℝ G :=
        AffineSubspace.vadd_mem_of_mem_direction hv y.2
      have := hsub (a := ⟨v +ᵥ (y : Fin n → ℝ), hmem⟩) (hball (by
        simp only [Metric.mem_ball, dist_eq_norm, vadd_eq_add]
        simpa using hvn))
      simpa [vadd_eq_add, add_comm] using this
  · rintro ⟨hxG, ε, hε, hball⟩
    refine ⟨⟨x, subset_affineSpan ℝ G hxG⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
    refine ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, ?_⟩
    rintro ⟨w, hw⟩ hwb
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hwb ⊢
    have hv : w - x ∈ (affineSpan ℝ G).direction :=
      AffineSubspace.vsub_mem_direction hw (subset_affineSpan ℝ G hxG)
    have := hball _ hv hwb
    simpa using this

theorem ci_segment_ri {n : ℕ} {G : Set (Fin n → ℝ)} (hG : Convex ℝ G) {x y : Fin n → ℝ}
    (hx : x ∈ G) (hy : y ∈ intrinsicInterior ℝ G) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • y ∈ intrinsicInterior ℝ G := by
  rw [ci_mem_ri_iff] at hy ⊢
  obtain ⟨hyG, ε, hε, hball⟩ := hy
  refine ⟨hG hx hyG (by linarith) ht0.le (by ring), t * ε, mul_pos ht0 hε, fun v hv hvn => ?_⟩
  have h1 : t⁻¹ • v ∈ (affineSpan ℝ G).direction := Submodule.smul_mem _ _ hv
  have h2 : ‖t⁻¹ • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
    rw [inv_mul_lt_iff₀ ht0]; exact hvn
  have h3 := hG hx (hball _ h1 h2) (a := 1 - t) (b := t) (by linarith) ht0.le (by ring)
  have : (1 - t) • x + t • (y + t⁻¹ • v) = (1 - t) • x + t • y + v := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, add_assoc]
  rwa [this] at h3


theorem ci_rep {n : ℕ} (φ : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (x : Fin n → ℝ) (t : ℝ) :
    φ (x, t) = x ⬝ᵥ (fun i => φ ((fun j => if i = j then (1:ℝ) else 0), 0)) + t * φ (0, 1) := by
  have h1 : (x, t) = (x, (0:ℝ)) + t • ((0 : Fin n → ℝ), (1:ℝ)) := by ext <;> simp
  rw [h1, map_add, map_smul, smul_eq_mul]
  congr 1
  have := LinearMap.pi_apply_eq_sum_univ
    ((φ : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ).toLinearMap.comp (LinearMap.inl ℝ (Fin n → ℝ) ℝ)) x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
    ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this, dotProduct]

theorem ci_subgrad_interior {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ interior G) :
    ∃ ξ : Fin n → ℝ, ∀ y ∈ interior G, y ⬝ᵥ ξ - f y ≤ x₀ ⬝ᵥ ξ - f x₀ := by
  have hfi : ConvexOn ℝ (interior G) f := hf.subset interior_subset hf.1.interior
  have hcont : ContinuousOn f (interior G) := hf.continuousOn_interior
  set U : Set ((Fin n → ℝ) × ℝ) := {q | q.1 ∈ interior G ∧ f q.1 < q.2} with hU
  have hUc : Convex ℝ U := hfi.convex_strict_epigraph
  have hUo : IsOpen U := by
    have hc2 : ContinuousOn (fun q : (Fin n → ℝ) × ℝ => f q.1 - q.2) (Prod.fst ⁻¹' interior G) :=
      (hcont.comp continuousOn_fst (fun q hq => hq)).sub continuousOn_snd
    have := hc2.isOpen_inter_preimage (isOpen_interior.preimage continuous_fst)
      (isOpen_Iio (a := (0:ℝ)))
    convert this using 1
    ext q; simp [hU, sub_neg]
  have hnot : (x₀, f x₀) ∉ U := fun h => lt_irrefl _ h.2
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hUc hUo hnot
  set a : Fin n → ℝ := fun i => φ ((fun j => if i = j then (1:ℝ) else 0), 0) with ha
  set c : ℝ := φ (0, 1) with hcdef
  have hrep : ∀ x t, φ (x, t) = x ⬝ᵥ a + t * c := fun x t => ci_rep φ x t
  have hc : c < 0 := by
    have := hφ (x₀, f x₀ + 1) ⟨hx₀, by simp⟩
    rw [hrep, hrep] at this
    linarith
  have hle : ∀ y ∈ interior G, y ⬝ᵥ a + f y * c ≤ x₀ ⬝ᵥ a + f x₀ * c := by
    intro y hy
    by_contra hlt
    push Not at hlt
    set d := y ⬝ᵥ a + f y * c - (x₀ ⬝ᵥ a + f x₀ * c) with hd
    have hdpos : 0 < d := by rw [hd]; linarith
    have hmem : (y, f y - d / (2 * c)) ∈ U := by
      refine ⟨hy, ?_⟩
      have : 0 < -(d / (2 * c)) := by
        rw [← neg_div, lt_div_iff_of_neg (by linarith)]; linarith
      show f y < f y - d / (2 * c)
      linarith
    have := hφ _ hmem
    rw [hrep, hrep] at this
    have e : (f y - d / (2 * c)) * c = f y * c - d / 2 := by
      rw [sub_mul, div_mul_eq_mul_div, mul_div_mul_right _ _ hc.ne]
    rw [e] at this
    linarith
  refine ⟨(-c)⁻¹ • a, fun y hy => ?_⟩
  have key := mul_le_mul_of_nonneg_left (hle y hy) (inv_nonneg.2 (neg_nonneg.2 hc.le))
  have hcc : (-c)⁻¹ * (-c) = 1 := inv_mul_cancel₀ (by linarith)
  have e : ∀ z w : ℝ, (-c)⁻¹ * (z + w * c) = (-c)⁻¹ * z - w * ((-c)⁻¹ * (-c)) := by
    intro z w; ring
  rw [e, e, hcc] at key
  simp only [dotProduct_smul, smul_eq_mul]
  linarith

theorem ci_conjFun_eq {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (ξ x₀ : Fin n → ℝ)
    (hx₀ : x₀ ∈ G) (h : ∀ x ∈ G, x ⬝ᵥ ξ - f x ≤ x₀ ⬝ᵥ ξ - f x₀) :
    ξ ∈ conjDomain G f ∧ conjFun G f ξ = x₀ ⬝ᵥ ξ - f x₀ := by
  have hb : BddAbove ((fun x => x ⬝ᵥ ξ - f x) '' G) := ⟨x₀ ⬝ᵥ ξ - f x₀, by
    rintro _ ⟨x, hx, rfl⟩; exact h x hx⟩
  refine ⟨hb, le_antisymm ?_ (le_csSup hb ⟨x₀, hx₀, rfl⟩)⟩
  refine csSup_le (Set.Nonempty.image _ ⟨x₀, hx₀⟩) ?_
  rintro _ ⟨x, hx, rfl⟩; exact h x hx

theorem ci_support {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ intrinsicInterior ℝ G) :
    ∃ ξ ∈ conjDomain G f, conjFun G f ξ = x₀ ⬝ᵥ ξ - f x₀ := by
  have hx₀G : x₀ ∈ G := intrinsicInterior_subset hx₀
  set V := (affineSpan ℝ G).direction with hV
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (LinearMap.id : V →ₗ[ℝ] V)
  set P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := V.subtype ∘ₗ g with hPdef
  have hP : ∀ v ∈ V, P v = v := by
    intro v hv
    have := congrArg (fun h => (h ⟨v, hv⟩ : V)) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.id_coe, id_eq] at this
    simp [hPdef, this]
  have hPc : Continuous P := LinearMap.continuous_of_finiteDimensional P
  set A : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    P.toAffineMap + AffineMap.const ℝ (Fin n → ℝ) (x₀ - P x₀) with hA
  have hAapp : ∀ z, A z = P z + (x₀ - P x₀) := fun z => rfl
  have hdir : ∀ y ∈ G, y - x₀ ∈ V := fun y hy =>
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ G hy) (subset_affineSpan ℝ G hx₀G)
  have hAy : ∀ y ∈ G, A y = y := by
    intro y hy
    have := hP _ (hdir y hy)
    rw [map_sub] at this
    rw [hAapp]; linear_combination this
  have hconv := hf.comp_affineMap A
  have hint : ∀ y ∈ intrinsicInterior ℝ G, y ∈ interior (A ⁻¹' G) := by
    intro y hy
    have hyG := intrinsicInterior_subset hy
    obtain ⟨_, ε, hε, hball⟩ := ci_mem_ri_iff.1 hy
    rw [mem_interior_iff_mem_nhds]
    have hcz : Continuous (fun z => P (z - y)) := hPc.comp (continuous_id.sub continuous_const)
    have hn : (fun z => P (z - y)) ⁻¹' Metric.ball 0 ε ∈ nhds y := by
      apply hcz.continuousAt.preimage_mem_nhds
      simpa using Metric.ball_mem_nhds (0 : Fin n → ℝ) hε
    refine Filter.mem_of_superset hn (fun z hz => ?_)
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hz ⊢
    have hmem : P (z - y) ∈ V := (g (z - y)).2
    have := hball _ hmem hz
    have e : A z = y + P (z - y) := by
      have h2 := hP _ (hdir y hyG)
      rw [map_sub] at h2
      rw [hAapp, map_sub]; linear_combination h2
    rwa [e]
  obtain ⟨ξ, hξ⟩ := ci_subgrad_interior _ _ hconv x₀ (hint x₀ hx₀)
  have hri : ∀ y ∈ intrinsicInterior ℝ G, y ⬝ᵥ ξ - f y ≤ x₀ ⬝ᵥ ξ - f x₀ := by
    intro y hy
    have := hξ y (hint y hy)
    simp only [Function.comp_apply, hAy y (intrinsicInterior_subset hy), hAy x₀ hx₀G] at this
    exact this
  have hall : ∀ x ∈ G, x ⬝ᵥ ξ - f x ≤ x₀ ⬝ᵥ ξ - f x₀ := by
    intro x hx
    have hz := ci_segment_ri hf.1 hx hx₀ (t := 1/2) (by norm_num) (by norm_num)
    have h1 := hri _ hz
    have h2 := hf.2 hx hx₀G (show (0:ℝ) ≤ 1 - 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (by norm_num)
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h1 h2
    linarith
  obtain ⟨h1, h2⟩ := ci_conjFun_eq G f ξ x₀ hx₀G hall
  exact ⟨ξ, h1, h2⟩

theorem support_core {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hG : G.Nonempty) (hf : ConvexOn ℝ G f) :
    (conjDomain G f).Nonempty ∧
      ∀ x₀ ∈ intrinsicInterior ℝ G,
        ∃ ξ ∈ conjDomain G f, conjFun G f ξ = x₀ ⬝ᵥ ξ - f x₀ := by
  refine ⟨?_, ci_support G f hf⟩
  obtain ⟨x₀, hx₀⟩ := (intrinsicInterior_nonempty hf.1).2 hG
  obtain ⟨ξ, hξ, _⟩ := ci_support G f hf x₀ hx₀
  exact ⟨ξ, hξ⟩

end ConjugateConvex.Involution

open ConjugateConvex.Involution


theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hG : G.Nonempty) (hf : ConvexOn ℝ G f) :
    (conjDomain G f).Nonempty ∧
      ∀ x₀ ∈ intrinsicInterior ℝ G,
        ∃ ξ ∈ conjDomain G f, conjFun G f ξ = x₀ ⬝ᵥ ξ - f x₀ := by
  exact support_core G f hG hf
