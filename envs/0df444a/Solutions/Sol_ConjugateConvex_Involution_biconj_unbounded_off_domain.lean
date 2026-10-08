-- Prove2me | solution 1 for ConjugateConvex.Involution.biconj_unbounded_off_domain
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:01:36.051015+00:00
-- url     : https://prove2.me/submissions/ab5bfb6c-3e4a-4c06-88df-07b39ec1cbd1

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
import Definitions.Def_ConjugateConvex_Involution_IsClosedConvexPair



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

open Filter Topology

theorem ci_le {n : ℕ} {G : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} {ξ x : Fin n → ℝ}
    (hξ : ξ ∈ conjDomain G f) (hx : x ∈ G) : x ⬝ᵥ ξ - f x ≤ conjFun G f ξ :=
  le_csSup hξ ⟨x, hx, rfl⟩

theorem ci_bound {n : ℕ} {G : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (hG : G.Nonempty)
    {ξ : Fin n → ℝ} (B : ℝ) (h : ∀ x ∈ G, x ⬝ᵥ ξ - f x ≤ B) :
    ξ ∈ conjDomain G f ∧ conjFun G f ξ ≤ B := by
  refine ⟨⟨B, ?_⟩, csSup_le (hG.image _) ?_⟩ <;>
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx

theorem ci_sep {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (hG : G.Nonempty)
    (hf : ConvexOn ℝ G f) (p : Fin n → ℝ) (M : ℝ)
    (hpM : (p, M) ∉ closure {q : (Fin n → ℝ) × ℝ | q.1 ∈ G ∧ f q.1 ≤ q.2}) :
    (∃ ξ ∈ conjDomain G f, M ≤ ξ ⬝ᵥ p - conjFun G f ξ) ∨
      (∃ a : Fin n → ℝ, ∃ u : ℝ, (∀ x ∈ G, x ⬝ᵥ a < u) ∧ u < p ⬝ᵥ a) := by
  obtain ⟨φ, u, hφ, hu⟩ :=
    geometric_hahn_banach_closed_point hf.convex_epigraph.closure isClosed_closure hpM
  set a : Fin n → ℝ := fun i => φ ((fun j => if i = j then (1:ℝ) else 0), 0) with ha
  set c : ℝ := φ (0, 1) with hcdef
  have hrep : ∀ x t, φ (x, t) = x ⬝ᵥ a + t * c := fun x t => ci_rep φ x t
  have hin : ∀ x ∈ G, ∀ t, f x ≤ t → x ⬝ᵥ a + t * c < u := by
    intro x hx t ht
    have := hφ (x, t) (subset_closure ⟨hx, ht⟩)
    rwa [hrep] at this
  have hu' : u < p ⬝ᵥ a + M * c := by rw [← hrep]; exact hu
  rcases lt_trichotomy c 0 with hc | hc | hc
  · left
    set k := (-c)⁻¹ with hk
    have hkpos : 0 < k := inv_pos.2 (by linarith)
    have hkc : k * c = -1 := by
      rw [hk, inv_neg, neg_mul, inv_mul_cancel₀ hc.ne]
    refine ⟨k • a, ?_⟩
    have hb : ∀ x ∈ G, x ⬝ᵥ (k • a) - f x ≤ k * u := by
      intro x hx
      have h1 := mul_lt_mul_of_pos_left (hin x hx (f x) le_rfl) hkpos
      rw [dotProduct_smul, smul_eq_mul]
      have e : k * (x ⬝ᵥ a + f x * c) = k * (x ⬝ᵥ a) - f x := by
        linear_combination f x * hkc
      linarith
    obtain ⟨hmem, hle⟩ := ci_bound hG (k * u) hb
    refine ⟨hmem, ?_⟩
    have h2 := mul_lt_mul_of_pos_left hu' hkpos
    have e : k * (p ⬝ᵥ a + M * c) = k * (p ⬝ᵥ a) - M := by linear_combination M * hkc
    rw [dotProduct_comm, dotProduct_smul, smul_eq_mul]
    linarith
  · right
    refine ⟨a, u, fun x hx => ?_, ?_⟩
    · have := hin x hx (f x) le_rfl
      rw [hc] at this; simpa using this
    · rw [hc] at hu'; simpa using hu'
  · exfalso
    obtain ⟨x, hx⟩ := hG
    have := hin x hx (max (f x) ((u - x ⬝ᵥ a) / c)) (le_max_left _ _)
    have h2 : ((u - x ⬝ᵥ a) / c) * c ≤ (max (f x) ((u - x ⬝ᵥ a) / c)) * c :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
    rw [div_mul_cancel₀ _ hc.ne'] at h2
    linarith

theorem ci_notin {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ)
    (M K : ℝ) (hKM : M < K) (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 p)
    (hUG : ∀ y ∈ U ∩ G, K ≤ f y) :
    (p, M) ∉ closure {q : (Fin n → ℝ) × ℝ | q.1 ∈ G ∧ f q.1 ≤ q.2} := by
  intro h
  rw [mem_closure_iff_nhds] at h
  obtain ⟨q, hq1, hq2⟩ := h (U ×ˢ Set.Iio K) (prod_mem_nhds hU (Iio_mem_nhds hKM))
  have := hUG q.1 ⟨hq1.1, hq2.1⟩
  have h3 : q.2 < K := hq1.2
  linarith [hq2.2]

theorem ci_notin_of_ev {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ)
    (M K : ℝ) (hKM : M < K) (hev : ∀ᶠ y in 𝓝[G] p, K ≤ f y) :
    (p, M) ∉ closure {q : (Fin n → ℝ) × ℝ | q.1 ∈ G ∧ f q.1 ≤ q.2} := by
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  exact ci_notin G f p M K hKM U hU (fun y hy => hsub hy)

theorem ci_notin_off {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) (p : Fin n → ℝ) (hp : p ∉ G) (M : ℝ) :
    (p, M) ∉ closure {q : (Fin n → ℝ) × ℝ | q.1 ∈ G ∧ f q.1 ≤ q.2} := by
  by_cases hcl : p ∈ closure G
  · have hT := hGf.2.2.2 p ⟨hcl, hp⟩
    exact ci_notin_of_ev G f p M (M + 1) (by linarith) (tendsto_atTop.1 hT (M + 1))
  · exact ci_notin G f p M (M + 1) (by linarith) (closure G)ᶜ
      (isClosed_closure.isOpen_compl.mem_nhds hcl)
      (fun y hy => absurd (subset_closure hy.2) hy.1)

theorem ci_lower {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) (x : Fin n → ℝ) (hx : x ∈ G) (M : ℝ) (hM : M < f x) :
    ∃ ξ ∈ conjDomain G f, M ≤ ξ ⬝ᵥ x - conjFun G f ξ := by
  have hev : ∀ᶠ y in 𝓝[G] x, (M + f x) / 2 ≤ f y := by
    filter_upwards [hGf.2.2.1 x hx ((M + f x) / 2) (by linarith)] with y hy using hy.le
  have hn := ci_notin_of_ev G f x M ((M + f x) / 2) (by linarith) hev
  rcases ci_sep G f hGf.1 hGf.2.1 x M hn with h | ⟨a, u, h1, h2⟩
  · exact h
  · exact absurd (h1 x hx) (by linarith)

theorem ci_nonempty {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) : (conjDomain G f).Nonempty := by
  obtain ⟨x, hx⟩ := hGf.1
  obtain ⟨ξ, hξ, _⟩ := ci_lower G f hGf x hx (f x - 1) (by linarith)
  exact ⟨ξ, hξ⟩

theorem biconj_core {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    ∀ x₀ ∉ G,
      ¬ BddAbove ((fun ξ => ξ ⬝ᵥ x₀ - conjFun G f ξ) '' conjDomain G f) := by
  intro x₀ hx₀ ⟨B, hB⟩
  have hB' : ∀ ξ ∈ conjDomain G f, ξ ⬝ᵥ x₀ - conjFun G f ξ ≤ B := fun ξ hξ => hB ⟨ξ, hξ, rfl⟩
  rcases ci_sep G f hGf.1 hGf.2.1 x₀ (B + 1) (ci_notin_off G f hGf x₀ hx₀ (B + 1)) with
    ⟨ξ, hξ, h⟩ | ⟨a, u, h1, h2⟩
  · linarith [hB' ξ hξ]
  · obtain ⟨ξ₀, hξ₀⟩ := ci_nonempty G f hGf
    set C := ξ₀ ⬝ᵥ x₀ - conjFun G f ξ₀ with hC
    set lam := max 0 ((B - C + 1) / (x₀ ⬝ᵥ a - u)) with hlam
    have hlam0 : 0 ≤ lam := le_max_left _ _
    have hpos : 0 < x₀ ⬝ᵥ a - u := by linarith
    have hlam1 : B - C + 1 ≤ lam * (x₀ ⬝ᵥ a - u) := by
      have := mul_le_mul_of_nonneg_right (le_max_right 0 ((B - C + 1) / (x₀ ⬝ᵥ a - u)))
        hpos.le
      rw [div_mul_cancel₀ _ hpos.ne'] at this
      exact this
    have hb : ∀ x ∈ G, x ⬝ᵥ (ξ₀ + lam • a) - f x ≤ conjFun G f ξ₀ + lam * u := by
      intro x hx
      have := ci_le hξ₀ hx
      have := mul_le_mul_of_nonneg_left (h1 x hx).le hlam0
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
    obtain ⟨hmem, hle⟩ := ci_bound hGf.1 _ hb
    have := hB' _ hmem
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm a x₀] at this
    nlinarith

theorem ci_dot_cont {n : ℕ} (x : Fin n → ℝ) : Continuous fun ξ : Fin n → ℝ => x ⬝ᵥ ξ := by
  unfold dotProduct; fun_prop

theorem ci_ev {n : ℕ} {G : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ G) (ξ : Fin n → ℝ) (y : ℝ) (h : y < x ⬝ᵥ ξ - f x) :
    ∀ᶠ ξ' in 𝓝[conjDomain G f] ξ, y < conjFun G f ξ' := by
  have hc : Continuous fun ξ' : Fin n → ℝ => x ⬝ᵥ ξ' - f x :=
    (ci_dot_cont x).sub continuous_const
  have h1 : ∀ᶠ ξ' in 𝓝 ξ, y < x ⬝ᵥ ξ' - f x := continuousAt_const.eventually_lt hc.continuousAt h
  filter_upwards [mem_nhdsWithin_of_mem_nhds h1, self_mem_nhdsWithin] with ξ' h1 h2
  exact lt_of_lt_of_le h1 (ci_le h2 hx)

theorem ci_pair {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) : IsClosedConvexPair (conjDomain G f) (conjFun G f) := by
  have hG := hGf.1
  have hconv : ∀ ξ₁ ∈ conjDomain G f, ∀ ξ₂ ∈ conjDomain G f, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a • ξ₁ + b • ξ₂ ∈ conjDomain G f ∧
        conjFun G f (a • ξ₁ + b • ξ₂) ≤ a * conjFun G f ξ₁ + b * conjFun G f ξ₂ := by
    intro ξ₁ h₁ ξ₂ h₂ a b ha hb hab
    apply ci_bound hG
    intro x hx
    have e1 := mul_le_mul_of_nonneg_left (ci_le h₁ hx) ha
    have e2 := mul_le_mul_of_nonneg_left (ci_le h₂ hx) hb
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : f x = a * f x + b * f x := by rw [← add_mul, hab, one_mul]
    nlinarith
  refine ⟨ci_nonempty G f hGf, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro ξ₁ h₁ ξ₂ h₂ a b ha hb hab
    exact (hconv ξ₁ h₁ ξ₂ h₂ a b ha hb hab).1
  · intro ξ₁ h₁ ξ₂ h₂ a b ha hb hab
    simpa using (hconv ξ₁ h₁ ξ₂ h₂ a b ha hb hab).2
  · intro ξ hξ y hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hG.image _) hy
    exact ci_ev hx ξ y hlt
  · rintro ξ ⟨_, hξ⟩
    rw [tendsto_atTop]
    intro K
    have : ¬ BddAbove ((fun x => x ⬝ᵥ ξ - f x) '' G) := hξ
    rw [not_bddAbove_iff] at this
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := this K
    filter_upwards [ci_ev hx ξ K hlt] with ξ' h using h.le

theorem ci_biconj {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    conjDomain (conjDomain G f) (conjFun G f) = G ∧
      ∀ x ∈ G, conjFun (conjDomain G f) (conjFun G f) x = f x := by
  have hbd : ∀ x ∈ G, ∀ ξ ∈ conjDomain G f, ξ ⬝ᵥ x - conjFun G f ξ ≤ f x := by
    intro x hx ξ hξ
    have := ci_le hξ hx
    rw [dotProduct_comm] at this
    linarith
  have hsub : G ⊆ conjDomain (conjDomain G f) (conjFun G f) := by
    intro x hx
    exact ⟨f x, by rintro _ ⟨ξ, hξ, rfl⟩; exact hbd x hx ξ hξ⟩
  refine ⟨Set.Subset.antisymm ?_ hsub, ?_⟩
  · intro x hx
    by_contra hxG
    exact biconj_core G f hGf x hxG hx
  · intro x hx
    apply le_antisymm
    · exact (ci_bound (ci_nonempty G f hGf) (f x) (fun ξ hξ => hbd x hx ξ hξ)).2
    · apply le_of_forall_lt
      intro M hM
      obtain ⟨ξ, hξ, h⟩ := ci_lower G f hGf x hx ((M + f x) / 2) (by linarith)
      have := ci_le (G := conjDomain G f) (f := conjFun G f) (hsub hx) hξ
      linarith

theorem ci_congr {n : ℕ} (G : Set (Fin n → ℝ)) (f h : (Fin n → ℝ) → ℝ)
    (hfh : ∀ x ∈ G, h x = f x) :
    conjDomain G h = conjDomain G f ∧ conjFun G h = conjFun G f := by
  have : ∀ ξ, (fun x => x ⬝ᵥ ξ - h x) '' G = (fun x => x ⬝ᵥ ξ - f x) '' G := by
    intro ξ
    apply Set.image_congr
    intro x hx; rw [hfh x hx]
  constructor
  · ext ξ; simp only [conjDomain, Set.mem_ofPred_eq, this]
  · funext ξ; simp only [conjFun, this]

theorem goal_core {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    IsClosedConvexPair (conjDomain G f) (conjFun G f) ∧
    (∀ x ∈ G, ∀ ξ ∈ conjDomain G f, x ⬝ᵥ ξ ≤ f x + conjFun G f ξ) ∧
    (∀ x ∈ intrinsicInterior ℝ G, ∃ ξ ∈ conjDomain G f, x ⬝ᵥ ξ = f x + conjFun G f ξ) ∧
    conjDomain (conjDomain G f) (conjFun G f) = G ∧
    (∀ x ∈ G, conjFun (conjDomain G f) (conjFun G f) x = f x) ∧
    (∀ (Γ' : Set (Fin n → ℝ)) (φ' : (Fin n → ℝ) → ℝ), IsClosedConvexPair Γ' φ' →
      conjDomain Γ' φ' = G → (∀ x ∈ G, conjFun Γ' φ' x = f x) →
      Γ' = conjDomain G f ∧ ∀ ξ ∈ Γ', φ' ξ = conjFun G f ξ) := by
  obtain ⟨hd, he⟩ := ci_biconj G f hGf
  refine ⟨ci_pair G f hGf, ?_, ?_, hd, he, ?_⟩
  · intro x hx ξ hξ
    have := ci_le hξ hx
    linarith
  · intro x hx
    obtain ⟨ξ, hξ, h⟩ := ci_support G f hGf.2.1 x hx
    exact ⟨ξ, hξ, by linarith⟩
  · intro Γ' φ' hp h1 h2
    obtain ⟨hd', he'⟩ := ci_biconj Γ' φ' hp
    rw [h1] at hd' he'
    obtain ⟨c1, c2⟩ := ci_congr G f (conjFun Γ' φ') h2
    rw [c1] at hd'
    rw [c2] at he'
    exact ⟨hd'.symm, fun ξ hξ => (he' ξ hξ).symm⟩

end ConjugateConvex.Involution

open ConjugateConvex.Involution


theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    ∀ x₀ ∉ G,
      ¬ BddAbove ((fun ξ => ξ ⬝ᵥ x₀ - conjFun G f ξ) '' conjDomain G f) := by
  exact biconj_core G f hGf
