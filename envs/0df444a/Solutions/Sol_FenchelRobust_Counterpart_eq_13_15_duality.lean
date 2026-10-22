-- Prove2me | solution 1 for FenchelRobust.Counterpart.eq_13_15_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:22:31.595988+00:00
-- url     : https://prove2.me/submissions/0b775580-7921-4141-a748-0ddc1b95e42c

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model



namespace FenchelRobust.Counterpart

theorem fr_mem_ri_iff {n : ℕ} {G : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
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

theorem fr_segment_ri {n : ℕ} {G : Set (Fin n → ℝ)} (hG : Convex ℝ G) {x y : Fin n → ℝ}
    (hx : x ∈ G) (hy : y ∈ intrinsicInterior ℝ G) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • y ∈ intrinsicInterior ℝ G := by
  rw [fr_mem_ri_iff] at hy ⊢
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


theorem fr_rep {n : ℕ} (φ : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (x : Fin n → ℝ) (t : ℝ) :
    φ (x, t) = x ⬝ᵥ (fun i => φ ((fun j => if i = j then (1:ℝ) else 0), 0)) + t * φ (0, 1) := by
  have h1 : (x, t) = (x, (0:ℝ)) + t • ((0 : Fin n → ℝ), (1:ℝ)) := by ext <;> simp
  rw [h1, map_add, map_smul, smul_eq_mul]
  congr 1
  have := LinearMap.pi_apply_eq_sum_univ
    ((φ : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ).toLinearMap.comp (LinearMap.inl ℝ (Fin n → ℝ) ℝ)) x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
    ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this, dotProduct]

theorem fr_subgrad_interior {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
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
  have hrep : ∀ x t, φ (x, t) = x ⬝ᵥ a + t * c := fun x t => fr_rep φ x t
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

theorem fr_support_ineq {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ intrinsicInterior ℝ G) :
    ∃ ξ : Fin n → ℝ, ∀ x ∈ G, x ⬝ᵥ ξ - f x ≤ x₀ ⬝ᵥ ξ - f x₀ := by
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
    obtain ⟨_, ε, hε, hball⟩ := fr_mem_ri_iff.1 hy
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
  obtain ⟨ξ, hξ⟩ := fr_subgrad_interior _ _ hconv x₀ (hint x₀ hx₀)
  have hri : ∀ y ∈ intrinsicInterior ℝ G, y ⬝ᵥ ξ - f y ≤ x₀ ⬝ᵥ ξ - f x₀ := by
    intro y hy
    have := hξ y (hint y hy)
    simp only [Function.comp_apply, hAy y (intrinsicInterior_subset hy), hAy x₀ hx₀G] at this
    exact this
  have hall : ∀ x ∈ G, x ⬝ᵥ ξ - f x ≤ x₀ ⬝ᵥ ξ - f x₀ := by
    intro x hx
    have hz := fr_segment_ri hf.1 hx hx₀ (t := 1/2) (by norm_num) (by norm_num)
    have h1 := hri _ hz
    have h2 := hf.2 hx hx₀G (show (0:ℝ) ≤ 1 - 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (by norm_num)
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h1 h2
    linarith
  exact ⟨ξ, hall⟩

theorem fr_ri_W {m L : ℕ} (a0 : Fin m → ℝ) (A : Matrix (Fin m) (Fin L) ℝ)
    (Z : Set (Fin L → ℝ)) (D : Set (Fin m → ℝ))
    (hZ0 : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z) (ha0 : a0 ∈ intrinsicInterior ℝ D) :
    (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
      {w : Fin m → ℝ | ∃ d ∈ D, ∃ ζ ∈ Z, d + w = a0 + A.mulVec ζ} := by
  rw [fr_mem_ri_iff] at hZ0 ha0 ⊢
  obtain ⟨hZ0m, ε1, hε1, h1⟩ := hZ0
  obtain ⟨ha0D, ε2, hε2, h2⟩ := ha0
  set W : Set (Fin m → ℝ) := {w : Fin m → ℝ | ∃ d ∈ D, ∃ ζ ∈ Z, d + w = a0 + A.mulVec ζ} with hWdef
  set V1 := (affineSpan ℝ Z).direction with hV1
  set V2 := (affineSpan ℝ D).direction with hV2
  let Φ : (V1 × V2) →ₗ[ℝ] (Fin m → ℝ) :=
    A.mulVecLin.comp (V1.subtype.comp (LinearMap.fst ℝ V1 V2)) -
      V2.subtype.comp (LinearMap.snd ℝ V1 V2)
  have hΦ : ∀ p : V1 × V2, Φ p = A.mulVec (p.1 : Fin L → ℝ) - (p.2 : Fin m → ℝ) := by
    intro p; rfl
  have hWmem : ∀ w ∈ W, w ∈ LinearMap.range Φ := by
    rintro w ⟨d, hd, ζ, hζ, hw⟩
    have e1 : ζ ∈ V1 := by
      have := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ Z hζ)
        (subset_affineSpan ℝ Z hZ0m)
      simpa using this
    have e2 : d - a0 ∈ V2 :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ D hd) (subset_affineSpan ℝ D ha0D)
    refine ⟨(⟨ζ, e1⟩, ⟨d - a0, e2⟩), ?_⟩
    rw [hΦ]
    simp only
    have : w = a0 + A.mulVec ζ - d := by rw [← hw]; abel
    rw [this]; abel
  have hdir : (affineSpan ℝ W).direction ≤ LinearMap.range Φ := by
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro _ ⟨w1, hw1, w2, hw2, rfl⟩
    exact sub_mem (hWmem w1 hw1) (hWmem w2 hw2)
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective Φ.rangeRestrict
    (LinearMap.range_eq_top.2 Φ.surjective_rangeRestrict)
  let Rc : (LinearMap.range Φ) →L[ℝ] (V1 × V2) := LinearMap.toContinuousLinearMap R
  set K := ‖Rc‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg Rc
  refine ⟨⟨a0, ha0D, 0, hZ0m, by simp⟩, min ε1 ε2 / (K + 1), ?_, fun u hu hun => ?_⟩
  · exact div_pos (lt_min hε1 hε2) (by linarith)
  · have huR : u ∈ LinearMap.range Φ := hdir hu
    have hr := LinearMap.congr_fun hR ⟨u, huR⟩
    set r := R ⟨u, huR⟩ with hrdef
    have hΦr : Φ r = u := by
      have := congrArg Subtype.val hr
      simpa [LinearMap.rangeRestrict] using this
    have hbound : ‖r‖ ≤ K * ‖u‖ := by
      have := Rc.le_opNorm ⟨u, huR⟩
      simpa [Rc, hrdef, hK] using this
    have hlt : (K + 1) * ‖u‖ < min ε1 ε2 := by
      rw [lt_div_iff₀ (by linarith)] at hun
      linarith
    have hKu : K * ‖u‖ ≤ (K + 1) * ‖u‖ := by nlinarith [norm_nonneg u]
    have hp : ‖(r.1 : Fin L → ℝ)‖ < ε1 := by
      have : ‖r.1‖ ≤ ‖r‖ := norm_fst_le r
      have h3 : ‖(r.1 : Fin L → ℝ)‖ = ‖r.1‖ := rfl
      have := min_le_left ε1 ε2
      linarith
    have hq : ‖(r.2 : Fin m → ℝ)‖ < ε2 := by
      have : ‖r.2‖ ≤ ‖r‖ := norm_snd_le r
      have h3 : ‖(r.2 : Fin m → ℝ)‖ = ‖r.2‖ := rfl
      have := min_le_right ε1 ε2
      linarith
    have hz := h1 _ r.1.2 hp
    have hd := h2 _ r.2.2 hq
    refine ⟨a0 + (r.2 : Fin m → ℝ), hd, 0 + (r.1 : Fin L → ℝ), hz, ?_⟩
    rw [hΦ] at hΦr
    have : u = A.mulVec (r.1 : Fin L → ℝ) - (r.2 : Fin m → ℝ) := hΦr.symm
    rw [zero_add, zero_add, this]; abel


noncomputable def frPsi {m : ℕ} (S D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ)
    (w : Fin m → ℝ) : ℝ :=
  sSup (g '' {d | d ∈ D ∧ d + w ∈ S})

theorem fr_bdd {m : ℕ} (S D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (a0 : Fin m → ℝ)
    (hSc : IsCompact S) (hg : ConcaveOn ℝ D g) (ha0 : a0 ∈ intrinsicInterior ℝ D)
    (w : Fin m → ℝ) : BddAbove (g '' {d | d ∈ D ∧ d + w ∈ S}) := by
  obtain ⟨ξ, hξ⟩ := fr_support_ineq D (-g) hg.neg a0 ha0
  have hcont : Continuous fun s : Fin m → ℝ => g a0 + (a0 - (s - w)) ⬝ᵥ ξ := by
    unfold dotProduct
    fun_prop
  obtain ⟨M, hM⟩ := hSc.bddAbove_image hcont.continuousOn
  refine ⟨M, ?_⟩
  rintro _ ⟨d, ⟨hd, hds⟩, rfl⟩
  have h1 := hξ d hd
  simp only [Pi.neg_apply, neg_neg] at h1
  have h2 : g a0 + (a0 - (d + w - w)) ⬝ᵥ ξ ≤ M := hM ⟨d + w, hds, rfl⟩
  have h3 : (a0 - (d + w - w)) ⬝ᵥ ξ = a0 ⬝ᵥ ξ - d ⬝ᵥ ξ := by
    rw [add_sub_cancel_right, sub_dotProduct]
  rw [h3] at h2
  linarith

theorem fr_psi_ge {m : ℕ} (S D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (a0 : Fin m → ℝ)
    (hSc : IsCompact S) (hg : ConcaveOn ℝ D g) (ha0 : a0 ∈ intrinsicInterior ℝ D)
    (w d : Fin m → ℝ) (hd : d ∈ D) (hds : d + w ∈ S) : g d ≤ frPsi S D g w :=
  le_csSup (fr_bdd S D g a0 hSc hg ha0 w) ⟨d, ⟨hd, hds⟩, rfl⟩

theorem fr_psi_convex {m : ℕ} (S D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (a0 : Fin m → ℝ)
    (hSc : IsCompact S) (hSconv : Convex ℝ S) (hDconv : Convex ℝ D)
    (hg : ConcaveOn ℝ D g) (ha0 : a0 ∈ intrinsicInterior ℝ D) :
    ConvexOn ℝ {w | ∃ d ∈ D, d + w ∈ S} (fun w => - frPsi S D g w) := by
  have hne : ∀ w ∈ {w | ∃ d ∈ D, d + w ∈ S},
      (g '' {d | d ∈ D ∧ d + w ∈ S}).Nonempty := by
    rintro w ⟨d, hd, hds⟩
    exact ⟨g d, d, ⟨hd, hds⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro x ⟨dx, hdx, hx⟩ y ⟨dy, hdy, hy⟩ a b ha hb hab
    refine ⟨a • dx + b • dy, hDconv hdx hdy ha hb hab, ?_⟩
    have := hSconv hx hy ha hb hab
    convert this using 1
    simp only [smul_add]
    module
  · rintro x hx y hy a b ha hb hab
    have hxy : a • x + b • y ∈ {w | ∃ d ∈ D, d + w ∈ S} := by
      obtain ⟨dx, hdx, hx'⟩ := hx
      obtain ⟨dy, hdy, hy'⟩ := hy
      refine ⟨a • dx + b • dy, hDconv hdx hdy ha hb hab, ?_⟩
      have := hSconv hx' hy' ha hb hab
      convert this using 1
      simp only [smul_add]
      module
    simp only [smul_eq_mul]
    have key : a * frPsi S D g x + b * frPsi S D g y ≤ frPsi S D g (a • x + b • y) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have h1 : frPsi S D g x - ε < sSup (g '' {d | d ∈ D ∧ d + x ∈ S}) := by
        unfold frPsi; linarith
      have h2 : frPsi S D g y - ε < sSup (g '' {d | d ∈ D ∧ d + y ∈ S}) := by
        unfold frPsi; linarith
      obtain ⟨_, ⟨d1, ⟨hd1, hd1s⟩, rfl⟩, hlt1⟩ := exists_lt_of_lt_csSup (hne x hx) h1
      obtain ⟨_, ⟨d2, ⟨hd2, hd2s⟩, rfl⟩, hlt2⟩ := exists_lt_of_lt_csSup (hne y hy) h2
      have hmem : a • d1 + b • d2 ∈ D := hDconv hd1 hd2 ha hb hab
      have hS : (a • d1 + b • d2) + (a • x + b • y) ∈ S := by
        have := hSconv hd1s hd2s ha hb hab
        convert this using 1
        simp only [smul_add]
        module
      have hle := fr_psi_ge S D g a0 hSc hg ha0 _ _ hmem hS
      have hcc := hg.2 hd1 hd2 ha hb hab
      simp only [smul_eq_mul] at hcc
      nlinarith [mul_le_mul_of_nonneg_left hlt1.le ha, mul_le_mul_of_nonneg_left hlt2.le hb]
    linarith

theorem fr_core {m : ℕ} (S D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (a0 : Fin m → ℝ)
    (hSc : IsCompact S) (hSconv : Convex ℝ S) (hDconv : Convex ℝ D)
    (hg : ConcaveOn ℝ D g) (ha0 : a0 ∈ intrinsicInterior ℝ D)
    (h0 : (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ {w | ∃ d ∈ D, d + w ∈ S}) :
    ∃ v : Fin m → ℝ, ∀ d ∈ D, ∀ s ∈ S,
      g d + v ⬝ᵥ s - v ⬝ᵥ d ≤ sSup (g '' {d | d ∈ D ∧ d + 0 ∈ S}) := by
  obtain ⟨ξ, hξ⟩ := fr_support_ineq _ _ (fr_psi_convex S D g a0 hSc hSconv hDconv hg ha0) 0 h0
  refine ⟨ξ, fun d hd s hs => ?_⟩
  have hw : s - d ∈ {w | ∃ d ∈ D, d + w ∈ S} := ⟨d, hd, by simpa using hs⟩
  have h1 := hξ _ hw
  simp only [zero_dotProduct, neg_neg, zero_sub, sub_neg_eq_add] at h1
  have h2 := fr_psi_ge S D g a0 hSc hg ha0 (s - d) d hd (by simpa using hs)
  rw [sub_dotProduct] at h1
  have h3 : frPsi S D g 0 = sSup (g '' {d | d ∈ D ∧ d + 0 ∈ S}) := rfl
  have e1 := dotProduct_comm ξ s
  have e2 := dotProduct_comm ξ d
  linarith


theorem fr_support_eq {m : ℕ} (S : Set (Fin m → ℝ)) (hSc : IsCompact S) (hSne : S.Nonempty)
    (u : Fin m → ℝ) :
    ∃ s ∈ S, (∀ t ∈ S, u ⬝ᵥ t ≤ u ⬝ᵥ s) ∧ supportFun S u = ((u ⬝ᵥ s : ℝ) : EReal) := by
  have hc : ContinuousOn (fun t : Fin m → ℝ => u ⬝ᵥ t) S := by
    apply Continuous.continuousOn
    unfold dotProduct
    fun_prop
  obtain ⟨s, hs, hmax⟩ := hSc.exists_isMaxOn hSne hc
  refine ⟨s, hs, fun t ht => hmax ht, ?_⟩
  unfold supportFun
  apply le_antisymm
  · exact iSup₂_le fun a ha => EReal.coe_le_coe_iff.2 (hmax ha)
  · exact le_iSup₂ (f := fun a (_ : a ∈ S) => ((u ⬝ᵥ a : ℝ) : EReal)) s hs

theorem fr_conj_bdd {m : ℕ} (D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ)
    (hDne : D.Nonempty) (hb : BddBelow ((fun a => a ⬝ᵥ u - g a) '' D)) :
    concaveConj D g u = ((sInf ((fun a => a ⬝ᵥ u - g a) '' D) : ℝ) : EReal) := by
  unfold concaveConj
  set ρ := sInf ((fun a => a ⬝ᵥ u - g a) '' D) with hρ
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hrle : r ≤ ρ := by
      apply le_csInf (hDne.image _)
      rintro _ ⟨a, ha, rfl⟩
      have : (r : EReal) ≤ ((a ⬝ᵥ u - g a : ℝ) : EReal) :=
        hr2.le.trans (iInf₂_le a ha)
      exact EReal.coe_le_coe_iff.1 this
    have := EReal.coe_lt_coe_iff.1 hr1
    linarith
  · refine le_iInf₂ fun a ha => ?_
    exact EReal.coe_le_coe_iff.2 (csInf_le hb ⟨a, ha, rfl⟩)

theorem fr_conj_unbdd {m : ℕ} (D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ)
    (hb : ¬ BddBelow ((fun a => a ⬝ᵥ u - g a) '' D)) :
    concaveConj D g u = ⊥ := by
  unfold concaveConj
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  rw [not_bddBelow_iff] at hb
  obtain ⟨_, ⟨a, ha, rfl⟩, hlt⟩ := hb r
  exact lt_of_le_of_lt (iInf₂_le a ha) (EReal.coe_lt_coe_iff.2 hlt)

theorem fr_main {m : ℕ} (S D : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (a0 : Fin m → ℝ)
    (hSc : IsCompact S) (hSconv : Convex ℝ S) (hDconv : Convex ℝ D)
    (hg : ConcaveOn ℝ D g) (ha0 : a0 ∈ intrinsicInterior ℝ D) (ha0S : a0 ∈ S)
    (h0 : (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ {w | ∃ d ∈ D, d + w ∈ S}) :
    let F := ⨆ a ∈ S ∩ D, (g a : EReal)
    let dual := fun v : Fin m → ℝ => supportFun S v - concaveConj D g v
    F = (⨅ v, dual v) ∧ ∃ v, F = dual v := by
  intro F dual
  have ha0D : a0 ∈ D := intrinsicInterior_subset ha0
  have hSne : S.Nonempty := ⟨a0, ha0S⟩
  have hDne : D.Nonempty := ⟨a0, ha0D⟩
  have hset : {d | d ∈ D ∧ d + 0 ∈ S} = S ∩ D := by
    ext d; simp [and_comm]
  have hcore := fr_core S D g a0 hSc hSconv hDconv hg ha0 h0
  rw [hset] at hcore
  obtain ⟨v, hv⟩ := hcore
  have hbdd : BddAbove (g '' (S ∩ D)) := by
    have := fr_bdd S D g a0 hSc hg ha0 0
    rwa [hset] at this
  set Fr := sSup (g '' (S ∩ D)) with hFr
  have hne : (g '' (S ∩ D)).Nonempty := ⟨g a0, a0, ⟨ha0S, ha0D⟩, rfl⟩
  have hFE : F = ((Fr : ℝ) : EReal) := by
    apply le_antisymm
    · exact iSup₂_le fun a ha => EReal.coe_le_coe_iff.2 (le_csSup hbdd ⟨a, ha, rfl⟩)
    · by_contra hlt
      rw [not_le] at hlt
      obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
      have hrle : Fr ≤ r := by
        apply csSup_le hne
        rintro _ ⟨a, ha, rfl⟩
        have : ((g a : ℝ) : EReal) ≤ (r : EReal) :=
          (le_iSup₂ (f := fun a (_ : a ∈ S ∩ D) => ((g a : ℝ) : EReal)) a ha).trans hr1.le
        exact EReal.coe_le_coe_iff.1 this
      have := EReal.coe_lt_coe_iff.1 hr2
      linarith
  have weak : ∀ u, F ≤ dual u := by
    intro u
    obtain ⟨s, hs, hmax, hsup⟩ := fr_support_eq S hSc hSne u
    show F ≤ supportFun S u - concaveConj D g u
    rw [hsup, hFE]
    by_cases hb : BddBelow ((fun a => a ⬝ᵥ u - g a) '' D)
    · rw [fr_conj_bdd D g u hDne hb, ← EReal.coe_sub]
      apply EReal.coe_le_coe_iff.2
      apply csSup_le hne
      rintro _ ⟨a, ⟨haS, haD⟩, rfl⟩
      have h1 := csInf_le hb ⟨a, haD, rfl⟩
      have h2 := hmax a haS
      have h3 := dotProduct_comm u a
      simp only at h1
      linarith
    · rw [fr_conj_unbdd D g u hb]
      simp
  have strong : dual v ≤ F := by
    obtain ⟨s, hs, hmax, hsup⟩ := fr_support_eq S hSc hSne v
    show supportFun S v - concaveConj D g v ≤ F
    rw [hsup, hFE]
    have hb : BddBelow ((fun a => a ⬝ᵥ v - g a) '' D) := by
      refine ⟨v ⬝ᵥ s - Fr, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      have := hv d hd s hs
      have h3 := dotProduct_comm v d
      simp only
      linarith
    rw [fr_conj_bdd D g v hDne hb, ← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.2
    have : v ⬝ᵥ s - Fr ≤ sInf ((fun a => a ⬝ᵥ v - g a) '' D) := by
      apply le_csInf (hDne.image _)
      rintro _ ⟨d, hd, rfl⟩
      have := hv d hd s hs
      have h3 := dotProduct_comm v d
      simp only
      linarith
    linarith
  exact ⟨le_antisymm (le_iInf weak) ((iInf_le _ v).trans strong),
    v, le_antisymm (weak v) strong⟩

theorem eq1315_core {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hZnonempty : Z.Nonempty) (hZconvex : Convex ℝ Z) (hZcompact : IsCompact Z)
    (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hconcave : ∀ x, ConcaveOn ℝ (D x) (fun a => f a x))
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      let F := worstCase a0 A Z D f x
      let dual := fun v : Fin m → ℝ =>
        supportFun (uncertaintySet a0 A Z) v - concaveConj (D x) (fun a => f a x) v
      F = (⨅ v, dual v) ∧ ∃ v, F = dual v := by
  intro x
  have hSdef : uncertaintySet a0 A Z = (fun ζ => a0 + A.mulVec ζ) '' Z := by
    ext a; simp [uncertaintySet, eq_comm]
  have hSc : IsCompact (uncertaintySet a0 A Z) := by
    rw [hSdef]
    apply hZcompact.image
    exact continuous_const.add (Continuous.matrix_mulVec continuous_const continuous_id)
  have hSconv : Convex ℝ (uncertaintySet a0 A Z) := by
    rintro _ ⟨ζ1, h1, rfl⟩ _ ⟨ζ2, h2, rfl⟩ s t hs ht hst
    refine ⟨s • ζ1 + t • ζ2, hZconvex h1 h2 hs ht hst, ?_⟩
    obtain rfl : t = 1 - s := by linarith
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [smul_add]
    module
  have ha0S : a0 ∈ uncertaintySet a0 A Z :=
    ⟨0, intrinsicInterior_subset hZzero, by simp⟩
  exact fr_main (uncertaintySet a0 A Z) (D x) (fun a => f a x) a0 hSc hSconv (hconcave x).1
    (hconcave x) (hregular x) ha0S (fr_ri_W a0 A Z (D x) hZzero (hregular x))

end FenchelRobust.Counterpart

open FenchelRobust.Counterpart


theorem solution {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hZnonempty : Z.Nonempty) (hZconvex : Convex ℝ Z) (hZcompact : IsCompact Z)
    (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hconcave : ∀ x, ConcaveOn ℝ (D x) (fun a => f a x))
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      let F := worstCase a0 A Z D f x
      let dual := fun v : Fin m → ℝ =>
        supportFun (uncertaintySet a0 A Z) v - concaveConj (D x) (fun a => f a x) v
      F = (⨅ v, dual v) ∧ ∃ v, F = dual v := by
  exact eq1315_core a0 A Z D f hZnonempty hZconvex hZcompact hZzero hconcave hregular
