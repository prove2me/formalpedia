-- Prove2me | solution 1 for FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:37:46.667803+00:00
-- url     : https://prove2.me/submissions/ca93ee68-a0b4-44b6-9a22-e81ecd4873cd

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_exists_affine_normalization_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_compact_sections_subset_and_shrink_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_pos_alexandrov_maximum_principle_readable
import Theorems.Thm_FunctionalInequalities_Analysis_infDist_frontier_image_le_of_width_readable
import Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_comp_affineEquiv_symm_readable
import Theorems.Thm_FunctionalInequalities_Analysis_contact_stepA_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11E7LocalizedContactLemma
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.contact_sub_affine_convex {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    (c : ℝ) (p : E) :
    ConvexOn ℝ univ (fun x => u x - (c + ⟪p, x⟫)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hu.2 hx hy ha hb hab
  have hconst : a * c + b * c = c := by
    calc
      a * c + b * c = (a + b) * c := by ring
      _ = c := by rw [hab, one_mul]
  simp only [inner_add_right, real_inner_smul_right, smul_eq_mul] at h ⊢
  nlinarith only [h, hconst]
private lemma FunctionalInequalities.Analysis.contact_subgradientImage_sub_affine
    (u : E → ℝ) (c : ℝ) (p : E) (G : Set E) :
    subgradientImage (fun x => u x - (c + ⟪p, x⟫)) G =
      (fun q => q + -p) '' subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨q + p, ⟨x, hx, ?_⟩, by abel⟩
    intro y
    have h := hq y
    simp only [inner_add_left, inner_sub_right] at h ⊢
    linarith
  · rintro ⟨q, ⟨x, hx, hq⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hq y
    simp only [inner_add_left, inner_neg_left, inner_sub_right] at h ⊢
    linarith
section FiniteDimensional
variable [FiniteDimensional ℝ E]
section MeasurableSpace
variable [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.contact_volume_sub_affine
    (u : E → ℝ) (c : ℝ) (p : E) (G : Set E) :
    (volume : Measure E)
        (subgradientImage (fun x => u x - (c + ⟪p, x⟫)) G) =
      volume (subgradientImage u G) := by
  rw [contact_subgradientImage_sub_affine, Set.image_add_right,
    measure_preimage_add_right]
private lemma FunctionalInequalities.Analysis.contact_affine_volume (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (e '' G) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)| * volume G := by
  have he (x : E) : e x = e.linear x + e 0 := by
    simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : E) x
  have himage :
      e '' G = (fun x => x + e 0) '' ((e.linear : E →ₗ[ℝ] E) '' G) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact he x
  rw [himage, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap]
end MeasurableSpace
private lemma FunctionalInequalities.Analysis.contact_det_pos
    (e : E ≃ᵃ[ℝ] E) :
    0 < |LinearMap.det (e.linear : E →ₗ[ℝ] E)| := by
  classical
  apply abs_pos.mpr
  have h := (e.linear.isUnit_det (Module.finBasis ℝ E)
    (Module.finBasis ℝ E)).ne_zero
  simpa only [LinearMap.det_toMatrix] using h
private lemma FunctionalInequalities.Analysis.contact_real_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {G A : Set E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hG : μ G ≠ ∞)
    (hlo : ENNReal.ofReal a * μ G ≤ μ A)
    (hhi : μ A ≤ ENNReal.ofReal b * μ G) :
    μ A ≠ ∞ ∧
      a * (μ G).toReal ≤ (μ A).toReal ∧
      (μ A).toReal ≤ b * (μ G).toReal := by
  have hprod : ENNReal.ofReal b * μ G ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  have hA : μ A ≠ ∞ := ne_top_of_le_ne_top hprod hhi
  refine ⟨hA, ?_, ?_⟩
  · have h := ENNReal.toReal_mono hA hlo
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] using h
  · have h := ENNReal.toReal_mono hprod hhi
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] using h
private lemma FunctionalInequalities.Analysis.contact_transport_real_bounds
    [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) (a b : ℝ)
    (hfin : (volume : Measure E) (subgradientImage u G) ≠ ∞)
    (hlo : a * ((volume : Measure E) G).toReal ≤
      (volume (subgradientImage u G)).toReal)
    (hhi : (volume (subgradientImage u G)).toReal ≤
      b * ((volume : Measure E) G).toReal) :
    let D := |LinearMap.det (e.linear : E →ₗ[ℝ] E)|
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) ≠ ∞ ∧
      (a / D ^ 2) * (volume (e '' G)).toReal ≤
        (volume (subgradientImage (u ∘ e.symm) (e '' G))).toReal ∧
      (volume (subgradientImage (u ∘ e.symm) (e '' G))).toReal ≤
        (b / D ^ 2) * (volume (e '' G)).toReal := by
  let D := |LinearMap.det (e.linear : E →ₗ[ℝ] E)|
  have hD : 0 < D := contact_det_pos e
  have hvol :
      ((volume : Measure E) (e '' G)).toReal =
        D * (volume G).toReal := by
    have h := congrArg ENNReal.toReal (contact_affine_volume e G)
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h
  have hgrad :
      ((volume : Measure E)
          (subgradientImage (u ∘ e.symm) (e '' G))).toReal =
        D⁻¹ * (volume (subgradientImage u G)).toReal := by
    have h := congrArg ENNReal.toReal
      (volume_subgradientImage_comp_affineEquiv_symm_readable u e G)
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))] using h
  have hid (r V : ℝ) :
      r / D ^ 2 * (D * V) = D⁻¹ * (r * V) := by
    field_simp [ne_of_gt hD]
  refine ⟨?_, ?_, ?_⟩
  · rw [volume_subgradientImage_comp_affineEquiv_symm_readable]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  · change a / D ^ 2 * _ ≤ _
    rw [hvol, hgrad, hid]
    exact mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hD.le)
  · change _ ≤ b / D ^ 2 * _
    rw [hvol, hgrad, hid]
    exact mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hD.le)
private lemma FunctionalInequalities.Analysis.contact_stepB
    [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {S : Set E} {x : E} {c t C A B R : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hC : 0 < C) (hR : 0 ≤ R)
    (himage : S ⊆ closedBall (0 : E) C)
    (hfinite : (volume : Measure E) (subgradientImage v S) ≠ ∞)
    (hmaximum :
      ENNReal.ofReal (c * t ^ Module.finrank ℝ E) ≤
        (volume : Measure E) (subgradientImage v S) *
          ENNReal.ofReal
            (diam S ^ (Module.finrank ℝ E - 1) * infDist x (frontier S)))
    (hupper : ((volume : Measure E) (subgradientImage v S)).toReal ≤
      B * (volume (closedBall (0 : E) C)).toReal)
    (hA : A ≤ (8 * t) ^ Module.finrank ℝ E)
    (hBA : B ≤ R * A) :
    c ≤
      (R * 8 ^ Module.finrank ℝ E *
          ((volume : Measure E) (closedBall (0 : E) C)).toReal *
          (2 * C) ^ (Module.finrank ℝ E - 1)) *
        infDist x (frontier S) := by
  let n := Module.finrank ℝ E
  let V := ((volume : Measure E) (closedBall (0 : E) C)).toReal
  let d := infDist x (frontier S)
  have hd : 0 ≤ d := infDist_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfinite ENNReal.ofReal_ne_top) hmaximum
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ c * t ^ Module.finrank ℝ E),
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg diam_nonneg _) infDist_nonneg)] at hreal
  have hB : B ≤ R * (8 * t) ^ n :=
    hBA.trans (mul_le_mul_of_nonneg_left hA hR)
  have hJ :
      ((volume : Measure E) (subgradientImage v S)).toReal ≤
        (R * (8 * t) ^ n) * V :=
    hupper.trans (mul_le_mul_of_nonneg_right hB hV)
  have hdiam : diam S ^ (n - 1) ≤ (2 * C) ^ (n - 1) :=
    pow_le_pow_left₀ diam_nonneg (diam_le_of_subset_closedBall hC.le himage) _
  have hfinal :
      c * t ^ n ≤
        (R * 8 ^ n * V * (2 * C) ^ (n - 1) * d) * t ^ n := by
    calc
      c * t ^ n ≤
          ((volume : Measure E) (subgradientImage v S)).toReal *
            (diam S ^ (n - 1) * d) := hreal
      _ ≤ ((R * (8 * t) ^ n) * V) * ((2 * C) ^ (n - 1) * d) :=
        mul_le_mul hJ (mul_le_mul_of_nonneg_right hdiam hd)
          (mul_nonneg (pow_nonneg diam_nonneg _) hd) (by positivity)
      _ = (R * 8 ^ n * V * (2 * C) ^ (n - 1) * d) * t ^ n := by
        rw [mul_pow]
        ring
  exact le_of_mul_le_mul_right hfinal (pow_pos ht n)
private lemma FunctionalInequalities.Analysis.contact_stepC_choose {c C h K : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hh : 0 < h) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ h ∧ K * (2 * C * δ / (h / 2)) < c := by
  let L : ℝ := K * (2 * C / (h / 2))
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hL1 : 0 < L + 1 := by linarith
  let δ : ℝ := min h (c / (L + 1)) / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact half_pos (lt_min hh (div_pos hc hL1))
  have hδh : δ ≤ h := by
    have hm := min_le_left h (c / (L + 1))
    dsimp only [δ]
    linarith
  have hδc : δ < c / (L + 1) := by
    have hm := min_le_right h (c / (L + 1))
    have hp := div_pos hc hL1
    dsimp only [δ]
    linarith
  have hmul := (lt_div_iff₀ hL1).mp hδc
  refine ⟨δ, hδ, hδh, ?_⟩
  have hid : K * (2 * C * δ / (h / 2)) = L * δ := by
    dsimp only [L]
    ring
  rw [hid]
  nlinarith
section MeasurableSpace
variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 4000000 in
/-- **Caffarelli's contact-set lemma, localised form** (weak Letwin route): let `C` be the
compact contact set of a supporting affine function of the convex `u`, `z ∈ C` strictly exposed in the unit
direction `θ`, `h > 0`, and suppose the two-sided Alexandrov bounds hold only on compact subsets of an open `U`
containing the slab piece `C ∩ {⟪· − z, θ⟫ ≥ −h}`. Then `C = {z}`. -/
theorem solution {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫})
    {z θ : E} (hz : u z = u x₀ + ⟪p, z - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ z → ⟪x - z, θ⟫ < 0) {h : ℝ} (hh : 0 < h)
    {U : Set E} (hU : IsOpen U)
    (hCU : {x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U)
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ U → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G →
      closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ∧
      (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
    {x | u x = u x₀ + ⟪p, x - x₀⟫} = {z} := by
  classical
  by_contra hnot
  let C : Set E := {x | u x = u x₀ + ⟪p, x - x₀⟫}
  let xe : E := z
  have hxe : xe ∈ C := hz
  obtain ⟨x₁, hx₁, hx₁ne⟩ : ∃ x₁ ∈ C, x₁ ≠ xe := by
    by_contra hn
    apply hnot
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hz, ?_⟩
    intro x hx
    by_contra hne
    exact hn ⟨x, hx, hne⟩
  have hx₁pair : ⟪x₁ - xe, θ⟫ < 0 := hexp x₁ hx₁ hx₁ne
  have hcontactWidth (x : E) (hx : x ∈ C) : ⟪x - xe, θ⟫ ≤ 0 := by
    by_cases he : x = xe
    · simp only [he, sub_self, inner_zero_left, le_refl]
    · exact (hexp x hx he).le
  let c₀ : ℝ := u x₀ - ⟪p, x₀⟫
  let w : E → ℝ := fun x => u x - (c₀ + ⟪p, x⟫)
  have hw_eq (x : E) :
      w x = u x - (u x₀ + ⟪p, x - x₀⟫) := by
    dsimp only [w, c₀]
    rw [inner_sub_right]
    ring
  have hw_nonneg (x : E) : 0 ≤ w x := by
    rw [hw_eq]
    exact sub_nonneg.mpr (hp x)
  have hw_zero_iff (x : E) : w x = 0 ↔ x ∈ C := by
    rw [hw_eq]
    exact sub_eq_zero
  have hwxe : w xe = 0 := (hw_zero_iff xe).mpr hxe
  have hwx₁ : w x₁ = 0 := (hw_zero_iff x₁).mpr hx₁
  have hwconv : ConvexOn ℝ univ w := FunctionalInequalities.Analysis.contact_sub_affine_convex hconv c₀ p
  let s : ℝ := min (1 / 2) (h / (2 * |⟪x₁ - xe, θ⟫|))
  have habs : 0 < |⟪x₁ - xe, θ⟫| := abs_pos.mpr hx₁pair.ne
  have hs : 0 < s := by
    dsimp only [s]
    exact lt_min (by norm_num) (div_pos hh (mul_pos (by norm_num) habs))
  have hsone : s ≤ 1 := by
    have hs' : s ≤ 1 / 2 := min_le_left _ _
    linarith
  have hswidth : s * (2 * |⟪x₁ - xe, θ⟫|) ≤ h :=
    (le_div_iff₀ (mul_pos (by norm_num) habs)).mp (min_le_right _ _)
  let y : E := xe + s • (x₁ - xe)
  have hyC : y ∈ C := by
    have hyform : (1 - s) • xe + s • x₁ = y := by
      dsimp only [y]
      module
    have hc := hwconv.2 (mem_univ xe) (mem_univ x₁)
      (sub_nonneg.mpr hsone) hs.le (by ring : (1 - s) + s = 1)
    rw [hyform, hwxe, hwx₁] at hc
    simp only [smul_zero, add_zero] at hc
    exact (hw_zero_iff y).mp (le_antisymm hc (hw_nonneg y))
  have hypair_raw : ⟪y - xe, θ⟫ = s * ⟪x₁ - xe, θ⟫ := by
    dsimp only [y]
    rw [add_sub_cancel_left, real_inner_smul_left]
  let β : ℝ := -⟪y - xe, θ⟫
  have hβeq : β = s * |⟪x₁ - xe, θ⟫| := by
    dsimp only [β]
    rw [hypair_raw, abs_of_neg hx₁pair]
    ring
  have hβ : 0 < β := by
    rw [hβeq]
    exact mul_pos hs habs
  have hβhalf : β ≤ h / 2 := by
    rw [hβeq]
    nlinarith only [hswidth]
  have hypair : ⟪y - xe, θ⟫ = -β := by
    dsimp only [β]
    ring
  let P : Set E := C ∩ {x | -h ≤ ⟪x - xe, θ⟫}
  have hPcompact : IsCompact P :=
    hC.inter_right (isClosed_le continuous_const (by fun_prop))
  have hPne : P.Nonempty := by
    refine ⟨xe, hxe, ?_⟩
    change -h ≤ ⟪xe - xe, θ⟫
    simp only [sub_self, inner_zero_left]
    linarith
  obtain ⟨δ', hδ', hQU⟩ :=
    hPcompact.exists_cthickening_subset_open hU hCU
  let Q : Set E := cthickening δ' P
  have hQ : IsCompact Q := hPcompact.cthickening
  obtain ⟨⟨Q₀, hQ₀, ε₀, hε₀, hQ₀sub⟩, hshrink⟩ :=
    FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink_readable hconv hp hC hxe hθ hexp hh
  obtain ⟨a, b₀, ha, hbounds⟩ := hB Q hQ hQU
  let b : ℝ := max b₀ 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right b₀ 1)
  obtain ⟨C₀, hC₀, hnormalize⟩ := FunctionalInequalities.Analysis.exists_affine_normalization_readable (E := E)
  obtain ⟨c, hc, hmaximum⟩ := FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_readable (E := E)
  let n := Module.finrank ℝ E
  let R : ℝ := b / a
  have hR : 0 ≤ R := (div_pos hb ha).le
  let K : ℝ :=
    R * 8 ^ n * ((volume : Measure E) (closedBall (0 : E) C₀)).toReal *
      (2 * C₀) ^ (n - 1)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  obtain ⟨δ, hδ, hδβ, hδsmall⟩ :=
    FunctionalInequalities.Analysis.contact_stepC_choose hc hC₀ (show 0 < 2 * β by positivity) hK
  have hδh : δ ≤ h := by linarith
  have htwoβ : 2 * β / 2 = β := by ring
  rw [htwoβ] at hδsmall
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := hshrink (min δ δ') (lt_min hδ hδ')
  let ε : ℝ := min ε₀ ε₁ / 2
  have hε : 0 < ε := half_pos (lt_min hε₀ hε₁)
  have hεsmall₀ : ε < ε₀ := by
    have hm := min_le_left ε₀ ε₁
    dsimp only [ε]
    linarith
  have hεsmall₁ : ε < ε₁ := by
    have hm := min_le_right ε₀ ε₁
    dsimp only [ε]
    linarith
  let q : E := ε • θ
  let c₁ : ℝ := ε * (h - ⟪θ, xe⟫)
  let v : E → ℝ := fun x => w x - (c₁ + ⟪q, x⟫)
  have hv_eq (x : E) :
      v x = w x - ε * (⟪x - xe, θ⟫ + h) := by
    have hqx : ⟪q, x⟫ = ε * ⟪θ, x⟫ := by
      change ⟪ε • θ, x⟫ = ε * ⟪θ, x⟫
      rw [real_inner_smul_left]
    have hinner : ⟪x - xe, θ⟫ = ⟪θ, x⟫ - ⟪θ, xe⟫ := by
      rw [← real_inner_comm (x - xe) θ, inner_sub_right]
    change w x - (c₁ + ⟪q, x⟫) = _
    rw [hqx, hinner]
    dsimp only [c₁]
    ring
  have hvconv : ConvexOn ℝ univ v := FunctionalInequalities.Analysis.contact_sub_affine_convex hwconv c₁ q
  have hvc : Continuous v :=
    continuousOn_univ.mp (hvconv.continuousOn isOpen_univ)
  let S : Set E := {x | v x < 0}
  have hSo : IsOpen S := isOpen_lt hvc continuous_const
  have hSc : Convex ℝ S := by
    simpa only [mem_univ, true_and] using hvconv.convex_lt 0
  have hSQ₀ : S ⊆ Q₀ := by
    intro x hx
    apply hQ₀sub ε hε hεsmall₀
    change u x - (u x₀ + ⟪p, x - x₀⟫) <
      ε * (⟪x - xe, θ⟫ + h)
    rw [← hw_eq]
    have hx' : v x < 0 := hx
    rw [hv_eq] at hx'
    linarith
  have hSb : Bornology.IsBounded S := hQ₀.isBounded.subset hSQ₀
  have hSthickMin : S ⊆ cthickening (min δ δ') P := by
    intro x hx
    apply hε₁sub ε hε hεsmall₁
    change u x - (u x₀ + ⟪p, x - x₀⟫) <
      ε * (⟪x - xe, θ⟫ + h)
    rw [← hw_eq]
    have hx' : v x < 0 := hx
    rw [hv_eq] at hx'
    linarith
  have hSQ : S ⊆ Q :=
    hSthickMin.trans (cthickening_mono (min_le_right δ δ') P)
  have hSclQ : closure S ⊆ Q := closure_minimal hSQ hQ.isClosed
  have hSthick : S ⊆ cthickening δ P :=
    hSthickMin.trans (cthickening_mono (min_le_left δ δ') P)
  have hvxe : v xe = -(ε * h) := by
    rw [hv_eq, hwxe]
    simp only [sub_self, inner_zero_left, zero_add, zero_sub]
  have hxeS : xe ∈ S := by
    change v xe < 0
    rw [hvxe]
    exact neg_neg_of_pos (mul_pos hε hh)
  have hyS : y ∈ S := by
    change v y < 0
    rw [hv_eq, (hw_zero_iff y).mpr hyC, hypair]
    have hgap : 0 < -β + h := by linarith
    exact sub_neg.mpr (mul_pos hε hgap)
  have hup (x : E) (hx : x ∈ S) : ⟪x - xe, θ⟫ ≤ δ := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (mem_cthickening_iff.mp (hSthick hx))
    have hdist : infDist x P ≤ δ := by
      simpa only [Metric.infDist, ENNReal.toReal_ofReal hδ.le] using ht
    obtain ⟨r, hr, heq⟩ := hPcompact.exists_infDist_eq_dist hPne x
    have hrdist : ‖x - r‖ ≤ δ := by
      rw [heq, dist_eq_norm] at hdist
      exact hdist
    have hrwidth := hcontactWidth r hr.1
    have hinner : ⟪x - r, θ⟫ ≤ ‖x - r‖ := by
      calc
        ⟪x - r, θ⟫ ≤ |⟪x - r, θ⟫| := le_abs_self _
        _ ≤ ‖x - r‖ * ‖θ‖ := abs_real_inner_le_norm _ _
        _ = ‖x - r‖ := by rw [hθ, mul_one]
    rw [show x - xe = (x - r) + (r - xe) by abel, inner_add_left]
    linarith
  have hvfront : ∀ x ∈ frontier S, v x = 0 := by
    have hsub : S ⊆ {x | v x ≤ 0} := by
      intro z hz
      exact le_of_lt (show v z < 0 from hz)
    have hcl : closure S ⊆ {x | v x ≤ 0} :=
      closure_minimal hsub (isClosed_le hvc continuous_const)
    intro x hx
    have hlo : v x ≤ 0 := hcl (frontier_subset_closure hx)
    have hnotS : x ∉ S := (hSo.frontier_eq ▸ hx).2
    have hhi : 0 ≤ v x := le_of_not_gt hnotS
    exact le_antisymm hlo hhi
  have hSne : S.Nonempty := ⟨xe, hxeS⟩
  have hreg : interior (closure S) = S := by
    rw [hSc.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hSo.interior_eq]; exact hSne), hSo.interior_eq]
  have hclosureCompact : IsCompact (closure S) :=
    hQ.of_isClosed_subset isClosed_closure hSclQ
  obtain ⟨e, heball, heouter⟩ := hnormalize (closure S) hclosureCompact hSc.closure
    (by rw [hreg]; exact hSne)
  let eh := (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph
  let S' : Set E := e '' S
  let v' : E → ℝ := v ∘ e.symm
  let D : ℝ := |LinearMap.det (e.linear : E →ₗ[ℝ] E)|
  have hD : 0 < D := FunctionalInequalities.Analysis.contact_det_pos e
  have hS'o : IsOpen S' := eh.isOpenMap S hSo
  have hS'c : Convex ℝ S' := hSc.affine_image e.toAffineMap
  have hS'outer : S' ⊆ closedBall (0 : E) C₀ :=
    (Set.image_mono subset_closure).trans heouter
  have hS'b : Bornology.IsBounded S' :=
    Metric.isBounded_closedBall.subset hS'outer
  have hS'ball : ball (0 : E) 1 ⊆ S' := by
    intro x hx
    have hi : x ∈ interior (e '' closure S) :=
      interior_mono heball (ball_subset_interior_closedBall hx)
    have him : eh '' interior (closure S) = interior (e '' closure S) :=
      eh.image_interior (closure S)
    rw [← him, hreg] at hi
    exact hi
  have hv'conv : ConvexOn ℝ univ v' := by
    simpa [v', Function.comp_def] using hvconv.comp_affineMap e.symm.toAffineMap
  have hv'front : ∀ x ∈ frontier S', v' x = 0 := by
    intro x hx
    have him : eh '' frontier S = frontier S' := eh.image_frontier S
    rw [← him] at hx
    rcases hx with ⟨z, hz, rfl⟩
    change v (e.symm (e z)) = 0
    rw [e.symm_apply_apply]
    exact hvfront z hz
  have hloc :
      ∀ G' : Set E, IsOpen G' → G' ⊆ S' →
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage v' G') ≠ ∞ ∧
          (a / D ^ 2) * (volume G').toReal ≤
            (volume (FunctionalInequalities.Analysis.subgradientImage v' G')).toReal ∧
          (volume (FunctionalInequalities.Analysis.subgradientImage v' G')).toReal ≤
            (b / D ^ 2) * (volume G').toReal := by
    intro G' hG'o hG'S
    let G : Set E := e.symm '' G'
    have hGo : IsOpen G := eh.symm.isOpenMap G' hG'o
    have hGS : G ⊆ S := by
      rintro x ⟨z, hz, rfl⟩
      rcases hG'S hz with ⟨y, hy, he⟩
      rw [← he, e.symm_apply_apply]
      exact hy
    have hGcl : closure G ⊆ Q := (closure_mono hGS).trans hSclQ
    obtain ⟨hlo, hhi⟩ := hbounds G hGo hGcl
    have hhi' :
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ≤
          ENNReal.ofReal b * volume G :=
      hhi.trans (mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (le_max_left b₀ 1)) _)
    have hvvolume :
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage v G) =
          volume (FunctionalInequalities.Analysis.subgradientImage u G) := by
      rw [FunctionalInequalities.Analysis.contact_volume_sub_affine w c₁ q G,
        FunctionalInequalities.Analysis.contact_volume_sub_affine u c₀ p G]
    have hGfin : (volume : Measure E) G ≠ ∞ :=
      (hSb.subset hGS).measure_lt_top.ne
    obtain ⟨hfin, hrealLo, hrealHi⟩ :=
      FunctionalInequalities.Analysis.contact_real_bounds (volume : Measure E) ha.le hb.le hGfin hlo hhi'
    rw [← hvvolume] at hfin hrealLo hrealHi
    have himage : e '' G = G' := e.toEquiv.image_symm_image G'
    have ht := FunctionalInequalities.Analysis.contact_transport_real_bounds v e G a b hfin hrealLo hrealHi
    simpa only [himage] using ht
  let t : ℝ := ε * h
  have ht : 0 < t := mul_pos hε hh
  have hv'lo : ∀ x ∈ S', -2 * t ≤ v' x := by
    rintro x ⟨z, hz, rfl⟩
    change -2 * t ≤ v (e.symm (e z))
    rw [e.symm_apply_apply, hv_eq]
    have hzlo := hw_nonneg z
    have hzup := hup z hz
    have hi : ⟪z - xe, θ⟫ + h ≤ 2 * h := by linarith
    have hm := mul_le_mul_of_nonneg_left hi hε.le
    dsimp only [t]
    nlinarith
  have hv'hi : ∀ x ∈ S', v' x ≤ 0 := by
    rintro x ⟨z, hz, rfl⟩
    change v (e.symm (e z)) ≤ 0
    rw [e.symm_apply_apply]
    exact le_of_lt hz
  have hhalfS : ball (0 : E) (1 / 2) ⊆ S' :=
    (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hS'ball
  have hA :
      a / D ^ 2 ≤ (8 * t) ^ n :=
    FunctionalInequalities.Analysis.contact_stepA_readable ht hS'ball hv'lo hv'hi
      (hloc (ball (0 : E) (1 / 2)) isOpen_ball hhalfS).2.1
  obtain ⟨hfinite, _, hupper⟩ := hloc S' hS'o (Subset.refl S')
  have hupper' :
      ((volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage v' S')).toReal ≤
        (b / D ^ 2) * (volume (closedBall (0 : E) C₀)).toReal := by
    apply hupper.trans
    apply mul_le_mul_of_nonneg_left
    · exact ENNReal.toReal_mono Metric.isBounded_closedBall.measure_lt_top.ne
        (measure_mono hS'outer)
    · positivity
  have hxeS' : e xe ∈ S' := ⟨xe, hxeS, rfl⟩
  have hv'xe : v' (e xe) = -t := by
    change v (e.symm (e xe)) = -(ε * h)
    rw [e.symm_apply_apply]
    exact hvxe
  have hAMP := hmaximum v' hv'conv S' hS'o hS'c hS'b
    (fun x hx => (hv'front x hx).symm.le)
    (e xe) hxeS' (by rw [hv'xe]; exact neg_neg_of_pos ht)
  rw [hv'xe, neg_neg] at hAMP
  have hBA : b / D ^ 2 ≤ R * (a / D ^ 2) := by
    apply le_of_eq
    dsimp only [R]
    field_simp [ha.ne', hD.ne']
  have haway : c ≤ K * infDist (e xe) (frontier S') :=
    FunctionalInequalities.Analysis.contact_stepB hc ht hC₀ hR hS'outer hfinite hAMP hupper' hA hBA
  have hnear :
      infDist (e xe) (frontier S') ≤ 2 * C₀ * δ / β :=
    FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width_readable hSo hSb hxeS hθ hδ.le hβ
      hup ⟨y, hyS, hypair.le⟩ e hC₀ hS'outer
  have hstrict : K * infDist (e xe) (frontier S') < c :=
    (mul_le_mul_of_nonneg_left hnear hK).trans_lt hδsmall
  exact (not_lt_of_ge haway) hstrict
