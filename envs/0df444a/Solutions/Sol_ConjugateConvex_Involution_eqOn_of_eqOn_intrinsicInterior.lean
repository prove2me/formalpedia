-- Prove2me | solution 1 for ConjugateConvex.Involution.eqOn_of_eqOn_intrinsicInterior
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:54:32.965669+00:00
-- url     : https://prove2.me/submissions/caadc9b4-61bf-445d-b978-d1c492e669bc

import Mathlib



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

theorem ci_le_of_eq {n : ℕ} (G : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (hg : ConvexOn ℝ G g) (hfl : LowerSemicontinuousOn f G)
    (hfg : Set.EqOn f g (intrinsicInterior ℝ G)) (x : Fin n → ℝ) (hx : x ∈ G) :
    f x ≤ g x := by
  obtain ⟨y, hy⟩ := (intrinsicInterior_nonempty hg.1).2 ⟨x, hx⟩
  have hyG : y ∈ G := intrinsicInterior_subset hy
  by_contra hlt
  push Not at hlt
  set c := (g x + f x) / 2 with hc
  have hcf : c < f x := by rw [hc]; linarith
  have hlsc := hfl x hx c hcf
  let z : ℝ → (Fin n → ℝ) := fun t => (1 - t) • x + t • y
  have hzc : Continuous z := by fun_prop
  have hz0 : z 0 = x := by simp [z]
  have hT : Filter.Tendsto z (nhdsWithin 0 (Set.Ioo 0 1)) (nhdsWithin x G) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := hzc.tendsto 0
      rw [hz0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hg.1 hx hyG (by linarith [ht.2]) ht.1.le (by ring)
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioo 0 1), c ≤ (1 - t) * g x + t * g y := by
    filter_upwards [hT hlsc, self_mem_nhdsWithin] with t h1 ht
    have hri := ci_segment_ri hg.1 hx hy ht.1 ht.2.le
    have heq := hfg hri
    have hconv := hg.2 hx hyG (show (0:ℝ) ≤ 1 - t by linarith [ht.2]) ht.1.le (show 1 - t + t = 1 by ring)
    simp only [smul_eq_mul] at hconv
    have : c < f (z t) := h1
    simp only [z] at this
    linarith
  have hlim : Filter.Tendsto (fun t : ℝ => (1 - t) * g x + t * g y)
      (nhdsWithin (0:ℝ) (Set.Ioo 0 1)) (nhds (g x)) := by
    have : Filter.Tendsto (fun t : ℝ => (1 - t) * g x + t * g y) (nhds 0)
        (nhds ((1 - 0) * g x + 0 * g y)) := by
      apply Continuous.tendsto; fun_prop
    simp only [sub_zero, one_mul, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (0:ℝ) (Set.Ioo 0 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num)]
    simp
  have := ge_of_tendsto hlim hev
  rw [hc] at this
  linarith

theorem eqOn_core {n : ℕ} (G : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (hg : ConvexOn ℝ G g)
    (hfl : LowerSemicontinuousOn f G) (hgl : LowerSemicontinuousOn g G)
    (hfg : Set.EqOn f g (intrinsicInterior ℝ G)) :
    Set.EqOn f g G := fun x hx =>
  le_antisymm (ci_le_of_eq G f g hg hfl hfg x hx) (ci_le_of_eq G g f hf hgl hfg.symm x hx)

end ConjugateConvex.Involution

open ConjugateConvex.Involution


theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ G f) (hg : ConvexOn ℝ G g)
    (hfl : LowerSemicontinuousOn f G) (hgl : LowerSemicontinuousOn g G)
    (hfg : Set.EqOn f g (intrinsicInterior ℝ G)) :
    Set.EqOn f g G := by
  exact eqOn_core G f g hf hg hfl hgl hfg
