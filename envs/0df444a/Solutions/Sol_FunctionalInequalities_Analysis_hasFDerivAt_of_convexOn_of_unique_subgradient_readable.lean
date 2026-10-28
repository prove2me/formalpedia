-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:57.303909+00:00
-- url     : https://prove2.me/submissions/ecbcede6-3bfd-4b6e-8b00-318af83a0d47

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT5CUniqueSubgradientDifferentiable
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.convex_line_slope_mono [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (u (x + a • v) - u x) / a ≤ (u (x + b • v) - u x) / b := by
  have hline : ConvexOn ℝ Set.univ (fun t : ℝ => u (t • v + x)) := by
    simpa only [Set.preimage_univ, Function.comp_def,
      AffineMap.lineMap_apply_module', add_sub_cancel_left] using
      hconv.comp_affineMap (AffineMap.lineMap x (x + v))
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h :=
    hline.slope_mono (show (0 : ℝ) ∈ Set.univ by simp)
      (show a ∈ Set.univ \ {0} by simp [ne_of_gt ha])
      (show b ∈ Set.univ \ {0} by simp [ne_of_gt hb]) hab
  simpa only [slope_def_field, zero_smul, add_zero, sub_zero, add_comm] using h
section FiniteDimensional
variable [FiniteDimensional ℝ E]
 lemma solution {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x g : E)
    (hg : ∀ y, u x + ⟪g, y - x⟫ ≤ u y)
    (huniq : ∀ q, (∀ y, u x + ⟪q, y - x⟫ ≤ u y) → q = g) :
    HasFDerivAt u ((InnerProductSpace.toDual ℝ E) g) x := by
  classical
  have hu : Continuous u :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let R : E → ℝ := fun h => u (x + h) - u x - ⟪g, h⟫
  have hR_nonneg : ∀ h, 0 ≤ R h := by
    intro h
    have hh := hg (x + h)
    have hh' : u x + ⟪g, h⟫ ≤ u (x + h) := by
      simpa only [add_sub_cancel_left] using hh
    dsimp [R]
    linarith
  have hF_cont (t : ℝ) :
      Continuous (fun v : E =>
        (u (x + t • v) - u x) / t - ⟪g, v⟫) := by
    have harg : Continuous (fun v : E => x + t • v) :=
      continuous_const.add (continuous_const.smul continuous_id)
    have hinner : Continuous (fun v : E => ⟪g, v⟫) :=
      continuous_const.inner continuous_id
    exact (((hu.comp harg).sub continuous_const).div_const t).sub hinner
  have hlittle :
      R =o[nhds 0] fun h : E => h := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    by_cases hS : (Metric.sphere (0 : E) 1).Nonempty
    · let S : Set E := Metric.sphere (0 : E) 1
      have hSc : IsCompact S := by
        exact isCompact_sphere (0 : E) 1
      let I := {v : E // v ∈ S}
      let H : ∀ v : I, ∃ q : E,
          (∀ y, u x + ⟪q, y - x⟫ ≤ u y) ∧
            ∀ ε > 0, ∃ t > 0,
              (u (x + t • (v : E)) - u x) / t ≤ ⟪q, (v : E)⟫ + ε :=
        fun v => FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable hconv x (v : E)
      let T : I → ℝ := fun v =>
        Classical.choose ((H v).choose_spec.2 (ε / 2) (by linarith))
      have hT_pos (v : I) : 0 < T v := by
        exact (Classical.choose_spec
          ((H v).choose_spec.2 (ε / 2) (by linarith))).1
      have hT_bound (v : I) :
          (u (x + T v • (v : E)) - u x) / T v -
              ⟪g, v⟫ ≤ ε / 2 := by
        have hqg : (H v).choose = g :=
          huniq _ (H v).choose_spec.1
        have hchosen :=
          Classical.choose_spec ((H v).choose_spec.2 (ε / 2) (by linarith))
        have hchosen' :
            (u (x + T v • (v : E)) - u x) / T v ≤
              ⟪g, v⟫ + ε / 2 := by
          simpa only [T, hqg] using hchosen.2
        linarith
      let U : I → Set E := fun v =>
        {w | (u (x + T v • w) - u x) / T v - ⟪g, w⟫ < ε}
      have hU_open : ∀ v : I, IsOpen (U v) := by
        intro v
        exact isOpen_Iio.preimage (hF_cont (T v))
      have hU_cover : S ⊆ ⋃ v : I, U v := by
        intro v hv
        let w : I := ⟨v, hv⟩
        have hw : (w : E) ∈ U w := by
          change (u (x + T w • (w : E)) - u x) / T w -
              ⟪g, w⟫ < ε
          exact (hT_bound w).trans_lt (by linarith)
        exact Set.mem_iUnion.2 ⟨w, hw⟩
      obtain ⟨K, hK⟩ := hSc.elim_finite_subcover U hU_open hU_cover
      have hK_nonempty : K.Nonempty := by
        obtain ⟨v, hv⟩ := hS
        have hv' := hK hv
        rcases Set.mem_iUnion.mp hv' with ⟨w, hv'⟩
        rcases Set.mem_iUnion.mp hv' with ⟨hwK, _⟩
        exact ⟨w, hwK⟩
      obtain ⟨v₀, hv₀⟩ := hK_nonempty
      let K' : Finset ℝ := K.image T
      have hK'_nonempty : K'.Nonempty := by
        refine ⟨T v₀, ?_⟩
        exact Finset.mem_image.mpr ⟨v₀, hv₀, rfl⟩
      let δ : ℝ := K'.min' hK'_nonempty
      have hδ : 0 < δ := by
        have hδmem : δ ∈ K' := by
          dsimp [δ]
          exact Finset.min'_mem K' hK'_nonempty
        rcases Finset.mem_image.mp hδmem with ⟨v, _, heq⟩
        rw [← heq]
        exact hT_pos v
      have hδ_le (v : I) (hv : v ∈ K) : δ ≤ T v := by
        have hmem : T v ∈ K' := Finset.mem_image.mpr ⟨v, hv, rfl⟩
        change K'.min' hK'_nonempty ≤ T v
        exact Finset.min'_le K' (T v) hmem
      have hsmall :
          ∀ᶠ h : E in nhds 0, ‖h‖ < δ := by
        exact Metric.eventually_nhds_iff.2 ⟨δ, hδ, by
          intro h hh
          simpa [dist_zero_right] using hh⟩
      filter_upwards [hsmall] with h hh
      by_cases hz : h = 0
      · simp [R, hz]
      · let s : ℝ := ‖h‖
        let w : E := s⁻¹ • h
        have hs : 0 < s := by
          exact norm_pos_iff.mpr hz
        have hw : ‖w‖ = 1 := by
          calc
            ‖w‖ = ‖s⁻¹‖ * ‖h‖ := norm_smul _ _
            _ = s⁻¹ * ‖h‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hs)
        have hwS : w ∈ S := by
          rw [Metric.mem_sphere]
          simpa [dist_zero_right] using hw
        have hwI : ∃ v : I, v ∈ K ∧ (w : E) ∈ U v := by
          have hcover := hK hwS
          rcases Set.mem_iUnion.mp hcover with ⟨v, hcover⟩
          rcases Set.mem_iUnion.mp hcover with ⟨hvK, hwv⟩
          exact ⟨v, hvK, hwv⟩
        obtain ⟨v, hvK, hwv⟩ := hwI
        have hsδ : s < δ := by
          exact hh
        have hst : s ≤ T v := by
          exact hsδ.le.trans (hδ_le v hvK)
        have hmono :
            (u (x + s • w) - u x) / s ≤
              (u (x + T v • w) - u x) / T v := by
          exact FunctionalInequalities.Analysis.convex_line_slope_mono hconv x w hs hst
        have hU := hwv
        change (u (x + T v • w) - u x) / T v -
            ⟪g, w⟫ < ε at hU
        have hmono' :
            u (x + s • w) - u x ≤
              ((u (x + T v • w) - u x) / T v) * s := by
          exact (div_le_iff₀ hs).mp hmono
        have hupper :
            u (x + s • w) - u x - ⟪g, s • w⟫ ≤ ε * s := by
          have hscale : ⟪g, s • w⟫ = s * ⟪g, w⟫ := by
            simp [real_inner_smul_right]
          rw [hscale]
          calc
            u (x + s • w) - u x - s * ⟪g, w⟫ ≤
                ((u (x + T v • w) - u x) / T v) * s -
                  s * ⟪g, w⟫ := by
                    exact sub_le_sub_right hmono' _
            _ = ((u (x + T v • w) - u x) / T v -
                  ⟪g, w⟫) * s := by ring
            _ ≤ ε * s := by
              exact mul_le_mul_of_nonneg_right (by linarith) hs.le
        have heq : s • w = h := by
          dsimp [w, s]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
        have hnorm : ‖s • w‖ = s := by
          rw [norm_smul, Real.norm_of_nonneg hs.le, hw, mul_one]
        have hupper' :
            R h ≤ ε * ‖h‖ := by
          rw [← heq]
          change u (x + s • w) - u x - ⟪g, s • w⟫ ≤ ε * ‖s • w‖
          rw [hnorm]
          exact hupper
        rw [Real.norm_of_nonneg (hR_nonneg h)]
        exact hupper'
    · have hzero : ∀ v : E, v = 0 := by
        intro v
        by_contra hv
        let w : E := ‖v‖⁻¹ • v
        have hw : ‖w‖ = 1 := by
          calc
            ‖w‖ = ‖‖v‖⁻¹‖ * ‖v‖ := norm_smul _ _
            _ = ‖v‖⁻¹ * ‖v‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
            _ = 1 := inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hv))
        exact hS ⟨w, by
          rw [Metric.mem_sphere]
          simpa [dist_zero_right] using hw⟩
      exact Filter.Eventually.of_forall (fun h => by
        simp [R, hzero h])
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [InnerProductSpace.toDual_apply_apply, R] using hlittle
