-- Prove2me | solution 1 for DupacovaWets.Consistency.expectFn_epiConverges
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:22:44.540389+00:00
-- url     : https://prove2.me/submissions/a615b7d5-42d2-45b0-88ee-ae067c9d6ae0

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
open DupacovaWets.Consistency

namespace DW2Aux

theorem expect_top {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (g : Ξ → EReal) (hg : ∀ ξ, g ξ = ⊤) : expect Q g = ⊤ := by
  have : ∫⁻ ξ, (g ξ).toENNReal ∂Q = ∞ := by
    simp [hg]
  simp [expect, this]

theorem expect_coe {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
    (h : Ξ → ℝ) (hi : Integrable h Q) :
    expect Q (fun ξ => (h ξ : EReal)) = ((∫ ξ, h ξ ∂Q : ℝ) : EReal) := by
  have h1 : ∫⁻ ξ, ENNReal.ofReal (h ξ) ∂Q ≠ ∞ := hi.lintegral_lt_top.ne
  have h2 : ∫⁻ ξ, ENNReal.ofReal (-h ξ) ∂Q ≠ ∞ := hi.neg.lintegral_lt_top.ne
  have e1 : (fun ξ => ((h ξ : EReal)).toENNReal) = fun ξ => ENNReal.ofReal (h ξ) := by
    funext ξ; simp
  have e2 : (fun ξ => (-(h ξ : EReal)).toENNReal) = fun ξ => ENNReal.ofReal (-h ξ) := by
    funext ξ; rw [← EReal.coe_neg]; simp
  unfold expect
  rw [e1, e2, if_neg h1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    EReal.coe_sub, EReal.coe_ennreal_toReal h1, EReal.coe_ennreal_toReal h2]


section Tight
variable {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]

theorem integrable_of_tail (Q : Measure Ξ) [IsProbabilityMeasure Q] (h : Ξ → ℝ)
    (hc : Continuous h) (K : Set Ξ) (hK : IsCompact K)
    (ht : ∫⁻ ξ in Kᶜ, ENNReal.ofReal |h ξ| ∂Q ≠ ∞) : Integrable h Q := by
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold HasFiniteIntegral
  have e : (fun ξ => ‖h ξ‖ₑ) = fun ξ => ENNReal.ofReal |h ξ| := by
    funext ξ; rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  rw [e, ← lintegral_add_compl _ hKm]
  refine ENNReal.add_lt_top.mpr ⟨?_, lt_of_le_of_ne le_top ht⟩
  calc ∫⁻ ξ in K, ENNReal.ofReal |h ξ| ∂Q ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂Q := by
        refine setLIntegral_mono measurable_const fun ξ hξ => ?_
        exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC ξ hξ)
    _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- truncation estimate -/
theorem trunc_est (Q : Measure Ξ) [IsProbabilityMeasure Q] (h : Ξ → ℝ)
    (hc : Continuous h) (K : Set Ξ) (hK : IsCompact K) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ ξ ∈ K, |h ξ| ≤ M) (ε : ℝ)
    (ht : ∫⁻ ξ in Kᶜ, ENNReal.ofReal |h ξ| ∂Q < ENNReal.ofReal ε) :
    |∫ ξ, h ξ ∂Q - ∫ ξ, max (-M) (min M (h ξ)) ∂Q| < ε := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hi : Integrable h Q := integrable_of_tail Q h hc K hK (ne_top_of_lt ht)
  have hgc : Continuous fun ξ => max (-M) (min M (h ξ)) :=
    continuous_const.max (continuous_const.min hc)
  have hgi : Integrable (fun ξ => max (-M) (min M (h ξ))) Q := by
    refine Integrable.of_bound (C := M) hgc.aestronglyMeasurable (Eventually.of_forall ?_)
    intro ξ
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hdi : Integrable (fun ξ => h ξ - max (-M) (min M (h ξ))) Q := hi.sub hgi
  rw [← integral_sub hi hgi]
  have hpt : ∀ ξ, ENNReal.ofReal |h ξ - max (-M) (min M (h ξ))| ≤
      Kᶜ.indicator (fun ξ => ENNReal.ofReal |h ξ|) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ K
    · have := hM ξ hξ
      rw [abs_le] at this
      have : max (-M) (min M (h ξ)) = h ξ := by
        rw [min_eq_right this.2, max_eq_right this.1]
      simp [this]
    · rw [Set.indicator_of_mem (Set.mem_compl hξ)]
      refine ENNReal.ofReal_le_ofReal ?_
      have key : ∀ a : ℝ, |a - max (-M) (min M a)| ≤ |a| := by
        intro a
        have h1 := le_abs_self a; have h2 := neg_abs_le a; have h3 := abs_nonneg a
        rcases le_total a M with ha | ha
        · rw [min_eq_right ha]
          rcases le_total (-M) a with hb | hb
          · rw [max_eq_right hb]; simp
          · rw [max_eq_left hb, abs_le]; constructor <;> linarith
        · rw [min_eq_left ha, max_eq_right (by linarith), abs_le]; constructor <;> linarith
      exact key _
  have hle : ∫⁻ ξ, ENNReal.ofReal |h ξ - max (-M) (min M (h ξ))| ∂Q ≤
      ∫⁻ ξ in Kᶜ, ENNReal.ofReal |h ξ| ∂Q := by
    rw [← lintegral_indicator hKm.compl]
    exact lintegral_mono hpt
  calc |∫ ξ, (h ξ - max (-M) (min M (h ξ))) ∂Q|
      ≤ ∫ ξ, |h ξ - max (-M) (min M (h ξ))| ∂Q := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := Q)
          (fun ξ => h ξ - max (-M) (min M (h ξ)))
    _ = (∫⁻ ξ, ENNReal.ofReal |h ξ - max (-M) (min M (h ξ))| ∂Q).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => abs_nonneg _)
          hdi.abs.aestronglyMeasurable]
    _ < ε := by
        have hε : 0 < ε := by
          by_contra hn; push_neg at hn
          rw [ENNReal.ofReal_of_nonpos hn] at ht; exact absurd ht (not_lt_zero')
        refine (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top (ne_top_of_lt ht) hle)
          (ne_top_of_lt ht) |>.mpr hle).trans_lt ?_
        rw [← ENNReal.toReal_ofReal hε.le]
        exact (ENNReal.toReal_lt_toReal (ne_top_of_lt ht) ENNReal.ofReal_ne_top).mpr ht

theorem tendsto_integral_of_tight (Qk : ℕ → Measure Ξ) [∀ k, IsProbabilityMeasure (Qk k)]
    (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (hweak : ∀ g : Ξ →ᵇ ℝ, Tendsto (fun k => ∫ ξ, g ξ ∂(Qk k)) atTop (𝓝 (∫ ξ, g ξ ∂Q)))
    (h : Ξ → ℝ) (hc : Continuous h)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : Set Ξ, IsCompact K ∧
      ∫⁻ ξ in Kᶜ, ENNReal.ofReal |h ξ| ∂Q < ENNReal.ofReal ε ∧
      ∀ k, ∫⁻ ξ in Kᶜ, ENNReal.ofReal |h ξ| ∂(Qk k) < ENNReal.ofReal ε) :
    Tendsto (fun k => ∫ ξ, h ξ ∂(Qk k)) atTop (𝓝 (∫ ξ, h ξ ∂Q)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK, hQ, hQk⟩ := htail (ε / 3) (by linarith)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  set M := max C 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ ξ ∈ K, |h ξ| ≤ M := fun ξ hξ =>
    (by simpa [Real.norm_eq_abs] using hC ξ hξ : |h ξ| ≤ C).trans (le_max_left _ _)
  have hgc : Continuous fun ξ => max (-M) (min M (h ξ)) :=
    continuous_const.max (continuous_const.min hc)
  let g : Ξ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨_, hgc⟩ (2 * M) (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]
    have := le_max_left (-M) (min M (h x)); have := max_le (a := -M) (b := min M (h x))
      (by linarith) (min_le_left M (h x))
    have := le_max_left (-M) (min M (h y)); have := max_le (a := -M) (b := min M (h y))
      (by linarith) (min_le_left M (h y))
    constructor <;> linarith)
  have hg : ∀ ξ, g ξ = max (-M) (min M (h ξ)) := fun ξ => rfl
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hweak g) (ε / 3) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  have e1 := trunc_est (Qk k) h hc K hK M hM0 hM (ε / 3) (hQk k)
  have e2 := trunc_est Q h hc K hK M hM0 hM (ε / 3) hQ
  have e3 := hN k hk
  simp only [hg, Real.dist_eq] at e3
  rw [Real.dist_eq]
  calc |∫ ξ, h ξ ∂(Qk k) - ∫ ξ, h ξ ∂Q|
      ≤ |∫ ξ, h ξ ∂(Qk k) - ∫ ξ, max (-M) (min M (h ξ)) ∂(Qk k)| +
        |∫ ξ, max (-M) (min M (h ξ)) ∂(Qk k) - ∫ ξ, max (-M) (min M (h ξ)) ∂Q| +
        |∫ ξ, h ξ ∂Q - ∫ ξ, max (-M) (min M (h ξ)) ∂Q| := by
        have := abs_sub_le (∫ ξ, h ξ ∂(Qk k)) (∫ ξ, max (-M) (min M (h ξ)) ∂(Qk k))
          (∫ ξ, h ξ ∂Q)
        have := abs_sub_le (∫ ξ, max (-M) (min M (h ξ)) ∂(Qk k))
          (∫ ξ, max (-M) (min M (h ξ)) ∂Q) (∫ ξ, h ξ ∂Q)
        rw [abs_sub_comm (∫ ξ, max (-M) (min M (h ξ)) ∂Q) (∫ ξ, h ξ ∂Q)] at this
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end Tight

section Main
variable {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]

theorem toReal_cont (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
    Continuous (fun ξ => (f x ξ).toReal) := by
  refine EReal.continuousOn_toReal.comp_continuous (h34.continuous_of_mem x hx) fun ξ => ?_
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h34.ne_bot x ξ, ((h34.lt_top_iff x ξ).mpr hx).ne⟩

theorem coe_toReal_eq (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) (ξ : Ξ) :
    (((f x ξ).toReal : ℝ) : EReal) = f x ξ :=
  EReal.coe_toReal ((h34.lt_top_iff x ξ).mpr hx).ne (h34.ne_bot x ξ)

theorem expectFn_eq (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S)
    (hi : Integrable (fun ξ => (f x ξ).toReal) Q) :
    expectFn Q f x = ((∫ ξ, (f x ξ).toReal ∂Q : ℝ) : EReal) := by
  unfold expectFn
  rw [← expect_coe Q _ hi]
  congr 1
  funext ξ
  exact (coe_toReal_eq f S h34 x hx ξ).symm

theorem expectFn_notmem (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ S) : expectFn Q f x = ⊤ := by
  unfold expectFn
  refine expect_top Q _ fun ξ => ?_
  by_contra h
  exact hx ((h34.lt_top_iff x ξ).mp (lt_top_iff_ne_top.mpr h))

end Main

end DW2Aux

open DW2Aux in
theorem solution {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∀ᵐ ζ ∂μ, EpiConverges (fun k => expectFn (Pν k ζ) f) (expectFn P f) ∧
      ∀ x, Tendsto (fun k => expectFn (Pν k ζ) f x) atTop (𝓝 (expectFn P f x)) := by
  filter_upwards [h35.ae] with ζ hζ
  obtain ⟨hw, htail, -⟩ := hζ
  haveI : ∀ k, IsProbabilityMeasure (Pν k ζ) := fun k => h35.isProb k ζ
  -- integrability on S
  have hint : ∀ x ∈ S, Integrable (fun ξ => (f x ξ).toReal) P ∧
      ∀ k, Integrable (fun ξ => (f x ξ).toReal) (Pν k ζ) := by
    intro x hx
    obtain ⟨K, hK, h1, h2⟩ := htail x hx 1 one_pos
    exact ⟨integrable_of_tail P _ (toReal_cont f S h34 x hx) K hK (ne_top_of_lt h1),
      fun k => integrable_of_tail _ _ (toReal_cont f S h34 x hx) K hK (ne_top_of_lt (h2 k))⟩
  -- real convergence on S
  have hreal : ∀ x ∈ S, Tendsto (fun k => ∫ ξ, (f x ξ).toReal ∂(Pν k ζ)) atTop
      (𝓝 (∫ ξ, (f x ξ).toReal ∂P)) := fun x hx =>
    tendsto_integral_of_tight (fun k => Pν k ζ) P hw _ (toReal_cont f S h34 x hx) (htail x hx)
  have hpt : ∀ x, Tendsto (fun k => expectFn (Pν k ζ) f x) atTop (𝓝 (expectFn P f x)) := by
    intro x
    by_cases hx : x ∈ S
    · have e : (fun k => expectFn (Pν k ζ) f x) =
          fun k => (((∫ ξ, (f x ξ).toReal ∂(Pν k ζ)) : ℝ) : EReal) := by
        funext k; exact expectFn_eq f S h34 _ x hx ((hint x hx).2 k)
      rw [e, expectFn_eq f S h34 P x hx (hint x hx).1]
      exact (continuous_coe_real_ereal.tendsto _).comp (hreal x hx)
    · simp only [expectFn_notmem f S h34 _ x hx]
      exact tendsto_const_nhds
  refine ⟨fun x => ⟨?_, ⟨fun _ => x, tendsto_const_nhds, (hpt x).limsup_eq.le⟩⟩, hpt⟩
  intro u hu
  by_cases hx : x ∈ S
  · obtain ⟨V, hV, β, hβ⟩ := h34.lowerLipschitz x hx
    set B := ‖β‖
    have hc : Tendsto (fun k => ((∫ ξ, (f x ξ).toReal ∂(Pν k ζ) - B * ‖x - u k‖ : ℝ) : EReal))
        atTop (𝓝 (expectFn P f x)) := by
      rw [expectFn_eq f S h34 P x hx (hint x hx).1]
      refine (continuous_coe_real_ereal.tendsto _).comp ?_
      have : Tendsto (fun k => ‖x - u k‖) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := x)).sub hu
        simpa using this.norm
      simpa using (hreal x hx).sub (this.const_mul B)
    rw [← hc.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [hu hV] with k hk
    by_cases hkS : u k ∈ S
    · rw [expectFn_eq f S h34 _ (u k) hkS ((hint (u k) hkS).2 k), EReal.coe_le_coe_iff]
      have hle : ∀ ξ, (f x ξ).toReal ≤ (f (u k) ξ).toReal + B * ‖x - u k‖ := by
        intro ξ
        have h1 := hβ (u k) ⟨hk, hkS⟩ ξ
        rw [← coe_toReal_eq f S h34 x hx ξ, ← coe_toReal_eq f S h34 (u k) hkS ξ,
          ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
        have h2 : β ξ ≤ B := (le_abs_self _).trans (by
          simpa [Real.norm_eq_abs] using β.norm_coe_le_norm ξ)
        nlinarith [norm_nonneg (x - u k)]
      have hmono := integral_mono ((hint x hx).2 k)
        (((hint (u k) hkS).2 k).add (integrable_const (B * ‖x - u k‖))) hle
      simp only [Pi.add_apply] at hmono
      rw [integral_add ((hint (u k) hkS).2 k) (integrable_const _), integral_const] at hmono
      simp only [probReal_univ, one_smul] at hmono
      linarith
    · rw [expectFn_notmem f S h34 _ (u k) hkS]; exact le_top
  · have hev : ∀ᶠ k in atTop, u k ∉ S :=
      hu (h34.isClosed_S.isOpen_compl.mem_nhds hx)
    calc expectFn P f x ≤ ⊤ := le_top
      _ = liminf (fun _ : ℕ => (⊤ : EReal)) atTop := liminf_const ⊤ |>.symm
      _ ≤ liminf (fun k => expectFn (Pν k ζ) f (u k)) atTop := by
        refine liminf_le_liminf ?_
        filter_upwards [hev] with k hk
        rw [expectFn_notmem f S h34 _ (u k) hk]
