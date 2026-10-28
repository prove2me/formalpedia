-- Prove2me | solution 1 for FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:46.530974+00:00
-- url     : https://prove2.me/submissions/b2fc408f-4be8-405d-b1af-bfa8c18a194f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subseq_tendsto_of_convexOn_of_bddAbove_readable
import Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_readable
import Theorems.Thm_FunctionalInequalities_Probability_real_convexOn_effective_domain_readable
import Theorems.Thm_FunctionalInequalities_Analysis_radialExtension_radial_limit_readable

section
noncomputable section
open Set Filter
section NormedSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.smul_mem_of_mem_closure
    {K : Set E} (hK : IsOpen K) (hconv : Convex ℝ K) (h0K : (0 : E) ∈ K)
    {x : E} (hx : x ∈ closure K) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : t • x ∈ K := by
  have hz : (0 : E) ∈ interior K := by rwa [hK.interior_eq]
  have h := hconv.combo_interior_closure_mem_interior hz hx
    (show 0 < 1 - t by linarith) ht0 (by ring)
  simpa only [smul_zero, zero_add, hK.interior_eq] using h
private lemma FunctionalInequalities.Analysis.radial_mono
    {K : Set E} (h0K : (0 : E) ∈ K) {g : E → ℝ} (hg : ConvexOn ℝ K g)
    (hnn : ∀ y ∈ K, 0 ≤ g y) (hg0 : g 0 = 0) {x : E} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) (htK : t • x ∈ K) :
    g (s • x) ≤ g (t • x) := by
  have ha : 0 ≤ s / t := div_nonneg hs ht.le
  have ha1 : s / t ≤ 1 := (div_le_iff₀ ht).mpr (by simpa using hst)
  have h := hg.2 htK h0K ha (sub_nonneg.mpr ha1) (show s / t + (1 - s / t) = 1 by ring)
  have he : (s / t) • (t • x) + (1 - s / t) • (0 : E) = s • x := by
    rw [smul_zero, add_zero, smul_smul, div_mul_cancel₀ _ ht.ne']
  rw [he, hg0, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at h
  exact h.trans (mul_le_of_le_one_left (hnn _ htK) ha1)
private lemma FunctionalInequalities.Analysis.radialCut_convex_epigraph {K : Set E} {g : E → ℝ} (hg : ConvexOn ℝ K g) (a : ℝ) :
    Convex ℝ {p : E × ℝ | FunctionalInequalities.Analysis.radialCut K g a p.1 ≤ (p.2 : EReal)} := by
  classical
  let L : E × ℝ →ₗ[ℝ] E × ℝ :=
    (a • LinearMap.fst ℝ E ℝ).prod (LinearMap.snd ℝ E ℝ)
  have he : {p : E × ℝ | FunctionalInequalities.Analysis.radialCut K g a p.1 ≤ (p.2 : EReal)} =
      L ⁻¹' {p : E × ℝ | p.1 ∈ K ∧ g p.1 ≤ p.2} := by
    ext p
    by_cases hp : a • p.1 ∈ K
    · simp [FunctionalInequalities.Analysis.radialCut, hp, L, EReal.coe_le_coe_iff]
    · simp [FunctionalInequalities.Analysis.radialCut, hp, L]
  rw [he]
  exact hg.convex_epigraph.linear_preimage L
section MeasurableSpace
variable [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.measurable_radialCut {K : Set E} (hK : IsOpen K)
    {g : E → ℝ} (hcont : ContinuousOn g K) (a : ℝ) : Measurable (FunctionalInequalities.Analysis.radialCut K g a) := by
  classical
  let S : Set E := {x | a • x ∈ K}
  have hS : IsOpen S := hK.preimage (continuous_const.smul continuous_id)
  have hin : ContinuousOn (fun x => (g (a • x) : EReal)) S :=
    continuous_coe_real_ereal.comp_continuousOn
      (hcont.comp (continuous_const.smul continuous_id).continuousOn (by intro x hx; exact hx))
  have hout : ContinuousOn (fun _ : E => (⊤ : EReal)) Sᶜ := continuous_const.continuousOn
  have hm := hin.measurable_piecewise hout hS.measurableSet
  have he : FunctionalInequalities.Analysis.radialCut K g a = S.piecewise (fun x => (g (a • x) : EReal))
      (fun _ => ⊤) := by
    funext x
    by_cases hx : a • x ∈ K
    · simp [FunctionalInequalities.Analysis.radialCut, S, hx]
    · simp [FunctionalInequalities.Analysis.radialCut, S, hx]
  rw [he]
  exact hm
end MeasurableSpace
private theorem FunctionalInequalities.Analysis.radialScale_pos (n : ℕ) : 0 < FunctionalInequalities.Analysis.radialScale n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 1 < (n : ℝ) + 2 := by linarith
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
  dsimp [FunctionalInequalities.Analysis.radialScale]
  simp only [one_div_one] at h
  linarith
private theorem FunctionalInequalities.Analysis.radialScale_lt_one (n : ℕ) : FunctionalInequalities.Analysis.radialScale n < 1 := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have h := one_div_pos.mpr hden
  dsimp [FunctionalInequalities.Analysis.radialScale]
  linarith
private theorem FunctionalInequalities.Analysis.radialScale_monotone : Monotone FunctionalInequalities.Analysis.radialScale := by
  intro m n hmn
  have hm : 0 < (m : ℝ) + 2 := by positivity
  have hle : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hmn 2
  have h := one_div_le_one_div_of_le hm hle
  dsimp [FunctionalInequalities.Analysis.radialScale]
  linarith
private theorem FunctionalInequalities.Analysis.radialScale_tendsto : Tendsto FunctionalInequalities.Analysis.radialScale atTop (nhds (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds (0 : ℝ)) := by
    have h₀ : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h₂ := (tendsto_add_atTop_iff_nat 2).2 h₀
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h₂
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (nhds (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
private lemma FunctionalInequalities.Analysis.radialExtension_nonneg
    {K : Set E} {g : E → ℝ} (hnn : ∀ x ∈ K, 0 ≤ g x) (x : E) :
    0 ≤ FunctionalInequalities.Analysis.radialExtension K g x := by
  classical
  apply le_iSup_of_le 0
  by_cases hx : FunctionalInequalities.Analysis.radialScale 0 • x ∈ K
  · simp only [FunctionalInequalities.Analysis.radialCut, if_pos hx]
    exact EReal.coe_nonneg.mpr (hnn _ hx)
  · simp [FunctionalInequalities.Analysis.radialCut, hx]
private lemma FunctionalInequalities.Analysis.radialExtension_convex_epigraph {K : Set E} {g : E → ℝ} (hg : ConvexOn ℝ K g) :
    Convex ℝ {p : E × ℝ | FunctionalInequalities.Analysis.radialExtension K g p.1 ≤ (p.2 : EReal)} := by
  have he : {p : E × ℝ | FunctionalInequalities.Analysis.radialExtension K g p.1 ≤ (p.2 : EReal)} =
      ⋂ n, {p : E × ℝ | FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) p.1 ≤ (p.2 : EReal)} := by
    ext p
    simp only [FunctionalInequalities.Analysis.radialExtension, iSup_le_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  exact convex_iInter fun n => radialCut_convex_epigraph hg (FunctionalInequalities.Analysis.radialScale n)
private lemma FunctionalInequalities.Analysis.measurable_radialExtension
    [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsOpen K)
    {g : E → ℝ} (hcont : ContinuousOn g K) :
    Measurable (FunctionalInequalities.Analysis.radialExtension K g) := by
  exact Measurable.iSup fun n => measurable_radialCut hK hcont (FunctionalInequalities.Analysis.radialScale n)
private lemma FunctionalInequalities.Analysis.radialExtension_eq_on
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0)
    {x : E} (hx : x ∈ K) : FunctionalInequalities.Analysis.radialExtension K g x = (g x : EReal) := by
  have hmem (n : ℕ) : FunctionalInequalities.Analysis.radialScale n • x ∈ K :=
    smul_mem_of_mem_closure hK hg.1 h0K (subset_closure hx)
      (radialScale_pos n).le (radialScale_lt_one n)
  have hmono : Monotone (fun n => (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal)) := by
    intro m n hmn
    exact EReal.coe_le_coe_iff.mpr
      (radial_mono h0K hg hnn hg0 (radialScale_pos m).le
        (radialScale_monotone hmn) (radialScale_pos n) (hmem n))
  have hcont : ContinuousAt g x := (hg.continuousOn hK).continuousAt (hK.mem_nhds hx)
  have htx : Tendsto (fun n => FunctionalInequalities.Analysis.radialScale n • x) atTop (nhds x) := by
    simpa only [one_smul] using radialScale_tendsto.smul (tendsto_const_nhds (x := x))
  have hlim : Tendsto (fun n => (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal)) atTop
      (nhds (g x : EReal)) := EReal.tendsto_coe.mpr (hcont.tendsto.comp htx)
  have he : FunctionalInequalities.Analysis.radialExtension K g x = ⨆ n, (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal) := by
    simp only [FunctionalInequalities.Analysis.radialExtension, FunctionalInequalities.Analysis.radialCut, if_pos (hmem _)]
  rw [he]
  exact iSup_eq_of_tendsto hmono hlim
private lemma FunctionalInequalities.Analysis.radialExtension_eq_top_off
    {K : Set E} {g : E → ℝ} {x : E} (hx : x ∉ closure K) :
    FunctionalInequalities.Analysis.radialExtension K g x = ⊤ := by
  classical
  have htx : Tendsto (fun n => FunctionalInequalities.Analysis.radialScale n • x) atTop (nhds x) := by
    simpa only [one_smul] using radialScale_tendsto.smul (tendsto_const_nhds (x := x))
  have hevent : ∀ᶠ n in atTop, FunctionalInequalities.Analysis.radialScale n • x ∉ closure K :=
    htx.eventually (isClosed_closure.isOpen_compl.mem_nhds hx)
  obtain ⟨n, hn⟩ := hevent.exists
  have hnot : FunctionalInequalities.Analysis.radialScale n • x ∉ K := fun h => hn (subset_closure h)
  apply top_unique
  have h : FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x ≤ FunctionalInequalities.Analysis.radialExtension K g x := le_iSup (fun n => FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x) n
  simpa [FunctionalInequalities.Analysis.radialCut, hnot] using h
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- **Radial extension of a convex function.** A nonnegative real convex function on an open convex set `K ∋ 0` vanishing at
`0` extends to a nonnegative extended-real function with convex real epigraph and Borel `toENNReal`, equal to it on `K`,
`⊤` off `closure K`, and equal at every point to its radial limit from below. -/
theorem FunctionalInequalities.Analysis.exists_radial_extension_of_convexOn [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) :
    ∃ ψ : E → EReal, (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ K, ψ x = (g x : EReal)) ∧
      (∀ x ∉ closure K, ψ x = ⊤) ∧
      (∀ x, Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1)) (nhds (ψ x))) := by
  refine ⟨FunctionalInequalities.Analysis.radialExtension K g, radialExtension_nonneg hnn, ?_,
    radialExtension_convex_epigraph hg,
    (measurable_radialExtension hK (hg.continuousOn hK)).ereal_toENNReal, ?_, ?_, ?_⟩
  · rw [radialExtension_eq_on hK h0K hg hnn hg0 h0K, hg0, EReal.coe_zero]
  · intro x hx
    exact radialExtension_eq_on hK h0K hg hnn hg0 hx
  · intro x hx
    exact radialExtension_eq_top_off hx
  · intro x
    exact radialExtension_radial_limit_readable hK h0K hg hnn hg0 x
end FiniteDimensional
end NormedSpace
end
end

open MeasureTheory
open scoped ENNReal
private theorem FunctionalInequalities.Probability.aemeasurable_toENNReal_comp_of_continuousOn_toReal {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace E] {μ : Measure X} {K : Set E} (hK : IsOpen K)
    {g : X → E} (hg : Continuous g) {φ : E → EReal} (hnn : ∀ y ∈ K, 0 ≤ φ y) (hfin : ∀ y ∈ K, φ y ≠ ⊤)
    (hcont : ContinuousOn (fun y => (φ y).toReal) K) (hae : ∀ᵐ x ∂μ, g x ∈ K) :
    AEMeasurable (fun x => (φ (g x)).toENNReal) μ := by
  let S : Set X := g ⁻¹' K
  have hS : IsOpen S := hK.preimage hg
  have hcore : ContinuousOn (fun x => ENNReal.ofReal ((φ (g x)).toReal)) S :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (hcont.comp hg.continuousOn (by intro x hx; exact hx))
  have heq : Set.EqOn (fun x => (φ (g x)).toENNReal)
      (fun x => ENNReal.ofReal ((φ (g x)).toReal)) S := by
    intro x hx
    change (φ (g x)).toENNReal = ENNReal.ofReal ((φ (g x)).toReal)
    have hc : ((φ (g x)).toReal : EReal) = φ (g x) :=
      EReal.coe_toReal (hfin _ hx) (ne_of_gt (EReal.bot_lt_zero.trans_le (hnn _ hx)))
    rw [← hc, EReal.real_coe_toENNReal, EReal.toReal_coe]
  have hcontinuous : ContinuousOn (fun x => (φ (g x)).toENNReal) S := hcore.congr heq
  have hm : AEMeasurable (fun x => (φ (g x)).toENNReal) (μ.restrict S) :=
    hcontinuous.aemeasurable hS.measurableSet
  have hrestrict : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem hae
  rwa [hrestrict] at hm
private theorem FunctionalInequalities.Probability.le_of_smul_of_convex_epigraph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → EReal} (hnn : ∀ x, 0 ≤ φ x) (hφ0 : φ 0 = 0)
    (hconv : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : E) :
    φ (t • x) ≤ φ x := by
  by_cases htop : φ x = ⊤
  · rw [htop]
    exact le_top
  have hbot : φ x ≠ ⊥ := ne_of_gt (EReal.bot_lt_zero.trans_le (hnn x))
  lift φ x to ℝ using ⟨htop, hbot⟩ with q hq
  have hq0 : 0 ≤ q := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [hq, EReal.coe_zero] using hnn x
  have hx : (x, q) ∈ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    change φ x ≤ (q : EReal)
    rw [hq]
  have hz : ((0 : E), (0 : ℝ)) ∈ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    change φ 0 ≤ (0 : EReal)
    rw [hφ0]
  have hepi := hconv hx hz ht0 (sub_nonneg.mpr ht1) (by ring : t + (1 - t) = 1)
  have hle : φ (t • x) ≤ (t * q : ℝ) := by
    change φ (t • x + (1 - t) • 0) ≤ (t * q + (1 - t) * 0 : ℝ) at hepi
    simpa only [smul_zero, mul_zero, add_zero] using hepi
  exact hle.trans (EReal.coe_le_coe_iff.mpr (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hq0))
private theorem FunctionalInequalities.Probability.ae_mem_closure_and_smul_mem_interior_convexHull_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    (∀ᵐ x ∂μ, x ∈ closure (interior (convexHull ℝ μ.support))) ∧
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ᵐ x ∂μ, t • x ∈ interior (convexHull ℝ μ.support) := by
  let C := convexHull ℝ μ.support
  have hc : Convex ℝ C := convex_convexHull ℝ μ.support
  have hclosed : closure (interior C) = closure C :=
    hc.closure_interior_eq_closure_of_nonempty_interior ⟨0, h0⟩
  have hae : ∀ᵐ x ∂μ, x ∈ closure (interior C) := by
    filter_upwards [μ.support_mem_ae] with x hx
    rw [hclosed]
    exact subset_closure (subset_convexHull ℝ μ.support hx)
  refine ⟨hae, ?_⟩
  intro t ht0 ht1
  filter_upwards [hae] with x hx
  have hxC : x ∈ closure C := by simpa only [hclosed] using hx
  have hh := hc.combo_interior_closure_mem_interior h0 hxC
    (sub_pos.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  simpa only [smul_zero, zero_add] using hh
/-- **CEK Lemma 17, first half (56a).** For a finite measure whose support hull contains `0` in its interior, nonnegative
convex extended-real functions vanishing at `0` with uniformly bounded lintegrals have a subsequence and a nonnegative convex
limit (finite and attained pointwise on the interior of the support hull, radially closed, `⊤` off its closure, Borel) whose
lintegral is at most the liminf of the lintegrals. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x))) ∧
      (∀ x, Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1)) (nhds (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      ∫⁻ x, (ψ x).toENNReal ∂μ ≤
        Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop := by
  let K : Set E := interior (convexHull ℝ μ.support)
  have hK : IsOpen K := isOpen_interior
  have hKconv : Convex ℝ K := (convex_convexHull ℝ μ.support).interior
  have h0K : (0 : E) ∈ K := h0
  let B : ℝ≥0∞ := ⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ
  have hB : B ≠ ⊤ := hbdd
  have hint (ℓ : ℕ) : (∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤ :=
    ne_of_lt ((le_iSup (fun j => ∫⁻ x, (φ j x).toENNReal ∂μ) ℓ).trans_lt (Ne.lt_top hB))
  have hbounds : ∀ x ∈ K, ∃ M : ℝ, ∀ ℓ, φ ℓ x ≤ (M : EReal) := by
    intro x hx
    obtain ⟨C, hC, hbound⟩ := FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_readable μ x hx
    refine ⟨C * B.toReal, ?_⟩
    intro ℓ
    have ht := hbound (φ ℓ) (hnn ℓ) (hconv ℓ) (hmeas ℓ) (hint ℓ)
    have hib : (∫⁻ y, (φ ℓ y).toENNReal ∂μ).toReal ≤ B.toReal :=
      ENNReal.toReal_mono hB (le_iSup (fun j => ∫⁻ y, (φ j y).toENNReal ∂μ) ℓ)
    exact ht.trans (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hib hC.le))
  have hfin : ∀ ℓ, ∀ x ∈ K, φ ℓ x ≠ ⊤ := by
    intro ℓ x hx
    obtain ⟨M, hM⟩ := hbounds x hx
    exact ne_of_lt ((hM ℓ).trans_lt (EReal.coe_lt_top M))
  have hcoe : ∀ ℓ, ∀ x ∈ K, ((φ ℓ x).toReal : EReal) = φ ℓ x := by
    intro ℓ x hx
    exact EReal.coe_toReal (hfin ℓ x hx)
      (ne_of_gt (EReal.bot_lt_zero.trans_le (hnn ℓ x)))
  have hrealconv : ∀ ℓ, ConvexOn ℝ K (fun x => (φ ℓ x).toReal) := by
    intro ℓ
    exact (FunctionalInequalities.Probability.real_convexOn_effective_domain_readable (hnn ℓ) (hconv ℓ)).subset
      (fun x hx => hfin ℓ x hx) hKconv
  have hrealbdd : ∀ x ∈ K, BddAbove (Set.range fun ℓ => (φ ℓ x).toReal) := by
    intro x hx
    obtain ⟨M, hM⟩ := hbounds x hx
    refine ⟨M, ?_⟩
    rintro r ⟨ℓ, rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [hcoe ℓ x hx]
    exact hM ℓ
  obtain ⟨s, g, hs, hgconv, hglim⟩ :=
    FunctionalInequalities.Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove_readable hK
      (fun ℓ x => (φ ℓ x).toReal) hrealconv
      (fun ℓ x hx => EReal.toReal_nonneg (hnn ℓ x)) hrealbdd
  have hgnn : ∀ x ∈ K, 0 ≤ g x := by
    intro x hx
    exact ge_of_tendsto (hglim x hx)
      (Filter.Eventually.of_forall fun j => EReal.toReal_nonneg (hnn (s j) x))
  have hg0 : g 0 = 0 := by
    have hz : Filter.Tendsto (fun j => (φ (s j) 0).toReal) Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [hφ0, EReal.toReal_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
    exact tendsto_nhds_unique (hglim 0 h0K) hz
  obtain ⟨ψ, hψnn, hψ0, hψconv, hψmeas, hψeq, hψoff, hψrad⟩ :=
    FunctionalInequalities.Analysis.exists_radial_extension_of_convexOn hK h0K hgconv hgnn hg0
  have hlim : ∀ x ∈ K, Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x)) := by
    intro x hx
    rw [hψeq x hx]
    have ht := (continuous_coe_real_ereal.tendsto (g x)).comp (hglim x hx)
    convert ht using 1
    funext j
    exact (hcoe (s j) x hx).symm
  refine ⟨s, ψ, hs, hψnn, hψ0, hψconv, hψmeas, ?_, hψrad, hψoff, ?_⟩
  · intro x hx
    refine ⟨?_, hlim x hx⟩
    rw [hψeq x hx]
    exact EReal.coe_ne_top _
  · have hscale := (FunctionalInequalities.Probability.ae_mem_closure_and_smul_mem_interior_convexHull_support μ h0).2
    let L : ℝ≥0∞ := Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop
    have hcontract : ∀ t : ℝ, 0 ≤ t → t < 1 → ∫⁻ x, (ψ (t • x)).toENNReal ∂μ ≤ L := by
      intro t ht0 ht1
      have himage : ∀ᵐ x ∂μ, t • x ∈ K := hscale t ht0 ht1
      have hscaledmeas : ∀ j, AEMeasurable (fun x => (φ (s j) (t • x)).toENNReal) μ := by
        intro j
        exact FunctionalInequalities.Probability.aemeasurable_toENNReal_comp_of_continuousOn_toReal hK
          (continuous_const.smul continuous_id) (fun y hy => hnn (s j) y)
          (hfin (s j)) ((hrealconv (s j)).continuousOn hK) himage
      have hscaledlim : ∀ᵐ x ∂μ, Filter.Tendsto
          (fun j => (φ (s j) (t • x)).toENNReal) Filter.atTop (nhds ((ψ (t • x)).toENNReal)) := by
        filter_upwards [himage] with x hx
        exact (EReal.continuous_toENNReal.tendsto (ψ (t • x))).comp (hlim _ hx)
      calc
        ∫⁻ x, (ψ (t • x)).toENNReal ∂μ =
            ∫⁻ x, Filter.liminf (fun j => (φ (s j) (t • x)).toENNReal) Filter.atTop ∂μ :=
          lintegral_congr_ae (hscaledlim.mono fun x hx => hx.liminf_eq.symm)
        _ ≤ Filter.liminf (fun j => ∫⁻ x, (φ (s j) (t • x)).toENNReal ∂μ) Filter.atTop :=
          lintegral_liminf_le' hscaledmeas
        _ ≤ L := Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j =>
          lintegral_mono fun x => EReal.toENNReal_le_toENNReal
            (FunctionalInequalities.Probability.le_of_smul_of_convex_epigraph (hnn (s j)) (hφ0 (s j)) (hconv (s j)) ht0 ht1.le x))
    have hradial : ∀ x, Filter.Tendsto (fun t : ℝ => (ψ (t • x)).toENNReal)
        (nhdsWithin 1 (Set.Iio 1)) (nhds ((ψ x).toENNReal)) := by
      intro x
      exact (EReal.continuous_toENNReal.tendsto (ψ x)).comp (hψrad x)
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), ∫⁻ x, (ψ (t • x)).toENNReal ∂μ ≤ L := by
      have hpos : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < t :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 ht1
      exact hcontract t ht0.le ht1
    calc
      ∫⁻ x, (ψ x).toENNReal ∂μ =
          ∫⁻ x, Filter.liminf (fun t : ℝ => (ψ (t • x)).toENNReal) (nhdsWithin 1 (Set.Iio 1)) ∂μ :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun x => (hradial x).liminf_eq.symm)
      _ ≤ Filter.liminf (fun t : ℝ => ∫⁻ x, (ψ (t • x)).toENNReal ∂μ) (nhdsWithin 1 (Set.Iio 1)) :=
        lintegral_liminf_le (fun t => hψmeas.comp (continuous_const.smul continuous_id).measurable)
      _ ≤ L := Filter.liminf_le_of_frequently_le' hev.frequently
