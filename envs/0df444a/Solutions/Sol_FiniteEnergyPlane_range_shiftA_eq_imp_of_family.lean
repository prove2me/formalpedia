-- Prove2me | solution 1 for FiniteEnergyPlane.range_shiftA_eq_imp_of_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T15:57:49.441509+00:00
-- url     : https://prove2.me/submissions/cb49bbe6-c3fe-4e17-8082-d1bb3695451d

import Definitions.Def_FiniteEnergyPlane_CylClose
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_injOn_ball_of_hasStrictFDerivAt
import Theorems.Thm_FiniteEnergyPlane_exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem range_shiftA_eq_imp_of_family_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u)
    (r : ℝ) (hr : 0 < r) (g : ℂ × ℝ → V 1) (hg : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hg0 : ∀ z, g (z, 0) = u z) (hne : ∀ t ∈ Set.Ioo (-r) r, ∀ z, g (z, t) ≠ 0)
    (hclose : ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
      IsCylCloseTo H ε (fun z => g (z, t)) u)
    (htr : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) :
    ∃ r' ∈ Set.Ioc 0 r, ∀ c ∈ Set.Ioo (-r') r', ∀ t ∈ Set.Ioo (-r') r',
      ∀ c' ∈ Set.Ioo (-r') r', ∀ t' ∈ Set.Ioo (-r') r',
        Set.range (shiftA c (fun z => g (z, t))) = Set.range (shiftA c' (fun z => g (z, t'))) →
          c = c' ∧ t = t' := by
  have hopen : IsOpen ((Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r) := isOpen_univ.prod isOpen_Ioo
  have h00 : ((0 : ℂ), (0 : ℝ)) ∈ (Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r :=
    ⟨Set.mem_univ _, by linarith, hr⟩
  have hgs : HasStrictFDerivAt g (fderiv ℝ g (0, 0)) ((0 : ℂ), (0 : ℝ)) :=
    (hg.contDiffAt (hopen.mem_nhds h00)).hasStrictFDerivAt (by norm_num)
  -- continuity of `u` from the slice `t = 0`
  have huc : Continuous u := by
    have hc : ContinuousOn g ((Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r) := hg.continuousOn
    have : u = g ∘ fun z : ℂ => (z, (0 : ℝ)) := by
      funext z
      exact (hg0 z).symm
    rw [this]
    exact hc.comp_continuous (by fun_prop) (fun z => ⟨Set.mem_univ _, by linarith, hr⟩)
  -- the map `(z, c, t) ↦ e^{2c} g(z, t)`
  let π₁ : (ℂ × ℝ × ℝ) →L[ℝ] ℂ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ)))
  let σ : (ℂ × ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))
  let x₀ : ℂ × ℝ × ℝ := (0, 0, 0)
  have hgc : HasStrictFDerivAt (fun q : ℂ × ℝ × ℝ => g (π₁ q)) ((fderiv ℝ g (0, 0)).comp π₁) x₀ := by
    have hπ : π₁ x₀ = ((0 : ℂ), (0 : ℝ)) := rfl
    exact HasStrictFDerivAt.comp x₀ (by rw [hπ]; exact hgs) π₁.hasStrictFDerivAt
  have hexp : HasStrictFDerivAt (fun q : ℂ × ℝ × ℝ => Real.exp (2 * σ q))
      (Real.exp (2 * σ x₀) • ((2 : ℝ) • σ)) x₀ :=
    (σ.hasStrictFDerivAt.const_mul 2).exp
  have hF := hexp.smul hgc
  have hinj : Function.Injective
      (Real.exp (2 * σ x₀) • (fderiv ℝ g (0, 0)).comp π₁ +
        (Real.exp (2 * σ x₀) • ((2 : ℝ) • σ)).smulRight (g (π₁ x₀))) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨Δ, δc, δt⟩ h
    have hσ0 : σ x₀ = 0 := rfl
    have hπ0 : π₁ x₀ = ((0 : ℂ), (0 : ℝ)) := rfl
    have h' : fderiv ℝ g (0, 0) (Δ, δt) + (2 * δc) • g (0, 0) = 0 := by
      simpa [hσ0, hπ0, π₁, σ, smul_eq_mul] using h
    obtain ⟨h1, h2, h3⟩ := htr Δ δt (2 * δc) h'
    have h4 : δc = 0 := by linarith
    rw [h1, h2, h4]
    rfl
  obtain ⟨δ, hδ, hball⟩ := injOn_ball_of_hasStrictFDerivAt hF hinj
  obtain ⟨η, hη, hsep⟩ := exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd H hH P u hu0 huc
    hue.1 huP δ hδ
  obtain ⟨r₁, ⟨hr₁, hr₁r⟩, hcl⟩ := hclose (η / 8) (by positivity)
  refine ⟨min r₁ (min δ (η / 8)), ⟨lt_min hr₁ (lt_min hδ (by positivity)),
    (min_le_left _ _).trans hr₁r⟩, ?_⟩
  set r' := min r₁ (min δ (η / 8)) with hr'
  have hr'1 : r' ≤ r₁ := min_le_left _ _
  have hr'2 : r' ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hr'3 : r' ≤ η / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ∀ {τ : ℝ}, τ ∈ Set.Ioo (-r') r' → τ ∈ Set.Ioo (-r₁) r₁ := fun hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hsubr : ∀ {τ : ℝ}, τ ∈ Set.Ioo (-r') r' → τ ∈ Set.Ioo (-r) r := fun hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  intro c hc t ht c' hc' t' ht' hrange
  have hmem : shiftA c (fun z => g (z, t)) 0 ∈ Set.range (shiftA c' (fun z => g (z, t'))) := by
    rw [← hrange]
    exact Set.mem_range_self _
  obtain ⟨z', hz'⟩ := hmem
  have hz'' : Real.exp (2 * c') • g (z', t') = Real.exp (2 * c) • g (0, t) := hz'
  have hn1 := hne t' (hsubr ht') z'
  have hn2 := hne t (hsubr ht) 0
  obtain ⟨hp1, ha1⟩ := proj_aCoord_exp_smul H hH c' _ hn1
  obtain ⟨hp2, ha2⟩ := proj_aCoord_exp_smul H hH c _ hn2
  rw [hz''] at hp1 ha1
  have hA : aCoord H (g (z', t')) + c' = aCoord H (g (0, t)) + c := by rw [← ha1, ha2]
  have hPr : proj H (g (z', t')) = proj H (g (0, t)) := by rw [← hp1, hp2]
  have hz'lt : ‖z'‖ < δ := by
    by_contra hcon
    have hs := hsep z' (not_lt.mp hcon)
    obtain ⟨c1, c2, -⟩ := hcl t' (hsub ht') z'
    obtain ⟨c3, c4, -⟩ := hcl t (hsub ht) 0
    have ha : |aCoord H (u z') - aCoord H (u 0)| ≤ η / 2 := by
      have e1 := abs_le.mp c1
      have e2 := abs_le.mp c3
      rw [abs_le]
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hc.1, hc.2, hc'.1, hc'.2]
    have hp : ‖proj H (u z') - proj H (u 0)‖ ≤ η / 4 := by
      have e : proj H (u z') - proj H (u 0) =
          -(proj H (g (z', t')) - proj H (u z')) + (proj H (g (0, t)) - proj H (u 0)) := by
        rw [hPr]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg]
      linarith
    linarith
  have hpt1 : ((0 : ℂ), c, t) ∈ Metric.ball x₀ δ := by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
    simp only [x₀, dist_self, Real.dist_eq, sub_zero]
    exact max_lt hδ (max_lt (abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩)
      (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩))
  have hpt2 : (z', c', t') ∈ Metric.ball x₀ δ := by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
    simp only [x₀, dist_zero_right, Real.dist_eq, sub_zero, Real.norm_eq_abs]
    exact max_lt hz'lt (max_lt (abs_lt.mpr ⟨by linarith [hc'.1], by linarith [hc'.2]⟩)
      (abs_lt.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩))
  have heq := hball hpt1 hpt2 hz''.symm
  simp only [Prod.mk.injEq] at heq
  exact ⟨heq.2.1, heq.2.2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u)
    (r : ℝ) (hr : 0 < r) (g : ℂ × ℝ → V 1) (hg : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hg0 : ∀ z, g (z, 0) = u z) (hne : ∀ t ∈ Set.Ioo (-r) r, ∀ z, g (z, t) ≠ 0)
    (hclose : ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
      IsCylCloseTo H ε (fun z => g (z, t)) u)
    (htr : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) :
    ∃ r' ∈ Set.Ioc 0 r, ∀ c ∈ Set.Ioo (-r') r', ∀ t ∈ Set.Ioo (-r') r',
      ∀ c' ∈ Set.Ioo (-r') r', ∀ t' ∈ Set.Ioo (-r') r',
        Set.range (shiftA c (fun z => g (z, t))) = Set.range (shiftA c' (fun z => g (z, t'))) →
          c = c' ∧ t = t' :=
  range_shiftA_eq_imp_of_family_aux H hH P u hu0 huP hue r hr g hg hg0 hne hclose htr
