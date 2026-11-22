-- Prove2me | solution 1 for FiniteEnergyPlane.embedded_fastPlane_fredholm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:46:04.550098+00:00
-- url     : https://prove2.me/submissions/2b51ccdf-7430-48a8-b5fb-79ee903876e6

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_isProperEmbedding_proj_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_family
import Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_shiftA_comp_affine_of_range_eq
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_eq_of_tendsto_of_injective_fderiv



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma eff_tendsto_apply {v : ℕ → ℂ → V 1} {g : ℂ → V 1}
    (hconv : JHolomorphic.TendstoCInftyLocOn v g Set.univ) (z : ℂ) :
    Tendsto (fun k => v k z) atTop (𝓝 (g z)) := by
  have h := (hconv {z} (Set.subset_univ _) isCompact_singleton 0).tendsto_at
    (Set.mem_singleton z)
  have h2 := ((continuousMultilinearCurryFin0 ℝ ℂ (V 1)).continuous.tendsto _).comp h
  simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using h2

lemma eff_finrank : Module.finrank ℝ (ℂ × ℂ) = Module.finrank ℝ (V 1) := by
  simp [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_fin_fun]

theorem embedded_fastPlane_fredholm_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    P.IsCZAtLeast 3 → ∀ u : ℂ → V 1, IsFastPlane H J u → IsNondegenerateEnd H u cylInf P 1 →
    IsEmbeddedPlane u →
    (∀ z, proj H (u z) ∉ Set.range P.x) ∧ (Function.Injective (proj H ∘ u) ∧
      (∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z)) ∧
      ∀ K : Set (V 1), IsCompact K → Disjoint K (Set.range P.x) →
        Bornology.IsBounded ((proj H ∘ u) ⁻¹' K)) ∧
    ∀ l : ℕ, 1 ≤ l → ∃ r > 0, ∃ f : ℂ × ℂ → V 1, ContDiffOn ℝ l f (Set.univ ×ˢ ball (0 : ℂ) r) ∧ Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p)) ∧
      (∀ z, f (z, 0) = u z) ∧
      (∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
        IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ))) ∧
      ∀ τ₀ ∈ ball (0 : ℂ) r, ∀ v : ℕ → ℂ → V 1,
        (∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
          IsEmbeddedPlane (v k)) →
        JHolomorphic.TendstoCInftyLocOn v (fun z => f (z, τ₀)) Set.univ →
        ∃ τ A B : ℕ → ℂ, Tendsto τ atTop (𝓝 τ₀) ∧ Tendsto A atTop (𝓝 1) ∧
          Tendsto B atTop (𝓝 0) ∧
          ∀ᶠ k in atTop, τ k ∈ ball (0 : ℂ) r ∧ ∀ z, f (A k * z + B k, τ k) = v k z := by
  classical
  intro H J hJ P hcz u hu huP hue
  have hH : IsStrictlyStarShapedLevel H := (periodicOrbit_bridge H₀).1.2 hH₀
  have hA := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz u hu huP hue
  refine ⟨hA, isProperEmbedding_proj_of_isFastPlane H hH J hJ P u hu huP hA, ?_⟩
  intro l hl
  obtain ⟨r, hr, f, hfC, hfI, hfd, hf0, hfam, -⟩ :=
    exists_fastPlane_family H hH J hJ P hcz u hu huP hue l hl
  refine ⟨r, hr, f, hfC, hfI, hfd, hf0, hfam, ?_⟩
  intro τ₀ hτ₀ v hv hconv
  set U : Set (ℂ × ℂ) := Set.univ ×ˢ ball (0 : ℂ) r with hUdef
  have hU : IsOpen U := isOpen_univ.prod isOpen_ball
  have hf1 : ContDiffOn ℝ 1 f U := hfC.of_le (by exact_mod_cast hl)
  have hpt := eff_tendsto_apply hconv
  obtain ⟨x0, hx0, hx0e⟩ := exists_tendsto_eq_of_tendsto_of_injective_fderiv eff_finrank f U hU
    hf1 hfd (0, τ₀) ⟨Set.mem_univ _, hτ₀⟩ (fun k => v k 0) (hpt 0)
  obtain ⟨x1, hx1, hx1e⟩ := exists_tendsto_eq_of_tendsto_of_injective_fderiv eff_finrank f U hU
    hf1 hfd (1, τ₀) ⟨Set.mem_univ _, hτ₀⟩ (fun k => v k 1) (hpt 1)
  -- every good parameter carries `v k` as an affine reparametrization of a family member
  have key : ∀ k, x0 k ∈ U → f (x0 k) = v k 0 →
      ∃ A : ℂ, ∀ z, f (A * z + (x0 k).1, (x0 k).2) = v k z := by
    intro k hk hke
    set w : ℂ → V 1 := fun z => f (z, (x0 k).2) with hwdef
    obtain ⟨hw, hwP, hwe⟩ := hfam _ hk.2
    obtain ⟨hvk, hvkP, hvke⟩ := hv k
    have hwm := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz w hw hwP hwe
    have hvm := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz (v k) hvk hvkP hvke
    have hw0 : w (x0 k).1 = v k 0 := by
      simp only [hwdef, Prod.mk.eta]
      exact hke
    have hv0 : v k 0 ≠ 0 := hvk.1.2.1 0 (Set.mem_univ _)
    rcases range_eq_or_disjoint_of_isFastPlane H hH J hJ P w (v k) hw hwP hwe hvk hvkP hvke
      hwm hvm with heq | hdisj
    · obtain ⟨c, A, B, -, hAB⟩ :=
        exists_shiftA_comp_affine_of_range_eq H hH J hJ P hcz w (v k) hw hwP hwe hvk hvkP hvke heq
      have hwB : w B = Real.exp (2 * c) • v k 0 := by
        have := hAB 0
        simpa [shiftA] using this
      have hinj := (isProperEmbedding_proj_of_isFastPlane H hH J hJ P w hw hwP hwm).1
      have hB : B = (x0 k).1 := by
        apply hinj
        simp only [Function.comp_apply]
        rw [hwB, hw0, (proj_aCoord_exp_smul H hH c (v k 0) hv0).1]
      have hc : Real.exp (2 * c) = 1 := by
        have h1 : Real.exp (2 * c) • v k 0 = (1 : ℝ) • v k 0 := by
          rw [one_smul, ← hwB, hB, hw0]
        exact smul_left_injective ℝ hv0 h1
      refine ⟨A, fun z => ?_⟩
      have := hAB z
      simp only [shiftA, hc, one_smul, hwdef] at this
      rw [← hB]
      exact this
    · exfalso
      refine Set.disjoint_left.mp hdisj ⟨(x0 k).1, rfl⟩ ⟨0, ?_⟩
      simp only [Function.comp_apply]
      rw [hw0]
  refine ⟨fun k => (x0 k).2,
    fun k => if h : x0 k ∈ U ∧ f (x0 k) = v k 0 then Classical.choose (key k h.1 h.2) else 1,
    fun k => (x0 k).1, ?_, ?_, ?_, ?_⟩
  · exact (continuous_snd.tendsto _).comp hx0
  · have hgood : ∀ᶠ k in atTop, (x0 k ∈ U ∧ f (x0 k) = v k 0) ∧ (x1 k ∈ U ∧ f (x1 k) = v k 1) :=
      hx0e.and hx1e
    have hlim : Tendsto (fun k => (x1 k).1 - (x0 k).1) atTop (𝓝 1) := by
      have h1 := (continuous_fst.tendsto _).comp hx1
      have h0 := (continuous_fst.tendsto _).comp hx0
      simpa using h1.sub h0
    refine hlim.congr' ?_
    filter_upwards [hgood] with k ⟨hk0, hk1⟩
    rw [dif_pos hk0]
    have hspec := Classical.choose_spec (key k hk0.1 hk0.2)
    set A := Classical.choose (key k hk0.1 hk0.2)
    have hmem : (A * 1 + (x0 k).1, (x0 k).2) ∈ U := ⟨Set.mem_univ _, hk0.1.2⟩
    have heq : (A * 1 + (x0 k).1, (x0 k).2) = x1 k :=
      hfI hmem hk1.1 ((hspec 1).trans hk1.2.symm)
    have := congrArg Prod.fst heq
    simp only [mul_one] at this
    rw [← this]
    ring
  · exact (continuous_fst.tendsto _).comp hx0
  · filter_upwards [hx0e] with k hk
    refine ⟨hk.1.2, fun z => ?_⟩
    simp only [dif_pos hk]
    exact Classical.choose_spec (key k hk.1 hk.2) z

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    P.IsCZAtLeast 3 → ∀ u : ℂ → V 1, IsFastPlane H J u → IsNondegenerateEnd H u cylInf P 1 →
    IsEmbeddedPlane u →
    (∀ z, proj H (u z) ∉ Set.range P.x) ∧ (Function.Injective (proj H ∘ u) ∧
      (∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z)) ∧
      ∀ K : Set (V 1), IsCompact K → Disjoint K (Set.range P.x) →
        Bornology.IsBounded ((proj H ∘ u) ⁻¹' K)) ∧
    ∀ l : ℕ, 1 ≤ l → ∃ r > 0, ∃ f : ℂ × ℂ → V 1, ContDiffOn ℝ l f (Set.univ ×ˢ ball (0 : ℂ) r) ∧ Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p)) ∧
      (∀ z, f (z, 0) = u z) ∧
      (∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
        IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ))) ∧
      ∀ τ₀ ∈ ball (0 : ℂ) r, ∀ v : ℕ → ℂ → V 1,
        (∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
          IsEmbeddedPlane (v k)) →
        JHolomorphic.TendstoCInftyLocOn v (fun z => f (z, τ₀)) Set.univ →
        ∃ τ A B : ℕ → ℂ, Tendsto τ atTop (𝓝 τ₀) ∧ Tendsto A atTop (𝓝 1) ∧
          Tendsto B atTop (𝓝 0) ∧
          ∀ᶠ k in atTop, τ k ∈ ball (0 : ℂ) r ∧ ∀ z, f (A k * z + B k, τ k) = v k z :=
  FiniteEnergyPlane.embedded_fastPlane_fredholm_aux H₀ hH₀
