-- Prove2me | solution 1 for FiniteEnergyPlane.energy_ge_of_mapsTo_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T17:06:21.957602+00:00
-- url     : https://prove2.me/submissions/043699a1-4325-496a-9102-7ba0703b6d9e

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_fderiv_ne_zero_of_isCompact_fiber
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
import Theorems.Thm_FiniteEnergyPlane_energy_ge_of_almostComplex
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

set_option maxHeartbeats 1000000 in
/-- Monotonicity lemma (Zinger, Proposition 3.12). -/
theorem energy_ge_of_mapsTo_ball_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ U : Set ℂ, IsOpen U → ∀ u : ℂ → E, ContDiffOn ℝ ∞ u U →
        JHolomorphic.IsJHolomorphicOn J U u → Set.MapsTo u U (ball p r) →
        (∀ L : Set E, IsCompact L → L ⊆ ball p r → IsCompact (U ∩ u ⁻¹' L)) → p ∈ u '' U →
        ENNReal.ofReal (c * r ^ 2) ≤ ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := by
  obtain ⟨hOo, hJs, hJ2⟩ := hJ
  obtain ⟨δ, hδ, D, hD, hLip⟩ :=
    exists_lipschitz_near_compact hOo (hJs.of_le (by exact_mod_cast le_top)) hK hKO
  -- a Euclidean model of `E`
  let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  set TL : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) with hTL
  set SL : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E :=
    (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E) with hSL
  have hST : ∀ w, TL (SL w) = w := fun w => T.apply_symm_apply w
  have hTS : ∀ v, SL (TL v) = v := fun v => T.symm_apply_apply v
  set τ := ‖TL‖ + 1 with hτdef
  set τ' := ‖SL‖ + 1 with hτ'def
  have hτ : 0 < τ := by positivity
  have hτ' : 0 < τ' := by positivity
  have hSn : ∀ w, ‖SL w‖ ≤ τ' * ‖w‖ := fun w =>
    (SL.le_opNorm w).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hconj : ∀ B : E →L[ℝ] E, ‖TL ∘L B ∘L SL‖ ≤ τ * ‖B‖ * τ' := by
    intro B
    calc ‖TL ∘L B ∘L SL‖ ≤ ‖TL‖ * (‖B‖ * ‖SL‖) :=
          (TL.opNorm_comp_le _).trans
            (mul_le_mul_of_nonneg_left (B.opNorm_comp_le SL) (norm_nonneg _))
      _ ≤ τ * (‖B‖ * τ') := by
          gcongr
          · linarith
          · linarith
      _ = τ * ‖B‖ * τ' := by ring
  obtain ⟨cM, hcM, κ, hκ, hM⟩ :=
    energy_ge_of_almostComplex (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (τ * D * τ')
  refine ⟨min δ (κ / (τ * D * τ' + 1)), lt_min hδ (by positivity),
    cM / (4 * τ ^ 2 * τ' ^ 2), by positivity, ?_⟩
  intro p hp r hr hr₀ U hU u hu hhol hmaps hprop hpU
  have hrδ : r ≤ δ := hr₀.trans (min_le_left _ _)
  have hrκ : r ≤ κ / (τ * D * τ' + 1) := hr₀.trans (min_le_right _ _)
  obtain ⟨hBO, hLp⟩ := hLip p hp
  have hballδ : ball p r ⊆ closedBall p δ :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hrδ)
  have hdiff : DifferentiableOn ℝ u U := hu.differentiableOn (by simp)
  -- a regular point near `p`
  have hfib : IsCompact (U ∩ u ⁻¹' {p}) :=
    hprop {p} isCompact_singleton (singleton_subset_iff.2 (mem_ball_self hr))
  obtain ⟨z₁, hz₁U, hz₁p, hz₁⟩ :=
    exists_fderiv_ne_zero_of_isCompact_fiber hU hdiff hpU hfib (half_pos hr)
  have hqB : u z₁ ∈ closedBall p δ := hballδ (hmaps hz₁U)
  have hqO : u z₁ ∈ O := hBO hqB
  -- the transferred data
  set S := r / (2 * τ') with hSdef
  have hS : 0 < S := by positivity
  have hS' : τ' * S = r / 2 := by rw [hSdef]; field_simp
  set Λ := τ * D * τ' ^ 2 with hΛdef
  set A : ℂ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun z => TL ∘L J (u z) ∘L SL with hAdef
  set J₀ := A z₁ with hJ₀def
  set ũ : ℂ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun z => TL (u z) with hũdef
  have hDũ : ∀ z, fderiv ℝ ũ z = TL ∘L fderiv ℝ u z := fun z => T.comp_fderiv
  have hJ₀2 : J₀.comp J₀ = -ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h := congrArg (fun B => B (SL w)) (hJ2 (u z₁) hqO)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply] at h
    simp only [hJ₀def, hAdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, hTS, h, map_neg, hST]
  have hJ₀b : ‖J₀‖ ≤ τ * D * τ' := by
    calc ‖J₀‖ ≤ τ * ‖J (u z₁)‖ * τ' := hconj _
      _ ≤ τ * D * τ' := by gcongr; exact (hLp (u z₁) hqB).1
  have hΛS : Λ * S ≤ κ := by
    have h1 := (le_div_iff₀ (by positivity)).1 hrκ
    have e : Λ * S = τ * D * τ' * r / 2 := by rw [hΛdef, hSdef]; field_simp; try ring
    have h0 : 0 ≤ τ * D * τ' * r := by positivity
    rw [e]; nlinarith
  have hũ : ContDiffOn ℝ 2 ũ U := TL.contDiff.comp_contDiffOn (hu.of_le (by norm_cast))
  have hhol' : ∀ z ∈ U, ‖ũ z - TL (u z₁)‖ < S →
      fderiv ℝ ũ z Complex.I = A z (fderiv ℝ ũ z 1) ∧
        ‖A z - J₀‖ ≤ Λ * ‖ũ z - TL (u z₁)‖ := by
    intro z hz _
    have hzB : u z ∈ closedBall p δ := hballδ (hmaps hz)
    have hzO : u z ∈ O := hBO hzB
    refine ⟨?_, ?_⟩
    · have h1 := (hhol z hz).2
      simp only [JHolomorphic.dbarJ] at h1
      have h2 := congrArg (fun B => B (fderiv ℝ u z Complex.I)) (hJ2 (u z) hzO)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply] at h2
      have h3 : fderiv ℝ u z Complex.I = J (u z) (fderiv ℝ u z 1) := by
        have h4 := congrArg (J (u z)) h1
        rw [map_add, h2, map_zero] at h4
        exact (add_neg_eq_zero.1 h4).symm
      rw [hDũ]
      simp only [hAdef, ContinuousLinearMap.comp_apply, hTS, h3]
    · have e : A z - J₀ = TL ∘L (J (u z) - J (u z₁)) ∘L SL := by
        simp only [hJ₀def, hAdef, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      rw [e]
      have hJl := (hLp (u z) hzB).2 (u z₁) hqB
      have hw : ‖u z - u z₁‖ ≤ τ' * ‖ũ z - TL (u z₁)‖ := by
        have h5 : u z - u z₁ = SL (ũ z - TL (u z₁)) := by
          rw [hũdef]; simp only [map_sub, hTS]
        rw [h5]; exact hSn _
      calc ‖TL ∘L (J (u z) - J (u z₁)) ∘L SL‖ ≤ τ * ‖J (u z) - J (u z₁)‖ * τ' := hconj _
        _ ≤ τ * (D * (τ' * ‖ũ z - TL (u z₁)‖)) * τ' := by
            gcongr; exact hJl.trans (mul_le_mul_of_nonneg_left hw hD)
        _ = Λ * ‖ũ z - TL (u z₁)‖ := by rw [hΛdef]; ring
  have hprop' : ∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖ũ z - TL (u z₁)‖ ≤ ρ} := by
    intro ρ hρ
    have hLc : IsCompact (TL ⁻¹' closedBall (TL (u z₁)) ρ) := by
      have h6 := (isCompact_closedBall (TL (u z₁)) ρ).image SL.continuous
      convert h6 using 1
      ext y
      constructor
      · intro hy; exact ⟨TL y, hy, hTS y⟩
      · rintro ⟨w, hw, rfl⟩; simpa only [mem_preimage, hST] using hw
    have hLsub : TL ⁻¹' closedBall (TL (u z₁)) ρ ⊆ ball p r := by
      intro y hy
      rw [mem_preimage, mem_closedBall, dist_eq_norm] at hy
      have h1 : ‖y - u z₁‖ ≤ τ' * ρ := by
        have h5 : y - u z₁ = SL (TL y - TL (u z₁)) := by simp only [map_sub, hTS]
        rw [h5]; exact (hSn _).trans (mul_le_mul_of_nonneg_left hy hτ'.le)
      have h2 : τ' * ρ < r / 2 := by rw [← hS']; exact mul_lt_mul_of_pos_left hρ hτ'
      rw [mem_ball, dist_eq_norm]
      calc ‖y - p‖ = ‖(y - u z₁) + (u z₁ - p)‖ := by congr 1; abel
        _ ≤ ‖y - u z₁‖ + ‖u z₁ - p‖ := norm_add_le _ _
        _ < r := by linarith
    convert hprop _ hLc hLsub using 1
    ext z
    simp only [hũdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_closedBall, dist_eq_norm]
  have hreg : ∃ z ∈ U, ũ z = TL (u z₁) ∧ fderiv ℝ ũ z ≠ 0 := by
    refine ⟨z₁, hz₁U, rfl, ?_⟩
    rw [hDũ]
    intro h0
    apply hz₁
    refine ContinuousLinearMap.ext fun w => ?_
    have h7 := congrArg (fun B => SL (B w)) h0
    simpa only [ContinuousLinearMap.comp_apply, hTS, ContinuousLinearMap.zero_apply,
      map_zero] using h7
  have hE := hM J₀ hJ₀2 hJ₀b Λ S (by positivity) hS hΛS (TL (u z₁)) U ũ A hU hũ hhol' hprop' hreg
  -- comparison of the energies
  have hcmp : ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ ũ z‖ ^ 2) ≤
      ENNReal.ofReal (τ ^ 2) * ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_mul (by positivity), hDũ]
    refine ENNReal.ofReal_le_ofReal ?_
    have h' : ‖TL ∘L fderiv ℝ u z‖ ≤ τ * ‖fderiv ℝ u z‖ :=
      (TL.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    calc ‖TL ∘L fderiv ℝ u z‖ ^ 2 ≤ (τ * ‖fderiv ℝ u z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h' 2
      _ = τ ^ 2 * ‖fderiv ℝ u z‖ ^ 2 := by ring
  have hval : ENNReal.ofReal (cM * S ^ 2) =
      ENNReal.ofReal (τ ^ 2) * ENNReal.ofReal (cM / (4 * τ ^ 2 * τ' ^ 2) * r ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hSdef]; field_simp; ring
  have h8 := hE.trans hcmp
  rw [hval] at h8
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne'
    ENNReal.ofReal_ne_top).1 h8

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ U : Set ℂ, IsOpen U → ∀ u : ℂ → E, ContDiffOn ℝ ∞ u U →
        JHolomorphic.IsJHolomorphicOn J U u → Set.MapsTo u U (ball p r) →
        (∀ L : Set E, IsCompact L → L ⊆ ball p r → IsCompact (U ∩ u ⁻¹' L)) → p ∈ u '' U →
        ENNReal.ofReal (c * r ^ 2) ≤ ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) :=
  energy_ge_of_mapsTo_ball_aux J O hJ K hK hKO
