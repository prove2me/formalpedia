-- Prove2me | solution 1 for ExploreFirst.LargeT.inv_kinf_shift
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:42:11.907214+00:00
-- url     : https://prove2.me/submissions/8e347eee-d4f9-4f61-b964-34418e8f11d3

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting

open ExploreFirst.LargeT
open MeasureTheory BanditAlgorithm

theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (εD : ℝ → ℝ)
    (ωD : Measure ℝ → ℝ → ℝ)
    (hwell : IsWellBehaved 𝒟 εD ωD)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (hμ : banditOptimalMean ν ∈ expectationInterior 𝒟)
    (hKpos : 0 < banditDInf 𝒟 (ν.P a) (banditOptimalMean ν))
    (hKfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν) ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < εD (banditOptimalMean ν)) :
    (let K₀ := banditDInf 𝒟 (ν.P a) (banditOptimalMean ν)
     1 / K₀.toReal * (1 - ε * ωD (ν.P a) (banditOptimalMean ν) / K₀.toReal) ≤
       1 / (banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε)).toReal) := by
  intro K₀
  have hlt : ∫ y, y ∂(ν.P a) < banditOptimalMean ν := by
    unfold banditGap banditArmMean at ha; linarith
  have hω := hwell.2.1 (ν.P a) (hν a) _ hμ
  have hupper := hwell.2.2 (ν.P a) (hν a) _ hμ hlt ε hε hεsmall
  have hmono : K₀ ≤ banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε) := by
    unfold K₀ banditDInf
    apply biInf_mono
    intro Q hQ
    exact ⟨hQ.1, by linarith [hQ.2]⟩
  have hw : 0 < ε * ωD (ν.P a) (banditOptimalMean ν) := mul_pos hε hω
  have hDfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hKfin, ENNReal.ofReal_ne_top⟩) hupper
  have hK : 0 < K₀.toReal := ENNReal.toReal_pos hKpos.ne' hKfin
  have h1 : K₀.toReal ≤ (banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε)).toReal :=
    ENNReal.toReal_mono hDfin hmono
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hKfin, ENNReal.ofReal_ne_top⟩) hupper
  rw [ENNReal.toReal_add hKfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hw.le] at h2
  set D := (banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε)).toReal
  set w := ε * ωD (ν.P a) (banditOptimalMean ν)
  set k := K₀.toReal
  have hD : 0 < D := lt_of_lt_of_le hK h1
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hK hD]
  have : (1 - w / k) * D ≤ (1 - w / k) * (k + w) ∨ 1 - w / k < 0 := by
    by_cases hc : 0 ≤ 1 - w / k
    · exact Or.inl (mul_le_mul_of_nonneg_left h2 hc)
    · exact Or.inr (lt_of_not_ge hc)
  have e : (1 - w / k) * (k + w) = k - w ^ 2 / k := by field_simp; ring
  rcases this with h | h
  · rw [e] at h
    have : 0 ≤ w ^ 2 / k := by positivity
    linarith
  · nlinarith
