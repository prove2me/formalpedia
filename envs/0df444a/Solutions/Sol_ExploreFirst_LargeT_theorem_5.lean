-- Prove2me | solution 1 for ExploreFirst.LargeT.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:58:07.750746+00:00
-- url     : https://prove2.me/submissions/4f09b951-918b-4a53-a329-d9af6bd35285

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting
import Theorems.Thm_ExploreFirst_LargeT_equation_17
import Theorems.Thm_ExploreFirst_LargeT_inv_kinf_shift
import Theorems.Thm_ExploreFirst_LargeT_product_ge

open MeasureTheory BanditAlgorithm ExploreFirst.LargeT

theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (εD : ℝ → ℝ) (ωD : Measure ℝ → ℝ → ℝ)
    (hwell : IsWellBehaved 𝒟 εD ωD)
    (π : BanditPolicy K) (C : ℝ)
    (hπ : IsUniformlySuperFast 𝒟 π C)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (hμ : banditOptimalMean ν ∈ expectationInterior 𝒟)
    (hKpos : 0 < banditDInf 𝒟 (ν.P a) (banditOptimalMean ν))
    (hKfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν) ≠ ⊤)
    (T : ℕ) :
    (let K₀ := banditDInf 𝒟 (ν.P a) (banditOptimalMean ν)
     let aT := ωD (ν.P a) (banditOptimalMean ν) / K₀.toReal *
       ((Real.log T) ^ 4)⁻¹
     let bT := C * hardness ν * Real.log T / (T : ℝ)
     let cT := Real.log ((K : ℝ) * C * (Real.log T) ^ 9) / Real.log T
     2 ≤ T →
       ((Real.log T) ^ 4)⁻¹ < εD (banditOptimalMean ν) →
       aT < 1 → bT < 1 → 0 ≤ cT → cT < 1 →
       Real.log T / K₀.toReal * (1 - (aT + bT + cT)) -
         Real.log 2 / K₀.toReal ≤ ExploreFirst.FundIneq.expPulls ν π T a) := by
  intro K₀ aT bT cT hT hεD haT hbT hcT0 hcT1
  set μs := banditOptimalMean ν with hμs
  set L := Real.log (T : ℝ) with hL
  set ε : ℝ := (L ^ 4)⁻¹ with hεdef
  set ω := ωD (ν.P a) μs with hω
  set E := ExploreFirst.FundIneq.expPulls ν π T a with hE
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hεpos : 0 < ε := by positivity
  -- basic facts about K₀ and Kε
  have hPa : ν.P a ∈ 𝒟 := hν a
  have hmeanlt : (∫ y, y ∂(ν.P a)) < μs := by
    have : banditGap ν a = μs - banditArmMean ν a := rfl
    have h2 : banditArmMean ν a = ∫ y, y ∂(ν.P a) := rfl
    linarith
  have hωpos : 0 < ω := hwell.2.1 _ hPa _ hμ
  set Kε := banditDInf 𝒟 (ν.P a) (μs + ε) with hKεdef
  have hmono : K₀ ≤ Kε := by
    show banditDInf 𝒟 (ν.P a) μs ≤ banditDInf 𝒟 (ν.P a) (μs + ε)
    unfold banditDInf
    apply iInf_mono'
    intro Q
    refine ⟨Q, ?_⟩
    apply iInf_mono'
    intro hQ
    exact ⟨⟨hQ.1, by linarith [hQ.2]⟩, le_rfl⟩
  have hKεle : Kε ≤ K₀ + ENNReal.ofReal (ε * ω) :=
    hwell.2.2 _ hPa _ hμ hmeanlt ε hεpos hεD
  have hKεfin : Kε ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ hKεle
    exact ENNReal.add_ne_top.2 ⟨hKfin, ENNReal.ofReal_ne_top⟩
  have hKεpos : 0 < Kε := lt_of_lt_of_le hKpos hmono
  have hκ0 : 0 < K₀.toReal := ENNReal.toReal_pos hKpos.ne' hKfin
  have hκε : 0 < Kε.toReal := ENNReal.toReal_pos hKεpos.ne' hKεfin
  have hκle : K₀.toReal ≤ Kε.toReal := ENNReal.toReal_mono hKεfin hmono
  -- hardness is nonnegative
  have hH : 0 ≤ hardness ν := by
    unfold hardness
    apply Finset.sum_nonneg
    intro b _
    positivity
  -- optimal arms: nonempty, card ≤ K
  have hAne : (ExploreFirst.Asymptotic.optimalArms ν).Nonempty := by
    haveI : Nonempty (Fin K) := ⟨a⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => banditArmMean ν i)
    refine ⟨i, ?_⟩
    simp only [ExploreFirst.Asymptotic.optimalArms, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have hA1 : (1 : ℝ) ≤ ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hAne
  have hAK : ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) ≤ (K : ℝ) := by
    have := Finset.card_le_univ (ExploreFirst.Asymptotic.optimalArms ν)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  -- general consequence of (17) for any positive constant C' ≥ C
  have h17 : ∀ C' : ℝ, 0 < C' → C ≤ C' → C' * hardness ν * L ≤ (T : ℝ) →
      (1 - C' * hardness ν * L / (T : ℝ)) *
        Real.log ((T : ℝ) * ε ^ 2 /
          ((ExploreFirst.Asymptotic.optimalArms ν).card * C' * L)) / Kε.toReal -
        Real.log 2 / Kε.toReal ≤ E := by
    intro C' hC' hCC' hb
    have hπ' : IsUniformlySuperFast 𝒟 π C' := by
      intro ν' hν' b hb' T' hT'
      refine le_trans (hπ ν' hν' b hb' T' hT') ?_
      have hlog : 0 ≤ Real.log (T' : ℝ) := Real.log_nonneg (by
        have : (2 : ℝ) ≤ T' := by exact_mod_cast hT'
        linarith)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hCC' hlog
    exact equation_17 𝒟 h𝒟 π C' hπ' ν hν a ha ε hεpos hKεpos hKεfin T hT hC' hb
  by_cases hC : 0 < C
  · -- main case
    have hb : C * hardness ν * L ≤ (T : ℝ) := by
      have : C * hardness ν * L / T < 1 := hbT
      rw [div_lt_one hTpos] at this
      linarith
    have key := h17 C hC le_rfl hb
    set A := ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) with hA
    -- logarithm estimate
    have hlogeq : Real.log ((T : ℝ) * ε ^ 2 / (A * C * L)) =
        L - Real.log (A * C * L ^ 9) := by
      have h1 : (T : ℝ) * ε ^ 2 / (A * C * L) = (T : ℝ) / (A * C * L ^ 9) := by
        rw [hεdef]
        field_simp
      rw [h1, Real.log_div hTpos.ne' (by positivity)]
    have hlogle : Real.log (A * C * L ^ 9) ≤ Real.log ((K : ℝ) * C * L ^ 9) := by
      apply Real.log_le_log (by positivity)
      have : 0 < C * L ^ 9 := by positivity
      nlinarith
    have hcTL : cT * L = Real.log ((K : ℝ) * C * L ^ 9) := by
      show Real.log ((K : ℝ) * C * (Real.log T) ^ 9) / Real.log T * L = _
      rw [← hL]
      field_simp
    have hlogge : L * (1 - cT) ≤ Real.log ((T : ℝ) * ε ^ 2 / (A * C * L)) := by
      rw [hlogeq]; nlinarith
    -- inverse information bound
    have hinv : 1 / K₀.toReal * (1 - ε * ω / K₀.toReal) ≤ 1 / Kε.toReal :=
      inv_kinf_shift 𝒟 h𝒟 εD ωD hwell ν hν a ha hμ hKpos hKfin ε hεpos hεD
    have haTeq : aT = ε * ω / K₀.toReal := by
      show ωD (ν.P a) (banditOptimalMean ν) / K₀.toReal * ((Real.log T) ^ 4)⁻¹ = _
      rw [← hL, ← hεdef, ← hω]; ring
    have haT0 : 0 ≤ aT := by rw [haTeq]; positivity
    have hbT0 : 0 ≤ bT := by
      show 0 ≤ C * hardness ν * Real.log T / (T : ℝ)
      rw [← hL]; positivity
    have hprod := product_ge aT bT cT haT0 haT.le
      hbT0 hbT.le hcT0 hcT1.le
    have hbTeq : bT = C * hardness ν * L / T := rfl
    -- assemble
    have step1 : (1 - bT) * (L * (1 - cT)) * (1 / Kε.toReal) ≤
        (1 - bT) * Real.log ((T : ℝ) * ε ^ 2 / (A * C * L)) / Kε.toReal := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right _ hκε.le
      apply mul_le_mul_of_nonneg_left hlogge (by linarith)
    have hnn : 0 ≤ (1 - bT) * (L * (1 - cT)) := by
      apply mul_nonneg (by linarith); apply mul_nonneg hLpos.le (by linarith)
    have step2 : (1 - bT) * (L * (1 - cT)) * (1 / K₀.toReal * (1 - aT)) ≤
        (1 - bT) * (L * (1 - cT)) * (1 / Kε.toReal) := by
      apply mul_le_mul_of_nonneg_left _ hnn
      rw [haTeq]; exact hinv
    have step3 : L / K₀.toReal * (1 - (aT + bT + cT)) ≤
        (1 - bT) * (L * (1 - cT)) * (1 / K₀.toReal * (1 - aT)) := by
      have : L / K₀.toReal * (1 - (aT + bT + cT)) ≤
          L / K₀.toReal * ((1 - aT) * (1 - bT) * (1 - cT)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      calc _ ≤ _ := this
        _ = _ := by field_simp
    have step4 : Real.log 2 / Kε.toReal ≤ Real.log 2 / K₀.toReal :=
      div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hκ0 hκle
    have key' : (1 - bT) * Real.log ((T : ℝ) * ε ^ 2 / (A * C * L)) / Kε.toReal -
        Real.log 2 / Kε.toReal ≤ E := by
      rw [hbTeq]; exact key
    linarith
  · -- degenerate case C ≤ 0: the bound (17) with tiny constants is contradictory
    exfalso
    push Not at hC
    set A := ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) with hA
    set Q : ℝ := (T : ℝ) * ε ^ 2 / (A * L) with hQ
    have hQpos : 0 < Q := by positivity
    set M : ℝ := |Real.log Q| + 2 * |Kε.toReal * E + Real.log 2| + 1 with hM
    set C' : ℝ := min (Real.exp (-M)) ((T : ℝ) / (2 * (hardness ν * L + 1))) with hC'
    have hC'pos : 0 < C' := by
      apply lt_min (Real.exp_pos _); positivity
    have hC'le1 : C' ≤ Real.exp (-M) := min_le_left _ _
    have hC'le2 : C' ≤ (T : ℝ) / (2 * (hardness ν * L + 1)) := min_le_right _ _
    have hHL : 0 ≤ hardness ν * L := mul_nonneg hH hLpos.le
    have hbhalf : C' * hardness ν * L / T ≤ 1 / 2 := by
      rw [div_le_iff₀ hTpos]
      rw [le_div_iff₀ (by positivity)] at hC'le2
      nlinarith
    have hb : C' * hardness ν * L ≤ (T : ℝ) := by
      have := hbhalf; rw [div_le_iff₀ hTpos] at this; linarith
    have key := h17 C' hC'pos (by linarith) hb
    have hlogC' : Real.log C' ≤ -M := by
      calc Real.log C' ≤ Real.log (Real.exp (-M)) := Real.log_le_log hC'pos hC'le1
        _ = -M := Real.log_exp _
    have hlogeq : Real.log ((T : ℝ) * ε ^ 2 / (A * C' * L)) = Real.log Q - Real.log C' := by
      have : (T : ℝ) * ε ^ 2 / (A * C' * L) = Q / C' := by
        rw [hQ]; field_simp
      rw [this, Real.log_div hQpos.ne' hC'pos.ne']
    have hbig : 2 * |Kε.toReal * E + Real.log 2| + 1 ≤
        Real.log ((T : ℝ) * ε ^ 2 / (A * C' * L)) := by
      rw [hlogeq]
      have := neg_abs_le (Real.log Q)
      linarith
    set G := Real.log ((T : ℝ) * ε ^ 2 / (A * C' * L)) with hG
    have hGpos : 0 ≤ G := by linarith [abs_nonneg (Kε.toReal * E + Real.log 2)]
    have hfac : (1 - C' * hardness ν * L / (T : ℝ)) * G ≥ G / 2 := by
      have h := mul_le_mul_of_nonneg_right hbhalf hGpos
      have e : (1 - C' * hardness ν * L / (T : ℝ)) * G = G - (C' * hardness ν * L / (T : ℝ)) * G := by ring
      rw [e]; linarith
    have hmain : (1 - C' * hardness ν * L / (T : ℝ)) * G - Real.log 2 ≤ Kε.toReal * E := by
      have h1 : ((1 - C' * hardness ν * L / (T : ℝ)) * G - Real.log 2) / Kε.toReal ≤ E := by
        rw [sub_div]; exact key
      rw [div_le_iff₀ hκε] at h1
      linarith
    have habs := le_abs_self (Kε.toReal * E + Real.log 2)
    clear_value G
    linarith [hbig, hfac, hmain, habs, Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
