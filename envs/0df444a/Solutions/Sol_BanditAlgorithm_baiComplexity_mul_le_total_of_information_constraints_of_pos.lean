-- Prove2me | solution 1 for BanditAlgorithm.baiComplexity_mul_le_total_of_information_constraints_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:08:21.141283+00:00
-- url     : https://prove2.me/submissions/2d426bd9-9f00-47d6-97ab-f96f7c1e41d6

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 0 < k) (𝓔 : Set (StochasticBandit k)) (ν : StochasticBandit k)
    (c : Fin k → ℝ≥0∞) (L : ℝ≥0∞)
    (hinfo : ∀ ν' ∈ baiAlternatives 𝓔 ν,
      L ≤ ∑ i, c i * klDiv (ν.P i) (ν'.P i)) :
    BanditAlgorithm.baiComplexity ν 𝓔 * L ≤ ∑ i, c i := by
  classical
  let T : ℝ≥0∞ := ∑ i, c i
  change baiComplexity ν 𝓔 * L ≤ T
  by_cases hTtop : T = ⊤
  · simp [hTtop]
  by_cases halt : (baiAlternatives 𝓔 ν).Nonempty
  · obtain ⟨ν₀, hν₀⟩ := halt
    letI : Nonempty (StochasticBandit k) := ⟨ν⟩
    by_cases hT0 : T = 0
    · have hc0 : ∀ i, c i = 0 := by
        intro i
        apply bot_unique
        have hi : c i ≤ T := by
          exact Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)
        simpa [hT0] using hi
      have hL0 : L = 0 := by
        apply bot_unique
        simpa [hc0] using hinfo ν₀ hν₀
      simp [hL0]
    let α : Fin k → ℝ≥0 := fun i ↦ (c i / T).toNNReal
    have hcfin (i : Fin k) : c i ≠ ⊤ := by
      intro hi
      have : T = ⊤ := by
        apply top_unique
        calc
          ⊤ = c i := hi.symm
          _ ≤ T := Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)
      exact hTtop this
    have hdivfin (i : Fin k) : c i / T ≠ ⊤ := by
      rw [ENNReal.div_eq_inv_mul]
      exact ENNReal.mul_ne_top (by simp [hT0]) (hcfin i)
    have hαcoe (i : Fin k) : (α i : ℝ≥0∞) = c i / T := by
      exact ENNReal.coe_toNNReal (hdivfin i)
    have hαsum : ∑ i, α i = 1 := by
      apply ENNReal.coe_injective
      rw [ENNReal.coe_one, ENNReal.coe_finset_sum]
      simp_rw [hαcoe]
      simp_rw [ENNReal.div_eq_inv_mul]
      calc
        ∑ i, T⁻¹ * c i = T⁻¹ * ∑ i, c i := by
          simpa using (Finset.mul_sum Finset.univ c T⁻¹).symm
        _ = T⁻¹ * T := by rfl
        _ = 1 := ENNReal.inv_mul_cancel hT0 hTtop
    let J : ℝ≥0∞ :=
      ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
        ∑ i, (α i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)
    have hLJ : L ≤ T * J := by
      dsimp [J]
      rw [ENNReal.mul_iInf]
      · apply le_iInf
        intro ν'
        by_cases hν' : ν' ∈ baiAlternatives 𝓔 ν
        · letI : Nonempty (ν' ∈ baiAlternatives 𝓔 ν) := ⟨hν'⟩
          rw [ENNReal.mul_iInf]
          · apply le_iInf
            intro _
            calc
              L ≤ ∑ i, c i * klDiv (ν.P i) (ν'.P i) := hinfo ν' hν'
              _ = T * ∑ i, (α i : ℝ≥0∞) *
                    klDiv (ν.P i) (ν'.P i) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                rw [hαcoe, ENNReal.div_eq_inv_mul]
                rw [← mul_assoc T (T⁻¹ * c i), ← mul_assoc T T⁻¹,
                  ENNReal.mul_inv_cancel hT0 hTtop, one_mul]
          · intro htop hzero
            exact (hTtop htop).elim
        · simp [hν', hT0]
      · intro htop hzero
        exact (hTtop htop).elim
    let I : ℝ≥0∞ :=
      ⨆ α' : Fin k → ℝ≥0, ⨆ _ : α' ∈ {a | ∑ i, a i = 1},
        ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
          ∑ i, (α' i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)
    have hJI : J ≤ I := by
      dsimp [J, I]
      exact le_iSup_of_le α (le_iSup_of_le hαsum le_rfl)
    have hLI : L ≤ T * I := hLJ.trans (mul_le_mul' le_rfl hJI)
    rw [show baiComplexity ν 𝓔 = I⁻¹ by rfl]
    by_cases hI0 : I = 0
    · have hL0 : L = 0 := by
        apply bot_unique
        simpa [hI0, hTtop] using hLI
      simp [hL0]
    by_cases hItop : I = ⊤
    · simp [hItop]
    exact (ENNReal.inv_mul_le_iff hI0 hItop).2 (by simpa [mul_comm] using hLI)
  · have hempty : baiAlternatives 𝓔 ν = ∅ := Set.not_nonempty_iff_eq_empty.mp halt
    haveI : Nonempty (Fin k → ℝ≥0) := ⟨fun _ ↦ 0⟩
    let i0 : Fin k := ⟨0, hk⟩
    let α0 : Fin k → ℝ≥0 := fun i ↦ if i = i0 then 1 else 0
    have hα0 : ∑ i, α0 i = 1 := by simp [α0]
    have hinner :
        (⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
          ∑ i, (α0 i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) = ⊤ := by
      simp [hempty]
    have hsup :
        (⨆ α' : Fin k → ℝ≥0, ⨆ _ : α' ∈ {a | ∑ i, a i = 1},
          ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
            ∑ i, (α' i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) = ⊤ := by
      apply top_unique
      calc
        (⊤ : ℝ≥0∞) =
            (⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
              ∑ i, (α0 i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) := hinner.symm
        _ = (⨆ _ : α0 ∈ {a | ∑ i, a i = 1},
            ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
              ∑ i, (α0 i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) := by
                simpa only [Set.mem_setOf_eq] using
                  (iSup_pos (α := ℝ≥0∞)
                    (f := fun _ : (∑ i, α0 i = 1) ↦
                      ⨅ ν' : StochasticBandit k,
                        ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
                          ∑ i, (α0 i : ℝ≥0∞) *
                            klDiv (ν.P i) (ν'.P i)) hα0).symm
        _ ≤ (⨆ α' : Fin k → ℝ≥0, ⨆ _ : α' ∈ {a | ∑ i, a i = 1},
            ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
              ∑ i, (α' i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) :=
          le_iSup (fun α' : Fin k → ℝ≥0 ↦
            ⨆ _ : α' ∈ {a | ∑ i, a i = 1},
              ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
                ∑ i, (α' i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i)) α0
    rw [show baiComplexity ν 𝓔 =
      (⨆ α' : Fin k → ℝ≥0, ⨆ _ : α' ∈ {a | ∑ i, a i = 1},
        ⨅ ν' : StochasticBandit k, ⨅ _ : ν' ∈ baiAlternatives 𝓔 ν,
          ∑ i, (α' i : ℝ≥0∞) * klDiv (ν.P i) (ν'.P i))⁻¹ by rfl]
    rw [hsup]
    simp
