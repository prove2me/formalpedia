-- Prove2me | solution 1 for CompoundSMM.Conv.decomposition_e123
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:45:38.789627+00:00
-- url     : https://prove2.me/submissions/81bbd2cd-c4fa-4a6a-87ee-f9342fbc9bf9

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting
open CompoundSMM.Conv

theorem solution {n ℓG ℓF ℓφ : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (Lψ Lφ : ℝ) (hA2 : A2 P Lψ Lφ)
    (ξs ηs : ℕ → Ξ) (x : E n) (N' N : ℕ) (hN' : 0 < N') (hlt : N' < N) :
    Θbar P N N ξs ηs x - Θbar P N' N' ξs ηs x ≤
      (1 - ((N' : ℝ) ^ 2 / (N : ℝ) ^ 2)) * |Θbar P N' N' ξs ηs x - Θ P x| +
      (N' : ℝ) * ((N : ℝ) - N') / (N : ℝ) ^ 2 *
        |P.ψ ((1 / ((N : ℝ) - N')) • ∑ t ∈ Finset.Ico N' N,
            P.φ (P.G x (ξs t)) ((1 / (N' : ℝ)) • ∑ s ∈ Finset.range N', P.F x (ηs s)))
          - Θ P x| +
      (1 - (N' : ℝ) / N) *
        |P.ψ ((1 / (N : ℝ)) • ∑ t ∈ Finset.range N,
            P.φ (P.G x (ξs t)) ((1 / ((N : ℝ) - N')) • ∑ s ∈ Finset.Ico N' N, P.F x (ηs s)))
          - Θ P x| := by
  obtain ⟨-, -, hψI, -, -, -, hψC, hφC⟩ := hA2
  have hle : N' ≤ N := hlt.le
  have hr' : (0 : ℝ) < N' := by exact_mod_cast hN'
  have hd : (0 : ℝ) < (N : ℝ) - N' := by
    have : (N' : ℝ) < N := by exact_mod_cast hlt
    linarith
  have hr : (0 : ℝ) < N := by linarith
  -- inner averages
  set Fp : E ℓF := (1 / (N' : ℝ)) • ∑ s ∈ Finset.range N', P.F x (ηs s) with hFp
  set Ft : E ℓF := (1 / ((N : ℝ) - N')) • ∑ s ∈ Finset.Ico N' N, P.F x (ηs s) with hFt
  have hFb : (1 / (N : ℝ)) • ∑ s ∈ Finset.range N, P.F x (ηs s)
      = ((N' : ℝ) / N) • Fp + (((N : ℝ) - N') / N) • Ft := by
    rw [hFp, hFt, ← Finset.sum_range_add_sum_Ico _ hle, smul_add, smul_smul, smul_smul]
    congr 2
    · field_simp
    · field_simp
  set u' : E ℓφ := (1 / (N' : ℝ)) • ∑ t ∈ Finset.range N', P.φ (P.G x (ξs t)) Fp with hu'
  set v : E ℓφ := (1 / ((N : ℝ) - N')) • ∑ t ∈ Finset.Ico N' N, P.φ (P.G x (ξs t)) Fp with hv
  set w : E ℓφ := (1 / (N : ℝ)) • ∑ t ∈ Finset.range N, P.φ (P.G x (ξs t)) Ft with hw
  set α : ℝ := (N' : ℝ) ^ 2 / (N : ℝ) ^ 2 with hα
  set β : ℝ := (N' : ℝ) * ((N : ℝ) - N') / (N : ℝ) ^ 2 with hβ
  set γ : ℝ := 1 - (N' : ℝ) / N with hγ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hγ0 : 0 ≤ γ := by
    rw [hγ, sub_nonneg, div_le_one hr]; linarith
  have hsum : α + β + γ = 1 := by
    rw [hα, hβ, hγ]; field_simp; ring
  -- convexity of φ_j in the second argument along the split
  have hconv : ∀ t, ∀ j, P.φ (P.G x (ξs t)) ((1 / (N : ℝ)) • ∑ s ∈ Finset.range N, P.F x (ηs s)) j
      ≤ ((N' : ℝ) / N) * P.φ (P.G x (ξs t)) Fp j + (((N : ℝ) - N') / N) * P.φ (P.G x (ξs t)) Ft j := by
    intro t j
    have ha : (0 : ℝ) ≤ (N' : ℝ) / N := by positivity
    have hb : (0 : ℝ) ≤ ((N : ℝ) - N') / N := by positivity
    have hab : (N' : ℝ) / N + ((N : ℝ) - N') / N = 1 := by field_simp; ring
    have := (hφC j).2 (Set.mem_univ (P.G x (ξs t), Fp)) (Set.mem_univ (P.G x (ξs t), Ft)) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
    rw [← add_smul, hab, one_smul, ← hFb] at this
    exact this
  have hcomp : ∀ j, ((1 / (N : ℝ)) • ∑ t ∈ Finset.range N,
      P.φ (P.G x (ξs t)) ((1 / (N : ℝ)) • ∑ s ∈ Finset.range N, P.F x (ηs s))) j
      ≤ (α • u' + β • v + γ • w) j := by
    intro j
    simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul,
      hu', hv, hw]
    calc 1 / (N : ℝ) * ∑ t ∈ Finset.range N,
          P.φ (P.G x (ξs t)) ((1 / (N : ℝ)) • ∑ s ∈ Finset.range N, P.F x (ηs s)) j
        ≤ 1 / (N : ℝ) * ∑ t ∈ Finset.range N, (((N' : ℝ) / N) * P.φ (P.G x (ξs t)) Fp j
            + (((N : ℝ) - N') / N) * P.φ (P.G x (ξs t)) Ft j) := by
          gcongr with t ht
          exact hconv t j
      _ = (N' : ℝ) / N * (1 / N) * (∑ t ∈ Finset.range N', P.φ (P.G x (ξs t)) Fp j
            + ∑ t ∈ Finset.Ico N' N, P.φ (P.G x (ξs t)) Fp j)
          + ((N : ℝ) - N') / N * (1 / N * ∑ t ∈ Finset.range N, P.φ (P.G x (ξs t)) Ft j) := by
          rw [Finset.sum_range_add_sum_Ico _ hle, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
          ring
      _ = _ := by
          rw [hα, hβ, hγ]
          field_simp
  have hψ3 : P.ψ (α • u' + β • v + γ • w) ≤ α * P.ψ u' + β * P.ψ v + γ * P.ψ w := by
    -- use the general Jensen for three points
    have := hψC.map_sum_le (t := Finset.univ) (w := ![α, β, γ]) (p := ![u', v, w])
      (by intro i _; fin_cases i <;> simp [hα0, hβ0, hγ0])
      (by simp [Fin.sum_univ_three, hsum])
      (by intro i _; exact Set.mem_univ _)
    simpa [Fin.sum_univ_three, add_assoc] using this
  have hmain : Θbar P N N ξs ηs x ≤ α * P.ψ u' + β * P.ψ v + γ * P.ψ w := by
    refine le_trans ?_ hψ3
    unfold Θbar
    exact hψI _ _ hcomp
  have hΘ' : Θbar P N' N' ξs ηs x = P.ψ u' := rfl
  rw [hΘ']
  set T := Θ P x
  have e1 : -(P.ψ u' - T) ≤ |P.ψ u' - T| := neg_le_abs _
  have e2 : P.ψ v - T ≤ |P.ψ v - T| := le_abs_self _
  have e3 : P.ψ w - T ≤ |P.ψ w - T| := le_abs_self _
  have f1 := mul_le_mul_of_nonneg_left e1 (by linarith : (0:ℝ) ≤ 1 - α)
  have f2 := mul_le_mul_of_nonneg_left e2 hβ0
  have f3 := mul_le_mul_of_nonneg_left e3 hγ0
  have : α * P.ψ u' + β * P.ψ v + γ * P.ψ w - P.ψ u'
      = (1 - α) * (-(P.ψ u' - T)) + β * (P.ψ v - T) + γ * (P.ψ w - T) := by
    have : γ = 1 - α - β := by linarith
    rw [this]; ring
  linarith
