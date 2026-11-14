-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.algMain_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:16:21.125105+00:00
-- url     : https://prove2.me/submissions/de50f79c-7738-40f3-825b-a269a687a4b6

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
import all Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Theorems.Thm_BCFGJPSSV26_Greedy_core_spec

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-- **The guarantee of the main algorithm.** -/
theorem algMain_spec {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algMain c (toRaw I)) ∧
      ((algMain c (toRaw I)).length ≤ I.k + bcomp c I.n ∨
        (bcomp c I.n < I.n ∧ 2 ≤ I.n ∧ (algMain c (toRaw I)).length ≤ I.k + 6 * Rof c I.n)) ∧
      I.cost (I.centers (algMain c (toRaw I))) ≤
        (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) * I.opt I.k := by
  have hratio : (1 : ℝ) ≤ (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) := by
    exact_mod_cast ratio_ge_one hc
  have hopt0 := Instance.opt_nonneg' hI I.k
  have hk1 := hI.one_le_k
  have hm1 := hI.one_le_m
  unfold algMain
  split_ifs with h0 h1
  · -- no clients
    have hn0 : I.n = 0 := trivialSol_eq_nil_iff.1 h0
    refine ⟨⟨by simp, by simp, fun i hi ↦ ?_⟩, .inl ?_, ?_⟩
    · rw [List.mem_singleton] at hi
      omega
    · simp only [List.length_singleton]
      omega
    · have : I.cost (I.centers [0]) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ absurd j.2 (by omega)
      rw [this]
      positivity
  · -- the trivial solution
    have hn : 1 ≤ I.n := by
      by_contra hn
      exact h0 (trivialSol_eq_nil_iff.2 (by omega))
    exact ⟨isCenterList_trivialSol hI hn, .inl h1,
      (cost_trivialSol_le hI hn).trans (le_mul_of_one_le_left hopt0 hratio)⟩
  · -- the core on the guesses
    have hk : I.k < (trivialSol (toRaw I)).length := by
      change ¬ _ ≤ I.k + bcomp c I.n at h1
      omega
    obtain ⟨hpos, hn2, hkn, hkm⟩ := of_k_lt_length hI hk
    have hbn : bcomp c I.n < I.n := by
      have := trivialSol_length_le_n (I := I)
      change ¬ _ ≤ I.k + bcomp c I.n at h1
      omega
    obtain ⟨O, hOopt, Λ, hΛmem, hΛpos, hΛopt, hoptΛ⟩ := exists_good_guess hI hkm.le hpos
    have hx := coreOK_scaled hc hI hn2 hkn hkm hΛpos
    obtain ⟨hSne, hSnd, hSlt, hSlen, hScost⟩ := core_spec hc hx
    have hSmem : core c (scaledIn c (toRaw I) Λ) ∈ coreRuns c (toRaw I) :=
      List.mem_map.2 ⟨Λ, hΛmem, rfl⟩
    have hSvalid : Combine.valid I.m (I.k + 6 * Rof c I.n)
        (core c (scaledIn c (toRaw I) Λ)) = true :=
      Combine.valid_iff.2 ⟨hSne, hSnd, hSlt, hSlen⟩
    obtain ⟨hbv, hbcost⟩ := Combine.costQ_best_le (n := I.n) (distTable I) hSmem hSvalid
    obtain ⟨hBne, hBnd, hBlt, hBlen⟩ := Combine.valid_iff.1 hbv
    refine ⟨⟨hBne, hBnd, hBlt⟩, .inr ⟨hbn, hn2, hBlen⟩, ?_⟩
    -- the cost of the output is at most that of the core on the right guess
    have hB : I.cost (I.centers (Combine.best I.n I.m (I.k + 6 * Rof c I.n) (distTable I)
        (coreRuns c (toRaw I)))) ≤ I.cost (I.centers (core c (scaledIn c (toRaw I) Λ))) := by
      rw [← Combine.costQ_eq I hBne hBlt, ← Combine.costQ_eq I hSne hSlt]
      exact_mod_cast hbcost
    refine hB.trans ?_
    -- the core on the right guess
    have hn1 : 1 ≤ I.n := by omega
    have hOne := hOopt.nonempty hI
    have hOk : O.card ≤ I.k := hOopt.card.le
    have hsc := hScost O hOne hOk
    have hsc' := costF_scaled_le hc hI hn1 hΛpos hOne
    rw [hOopt.cost] at hsc'
    have hρ : ρ + 10 * c.δ ≤ 41 / 20 := by
      have := hc.δ_le
      rw [ρ_eq]
      linarith
    have hr1 : (1 : ℚ) ≤ ρ + 10 * c.δ := by
      have := one_le_ρ
      have := hc.δ_pos
      linarith
    have hs : (coreCost (scaledIn c (toRaw I) Λ) (core c (scaledIn c (toRaw I) Λ)) : ℝ) ≤
        ((ρ + 10 * c.δ : ℚ) : ℝ) * (I.opt I.k / (c.εp * Λ / I.n) + I.n) := by
      have h1 : (coreCost (scaledIn c (toRaw I) Λ) (core c (scaledIn c (toRaw I) Λ)) : ℝ) ≤
          ((ρ + 10 * c.δ : ℚ) : ℝ) *
            (costF (scaledSpace c hc I hI (by omega) Λ hΛpos).d O : ℝ) := by
        exact_mod_cast hsc
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have ht : ((tOf c I.n Λ : ℚ) : ℝ) = (c.εp : ℝ) * Λ / I.n := by
        simp [tOf]
      rw [← ht]
      exact hsc'
    obtain ⟨hcap, hfin⟩ := scale_arith (by exact_mod_cast hn1) (by exact_mod_cast hc.εp_pos)
      (by exact_mod_cast hc.εp_le) (by exact_mod_cast hΛpos) hΛopt hoptΛ
      (by exact_mod_cast hr1)
      (by have h := (Rat.cast_le (K := ℝ)).2 hρ
          rwa [show ((41 / 20 : ℚ) : ℝ) = 41 / 20 by norm_num] at h) hs
    have hcap' : coreCost (scaledIn c (toRaw I) Λ) (core c (scaledIn c (toRaw I) Λ)) <
        Mof c I.n := by
      have : ((Mof c I.n : ℚ) : ℝ) = 8 * (I.n : ℝ) ^ 2 / c.εp + 1 := by
        simp [Mof]
      exact_mod_cast (this ▸ hcap)
    have hcl := cost_le_of_coreCost_lt hc hI hn1 hΛpos hSne hSlt hcap'
    have ht : ((tOf c I.n Λ : ℚ) : ℝ) = c.εp * Λ / I.n := by
      simp [tOf]
    rw [ht] at hcl
    have he : (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) = ((ρ + 10 * c.δ : ℚ) : ℝ) * (1 + c.εp) := by
      push_cast
      ring
    rw [he]
    exact hcl.trans hfin

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.algMain_spec := @BCFGJPSSV26.Greedy.algMain_spec
