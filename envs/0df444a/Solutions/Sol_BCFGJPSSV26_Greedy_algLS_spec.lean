-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.algLS_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:04:24.318198+00:00
-- url     : https://prove2.me/submissions/0a3cb51e-06b5-4fbf-94d8-5b12a236b4fd

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
import all Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt
public import Theorems.Thm_BCFGJPSSV26_Stable_isALO_localSearch

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-- **The guarantee of the large-`ε` algorithm**: at most `k` facilities, of cost at most
`4 opt k`. -/
theorem algLS_spec {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algLS (toRaw I)) ∧ (algLS (toRaw I)).length ≤ I.k ∧
      I.cost (I.centers (algLS (toRaw I))) ≤ 4 * I.opt I.k := by
  have hopt0 := Instance.opt_nonneg' hI I.k
  have hk1 := hI.one_le_k
  have hm1 := hI.one_le_m
  unfold algLS
  split_ifs with h0 h1
  · have hn0 : I.n = 0 := trivialSol_eq_nil_iff.1 h0
    refine ⟨⟨by simp, by simp, fun i hi ↦ ?_⟩, ?_, ?_⟩
    · rw [List.mem_singleton] at hi
      omega
    · simp only [List.length_singleton]
      omega
    · have : I.cost (I.centers [0]) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ absurd j.2 (by omega)
      rw [this]
      positivity
  · have hn : 1 ≤ I.n := by
      by_contra hn
      exact h0 (trivialSol_eq_nil_iff.2 (by omega))
    exact ⟨isCenterList_trivialSol hI hn, h1, (cost_trivialSol_le hI hn).trans (by linarith)⟩
  · have hk : I.k < (trivialSol (toRaw I)).length := by
      change ¬ _ ≤ I.k at h1
      omega
    obtain ⟨-, -, -, hkm⟩ := of_k_lt_length hI hk
    obtain ⟨hnd, hlen, hlt⟩ := Stable.localSearch_spec hkm.le lsN (lsBudget (toRaw I))
    have hne : Stable.localSearch lsN (toRaw I) (lsBudget (toRaw I)) ≠ [] := by
      intro h
      rw [h, List.length_nil] at hlen
      omega
    obtain ⟨hB₁, hB₂⟩ := lsBudget_ge hkm
    have hALO := Stable.isALO_localSearch hI hkm.le (by norm_num [lsN]) hB₁ hB₂
    have h4 := Stable.costF_le_four_opt hI hkm.le (le_refl lsN) hALO
    refine ⟨⟨hne, hnd, hlt⟩, hlen.le, ?_⟩
    rw [← Instance.costF_eq_cost (Instance.centers_nonempty hne hlt)]
    exact h4

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.algLS_spec := @BCFGJPSSV26.Greedy.algLS_spec
