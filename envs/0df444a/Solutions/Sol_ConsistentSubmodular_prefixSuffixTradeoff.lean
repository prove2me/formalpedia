-- Prove2me | solution 1 for ConsistentSubmodular.prefixSuffixTradeoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:43.845854+00:00
-- url     : https://prove2.me/submissions/06327fa1-a7f7-405e-97a1-e1684882d78d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate
import Theorems.Thm_ConsistentSubmodular_WindowInstance_prefix_bound
import Theorems.Thm_ConsistentSubmodular_WindowInstance_halfMixture_suffix
import Theorems.Thm_ConsistentSubmodular_WindowInstance_halfMixture_certificate

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem benchmark_nonneg (j : Fin (W.lastStage + 1)) : 0 ≤ W.benchmark j :=
  W.objective.nonnegative _

/-- The optimum grows no faster than the arrivals alone, the second chain of
(19): `P_j - P_s ≤ λ_j - λ_s` for `s ≤ j`. The candidate `O_j` is feasible at
stage `s`, and diminishing returns compare the arrivals with and without it. -/
theorem benchmark_growth {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) :
    W.benchmark j - W.benchmark s ≤ W.arrivalValue j - W.arrivalValue s := by
  have hopt := W.candidate_optimal s (W.candidate j) (W.candidate_subset j) (W.candidate_card j)
  have hdr := W.objective.diminishing_returns
    (Finset.subset_union_right : W.arrivals s ⊆ W.candidate j ∪ W.arrivals s) (W.arrivals j)
  have h1 : (W.candidate j ∪ W.arrivals s) ∪ W.arrivals j = W.candidate j ∪ W.arrivals j := by
    rw [Finset.union_assoc, Finset.union_eq_right.mpr (W.arrivals_mono hsj)]
  rw [h1, Finset.union_eq_right.mpr (W.arrivals_mono hsj)] at hdr
  unfold benchmark arrivalValue
  linarith

theorem gain_antitone {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) : W.gain j ≤ W.gain s := by
  have h := W.benchmark_growth hsj
  unfold gain
  linarith

theorem pair_union_ge (j a b : Fin (W.lastStage + 1)) :
    W.objective.value (W.arrivals j ∪ W.candidate a) ≤
        W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) ∧
      W.objective.value (W.arrivals j ∪ W.candidate b) ≤
        W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) := by
  constructor <;> apply W.objective.monotone <;> intro e he <;>
    simp only [Finset.mem_union] at he ⊢ <;> tauto

end WindowInstance

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- Inequality (26): the credit never exceeds the benchmark, `K_j ≤ P_j`. -/
theorem credit_le_benchmark (j : Fin (W.lastStage + 1)) : W.credit j ≤ W.benchmark j := by
  have hg := W.gain_antitone (Fin.zero_le j)
  have hA : W.objective.value (W.candidate 0) ≤
      W.objective.value (W.arrivals j ∪ W.candidate 0) :=
    W.objective.monotone _ _ Finset.subset_union_right
  have h0 := W.objective.nonnegative ∅
  have hz : W.gain 0 = W.objective.value (W.candidate 0) - W.objective.value ∅ := by
    simp [gain, benchmark, arrivalValue, W.arrivals_zero]
  unfold credit residual
  unfold gain at *
  linarith

/-- The midpoint bound (24) at stage `j`, with
`(u + z)/2 - min(u, z)/4 = (u + z + max(u, z))/4`: four times
`H_{R_j}(O_0, O_c; 1/2)` is at least `4 L_j`. -/
theorem half_pair_lower (j c : Fin (W.lastStage + 1)) :
    4 * W.arrivalValue j + W.residual 0 j + W.residual c j +
        max (W.residual 0 j) (W.residual c j) ≤ 4 * W.pairValue j 0 c (1 / 2) := by
  obtain ⟨h0, hc⟩ := W.pair_union_ge j 0 c
  unfold residual arrivalValue pairValue twoTypeValue
  rcases le_total (W.objective.value (W.arrivals j ∪ W.candidate 0))
    (W.objective.value (W.arrivals j ∪ W.candidate c)) with h | h
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

end WindowInstance

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem envelopeTerm_le_envelope (β : ℝ) (j : Fin (W.lastStage + 1)) :
    W.envelopeTerm β j ≤ W.envelope β :=
  Finset.le_sup' _ (Finset.mem_univ j)

/-- The envelope is attained at an eligible stage `h`: `K_h ≥ D`, because
`K_h ≤ P_h` (26). Hence the last eligible index `c` of (27) exists. -/
theorem exists_envelope_eligible {β : ℝ} (hβ' : β ≤ 3 / 4) :
    ∃ h, W.envelopeTerm β h = W.envelope β ∧ W.envelope β ≤ W.credit h := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (W.envelopeTerm β)
  refine ⟨h, hh.symm, ?_⟩
  rw [envelope, hh]
  have hK := W.credit_le_benchmark h
  have hP := W.benchmark_nonneg h
  simp only [envelopeTerm]
  nlinarith

/-- The requirement behind the envelope: at every stage `j`,
`4 β P_j ≤ 4 λ_j + 2 r_j + K_c` once `K_c ≥ D`. -/
theorem envelope_requirement {β : ℝ} {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) (j : Fin (W.lastStage + 1)) :
    4 * β * W.benchmark j ≤ 4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c := by
  have hm := W.envelopeTerm_le_envelope β j
  simp only [envelopeTerm, credit, gain] at hm hDc ⊢
  linarith

/-- Persistence on the prefix (Theorem B.4): for `j ≤ c`, Lemma B.5 and the
envelope give `H_{R_j}(O_0, O_c; 1/2) ≥ β P_j`. -/
theorem halfMixture_prefix {β : ℝ} {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) {j : Fin (W.lastStage + 1)} (hjc : j ≤ c) :
    β * W.benchmark j ≤ W.pairValue j 0 c (1 / 2) := by
  have hb := W.prefix_bound hjc
  have := W.envelope_requirement hDc j
  linarith

end WindowInstance

namespace Certificates

/-- Theorem B.4 (prefix–suffix tradeoff). -/
theorem prefixSuffixTradeoff : PrefixSuffixTradeoffGoal := by
  intro β hβ hβ' n W
  have hβ0 : 0 < β := by linarith
  have hhalf : 2 * β * (1 / (2 * β)) = 1 := by field_simp
  obtain ⟨h, -, hhK⟩ := W.exists_envelope_eligible hβ'
  refine ⟨⟨h, hhK⟩, fun c hDc hafter => ⟨fun j hjc => W.halfMixture_prefix hDc hjc,
    fun j hcj => ?_, ?_⟩⟩
  · have hs := W.halfMixture_suffix (α := 1 / (2 * β)) hβ.le hβ' hhalf.le hafter hcj
    have hl := W.half_pair_lower j c
    have heq : W.benchmark j / (2 * β) = 1 / (2 * β) * W.benchmark j := by ring
    change W.benchmark j / (2 * β) ≤ W.pairValue j 0 c (1 / 2)
    linarith
  · have hlevel : 2 * β * min β (1 / (2 * β)) ≤ 1 := by
      calc 2 * β * min β (1 / (2 * β)) ≤ 2 * β * (1 / (2 * β)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
        _ = 1 := hhalf
    obtain ⟨Z, hZ, he, hx⟩ := W.halfMixture_certificate (α := min β (1 / (2 * β))) hβ.le hβ'
      (min_le_left _ _) hlevel hDc hafter
    exact ⟨Z, hZ, he, hx.le⟩

end Certificates

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : PrefixSuffixTradeoffGoal :=
  Certificates.prefixSuffixTradeoff

end
