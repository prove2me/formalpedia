-- Prove2me | solution 1 for BCFGJPSSV26.Stable.ksRun_phase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:19.386578+00:00
-- url     : https://prove2.me/submissions/b64e0eeb-205c-4054-9c3f-1884745c062d

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

namespace KSState

end KSState

namespace KSSteps

end KSSteps

/-- **Termination**: every run is done after `20 s + 20` steps. -/
theorem ksRun_phase (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (ch : ℕ → ℕ) : (ksRun N x LS Λ₁ s b ch).phase = 2 := by
  have h := KSSteps.foldl_pot N x LS Λ₁ s b ((List.range (20 * s + 20)).map ch) ksInit
    ⟨Nat.zero_le _, fun h ↦ absurd rfl h⟩
  rw [List.foldl_map, List.length_map, List.length_range] at h
  unfold ksRun
  rcases h with h | h
  · exact h
  · exfalso
    have : KSSteps.pot s ksInit = 14 * s + 4 := by
      simp [KSSteps.pot, ksInit, KSState.phase, KSState.tag, KSState.j, KSState.dums,
        KSState.del]
      omega
    omega

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.ksRun_phase := @BCFGJPSSV26.Stable.ksRun_phase
