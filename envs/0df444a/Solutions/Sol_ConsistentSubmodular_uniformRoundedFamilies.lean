-- Prove2me | solution 1 for ConsistentSubmodular.uniformRoundedFamilies
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:50.816368+00:00
-- url     : https://prove2.me/submissions/ec030d79-bbe4-4785-acf2-da326e81559d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformRoundedFamilies
import Theorems.Thm_ConsistentSubmodular_Objective_exists_rounded_bridge
import Theorems.Thm_ConsistentSubmodular_ProtectedClock_window_bridge_endpoints
import Theorems.Thm_ConsistentSubmodular_ProtectedClock_rounded_families
import Theorems.Thm_ConsistentSubmodular_FractionalWindow_rounded_of_zero_scale
import Theorems.Thm_ConsistentSubmodular_WindowSamples_toRounded
import Theorems.Thm_ConsistentSubmodular_FractionalWindow_exists_windowSamples

section

noncomputable section

namespace ConsistentSubmodular

namespace FractionalWindow

variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

/-- Every bounded-complexity fractional window has an endpoint-preserving
physical realization, including zero scale and zero-piece paths. -/
theorem exists_rounded (hN : 200 ≤ N) (hS : 0 < S) (hκ : windowHeavyBound N S ≤ κ) :
    Nonempty (RoundedWindow W (windowHeavyBound N S) (windowLengthBound S)) := by
  by_cases hV : f.bufferedOptimum old ∅ κ = 0
  · exact W.rounded_of_zero_scale hV _ _ (by unfold windowLengthBound; omega)
  · have hVpos : 0 < f.bufferedOptimum old ∅ κ :=
      lt_of_le_of_ne (f.bufferedOptimum_nonnegative _ _ _) (Ne.symm hV)
    obtain ⟨Smp⟩ := W.exists_windowSamples hN hS hκ hVpos
    exact Smp.toRounded hκ

end FractionalWindow

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution (O : CertificateFamily) (N : ℕ) (hN : 200 ≤ N) :
    HasUniformRoundedFamilies O.level N (familyHeavy N (O.budget (3 * N + 1)))
      (familyLength (O.budget (3 * N + 1))) := by
  intro n k f p
  let H := familyHeavy N (O.budget (3 * N + 1))
  let L := familyLength (O.budget (3 * N + 1))
  let C := transferClock f p
  have hN0 : 0 < N := by omega
  have hS : 0 < O.budget (3 * N + 1) := O.budget_pos _
  have hHW : windowHeavyBound N (O.budget (3 * N + 1)) ≤ p.core := by
    have hh := p.core_large
    dsimp only [familyHeavy] at hh
    omega
  let R := fun i => Classical.choice ((C.fractionalWindows f p.core O N hN0 i).exists_rounded hN hS hHW)
  apply C.rounded_families f p.core O N hN (windowHeavyBound N (O.budget (3 * N + 1)))
    (windowLengthBound (O.budget (3 * N + 1))) (bridgeHeavy N) 10 (p.core + p.block + H) L R
  · have hs := p.rounding_slack
    have hh : (windowHeavyBound N (O.budget (3 * N + 1)) : ℝ) ≤ H := by
      exact_mod_cast (show windowHeavyBound N (O.budget (3 * N + 1)) ≤ H by dsimp [H, familyHeavy]; omega)
    push_cast
    linarith
  · have hs := p.rounding_slack
    have hh : (bridgeHeavy N : ℝ) ≤ H := by
      exact_mod_cast (show bridgeHeavy N ≤ H by dsimp [H, familyHeavy]; omega)
    push_cast
    linarith
  · dsimp [L, familyLength]
    omega
  · dsimp [L, familyLength]
    omega
  · intro i
    have hterminal := C.windowTerminal_spec f p.core i
    have hinitial := C.windowInitial_spec f p.core (i + 1)
    obtain ⟨hA, hB, hAv, hBv⟩ := C.window_bridge_endpoints f p.core i
    obtain ⟨P, h0, h1, hlen, hnode⟩ := f.exists_rounded_bridge (C.windowTerminal f p.core i)
      (C.windowInitial f p.core (i + 1)) (C.windowBuffer n i (C.windowDuration i)) N p.core
      (f.prefixOptimum p.core (C.start (i + 1))) hN0 (f.prefixOptimum_nonnegative _ _)
      hterminal.2.1 hinitial.2.1 hAv hBv hA hB
    refine ⟨P, h0, h1, hlen, fun j => ⟨(hnode j).1, (hnode j).2.1, ?_⟩⟩
    have hV := f.prefixOptimum_nonnegative p.core (C.start (i + 1))
    exact (mul_le_mul_of_nonneg_right (by linarith [O.level_le]) hV).trans (hnode j).2.2

end
