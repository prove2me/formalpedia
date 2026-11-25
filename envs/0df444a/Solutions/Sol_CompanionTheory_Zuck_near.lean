-- Prove2me | solution 1 for CompanionTheory.Zuck.near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:39.196927+00:00
-- url     : https://prove2.me/submissions/0469c058-1f7d-4ebd-8db1-7ecb3d5ab84a

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {n : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution {ε : Fin n → Bool} {μ : Fin n → ℝ} {h D : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hD : ∀ a c, a < c → D ≤ μ a - μ c) {ν : Fin n → ℝ} (j : ℕ) (hj : (j : ℝ) < D)
    (hx : ∀ a, ∃ x : ℕ, x ≤ j ∧ ν a = μ a + x) :
    IsHCParam ν ∧ GapAtLeast ε ν (h - j) ∧ ∀ a c, a < c → D - j ≤ ν a - ν c := by
  choose x hxj hx using hx
  have hx0 : ∀ a, (0 : ℝ) ≤ x a := fun a => Nat.cast_nonneg _
  have hx1 : ∀ a, (x a : ℝ) ≤ j := fun a => by exact_mod_cast hxj a
  have h3 : ∀ a c, a < c → D - j ≤ ν a - ν c := fun a c hac => by
    have := hD a c hac
    rw [hx, hx]; linarith [hx0 a, hx1 c]
  refine ⟨⟨fun a c hac => by linarith [h3 a c hac], fun a => ?_⟩, fun a c hac => ?_, h3⟩
  · obtain ⟨m, hm⟩ := hμ.2 a
    exact ⟨m + x a, by rw [hx]; push_cast; linarith⟩
  · have h1 := hg a c hac
    rw [le_abs] at h1 ⊢
    rw [hx, hx]
    rcases h1 with h1 | h1
    · left; linarith [hx0 a, hx1 c]
    · right; linarith [hx0 c, hx1 a]
end CompanionTheory.Zuck
