-- Prove2me | solution 1 for Formalism.L2.G.IntCl.complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:39.140942+00:00
-- url     : https://prove2.me/submissions/c9f5657d-93ad-45c8-b2a9-0faf5411c927

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Theorems.Thm_Formalism_L2_G_IntCl_complete_of_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.IntCl
open IsLocalRing
variable (A K L : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
  [IsScalarTower A K L]
include K
namespace Formalism.L2.G.IntCl
theorem _root_.solution (hC : IsAdicComplete (maximalIdeal A) A) :
    haveI := isDVR A K L hC
    IsAdicComplete (maximalIdeal (integralClosure A L)) (integralClosure A L) := by
  have := isDVR A K L hC
  have := dedekind A K L
  have hcm := complete_map A K L hC
  have h6 : ∀ J : Ideal (integralClosure A L), J ≠ ⊥ →
      ∃ n : ℕ, J = maximalIdeal (integralClosure A L) ^ n :=
    ((IsDiscreteValuationRing.TFAE (integralClosure A L) (not_isField A K L)).out 0 6).mp
      (isDVR A K L hC)
  obtain ⟨n, hn⟩ := h6 _ (map_ne_bot A K L)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [hn, h0, pow_zero, Ideal.one_eq_top] at hcm
    exact absurd hcm.subsingleton (not_subsingleton _)
  · rw [hn] at hcm
    exact complete_of_pow _ hpos hcm
end Formalism.L2.G.IntCl
