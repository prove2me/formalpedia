-- Prove2me | solution 1 for Formalism.L2.G.IntCl.complete_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:12.912811+00:00
-- url     : https://prove2.me/submissions/79d83e20-b3a7-4803-a361-6ab65fd7a611

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete

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
namespace Formalism.L2.G.IntCl
theorem _root_.solution {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by
  refine { toIsHausdorff := ⟨fun x hx => h.toIsHausdorff.haus x fun k => ?_⟩,
           toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · rw [← pow_mul]
    exact hx (n * k)
  · obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec (f := fun k => f (n * k)) (fun {a b} hab => by
      rw [← pow_mul]
      exact hf (Nat.mul_le_mul_left n hab))
    refine ⟨L, fun k => ?_⟩
    have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    have h1 : f k ≡ f (n * k) [SMOD (J ^ k • ⊤ : Submodule R R)] := hf hk
    have h2 : f (n * k) ≡ L [SMOD (J ^ k • ⊤ : Submodule R R)] := by
      have := hL k
      rw [← pow_mul] at this
      exact SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hk)) this
    exact h1.trans h2
end Formalism.L2.G.IntCl
