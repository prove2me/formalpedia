-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.card_prodG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:53.070169+00:00
-- url     : https://prove2.me/submissions/6328740c-017e-49aa-8cbb-02b52260daa0

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {G : Type} [Group G]
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (N H : Subgroup G) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hd : Disjoint N H) : Nat.card (prodG N H hnorm) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun p : N × H => ⟨(p.1 : G) * (p.2 : G), p.1, p.1.2, p.2, p.2.2, rfl⟩) ⟨?_, ?_⟩
  · intro a b hab
    exact Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val hab)
  · rintro ⟨_, n, hn, h, hh, rfl⟩
    exact ⟨(⟨n, hn⟩, ⟨h, hh⟩), rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
