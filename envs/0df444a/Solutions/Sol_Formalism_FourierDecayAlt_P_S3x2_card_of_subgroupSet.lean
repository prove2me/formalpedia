-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.card_of_subgroupSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:37.194484+00:00
-- url     : https://prove2.me/submissions/653c264e-9b11-4d17-9c16-c9414bd5f56e

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]
variable {c : ι → ℕ} {x y : Matrix ι ι A}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (P : Matrix ι ι A → Prop) (B : Subgroup (GL ι A))
    (h : ∀ x, P x ↔ ∃ g ∈ B, (g : Matrix ι ι A) = x) : Nat.card {x // P x} = Nat.card B := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun g : B => ⟨((g : GL ι A) : Matrix ι ι A), (h _).2 ⟨g, g.2, rfl⟩⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h1 : ((a : GL ι A) : Matrix ι ι A) = ((b : GL ι A) : Matrix ι ι A) := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext h1)
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := (h x).1 hx
    exact ⟨⟨g, hg⟩, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
