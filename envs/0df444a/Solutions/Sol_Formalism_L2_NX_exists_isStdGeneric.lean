-- Prove2me | solution 1 for Formalism.L2.NX.exists_isStdGeneric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:53.214798+00:00
-- url     : https://prove2.me/submissions/e5242e53-35bb-4c9b-943f-fb82f9466e0e

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
import Theorems.Thm_Formalism_L2_NX_charOf_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
namespace Formalism.L2.NX
theorem _root_.solution {K : Type} [Field K] (hp : ∀ x, (p x).Prime)
    (hζ : ∀ x, ∃ ζ : K, IsPrimitiveRoot ζ (p x)) : ∃ ψ : Uup p r →* Kˣ, IsStdGeneric p r ψ := by
  choose ζ hζ using hζ
  have hne : ∀ x, ζ x ≠ 0 := fun x => (hζ x).ne_zero (hp x).ne_zero
  let u : ∀ x, Kˣ := fun x => Units.mk0 (ζ x) (hne x)
  have hu : ∀ x, u x ^ (p x) = 1 := fun x => Units.ext (by simp [u, (hζ x).pow_eq_one])
  refine ⟨psiStd p r (fun x => charOf (u x) (hu x)), fun x => charOf (u x) (hu x), fun _ x h1 => ?_, fun _ => rfl⟩
  have h2 := congrArg (fun f => f (Multiplicative.ofAdd (1 : ZMod (p x)))) h1
  simp only [charOf_one, MonoidHom.one_apply] at h2
  exact (hζ x).ne_one (hp x).one_lt (by simpa [u] using congrArg Units.val h2)
end Formalism.L2.NX
