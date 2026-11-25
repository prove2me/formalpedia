-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.isAlgebraic_map_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:38.19107+00:00
-- url     : https://prove2.me/submissions/f8a3d1a5-7728-49a0-9976-69430f26c71e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (hφ : Function.Injective φ) (s : Set A) {a : A}
    (h : IsAlgebraic (Algebra.adjoin R s) a) : IsAlgebraic (Algebra.adjoin R (φ '' s)) (φ a) := by
  have hmem : ∀ y : Algebra.adjoin R s, φ y ∈ Algebra.adjoin R (φ '' s) := by
    intro y
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.2 ⟨y, y.2, rfl⟩
  let f : Algebra.adjoin R s →+* Algebra.adjoin R (φ '' s) :=
    { toFun := fun y => ⟨φ y, hmem y⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Injective f := fun y z hyz => Subtype.ext (hφ (congrArg Subtype.val hyz))
  exact h.ringHom_of_comp_eq (f := f) (g := φ.toRingHom) hf (RingHom.ext fun y => rfl)
end Formalism.L2.Pj.GenSect
