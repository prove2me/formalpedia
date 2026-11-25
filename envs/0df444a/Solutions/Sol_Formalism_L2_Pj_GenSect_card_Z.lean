-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.card_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:31.043166+00:00
-- url     : https://prove2.me/submissions/5e2a2276-b820-4434-b669-b3e3e05ceeba

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
theorem _root_.solution (j₀ : Fin m) : Fintype.card {p : Fin (D + 1) × Fin m // Zs j₀ p} = D := by
  let e : {p : Fin (D + 1) × Fin m // Zs j₀ p} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun q => ⟨q.1.1, (q.2 : q.1.1 ≠ 0 ∧ q.1.2 = j₀).1⟩
      invFun := fun i => ⟨(i.1, j₀), (⟨i.2, rfl⟩ : i.1 ≠ 0 ∧ j₀ = j₀)⟩
      left_inv := fun q => by
        obtain ⟨⟨a, b⟩, h⟩ := q
        have hb : b = j₀ := (h : a ≠ 0 ∧ b = j₀).2
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simp
end Formalism.L2.Pj.GenSect
