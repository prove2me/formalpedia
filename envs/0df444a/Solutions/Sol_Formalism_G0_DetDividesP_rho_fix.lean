-- Prove2me | solution 1 for Formalism.G0.DetDividesP.rho_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:24.935333+00:00
-- url     : https://prove2.me/submissions/afc36f6e-bd18-4216-a645-5ada934e6355

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_not_mem_vars_of_degreeOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (A : Fin r → ι) (l : Fin r) {p : MvPolynomial ((ι × Fin r) ⊕ ι) K}
    (hp : ∀ i, degreeOf (Sum.inr i) p = 0) : rho K A l p = p := by
  have hsub : (p.vars : Set ((ι × Fin r) ⊕ ι)) ⊆ Set.range Sum.inl := by
    intro x hx
    cases x with
    | inl q => exact ⟨q, rfl⟩
    | inr i => exact absurd hx (not_mem_vars_of_degreeOf (hp i))
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p Sum.inl Sum.inl_injective hsub
  rw [rho, aeval_rename]
  have : ((Sum.elim (fun q => (X (Sum.inl q) : MvPolynomial ((ι × Fin r) ⊕ ι) K))
      (fun i => if i = A l then 1 else 0)) ∘ Sum.inl) = fun q => X (Sum.inl q) := by
    funext q; simp
  rw [this]
  clear hp hsub this
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]
end Formalism.G0.DetDividesP
