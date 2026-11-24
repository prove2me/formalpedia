-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.hwrow_sum_single_castLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:15.289433+00:00
-- url     : https://prove2.me/submissions/587715af-a280-4f4e-98ce-36f083b173e7

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by
  have h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ) :=
    Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))
  rw [h1]
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · exact if_pos (Fin.ext rfl)
    · intro b _ hb
      rw [if_neg]
      intro hab
      subst hab
      exact hb (Fin.ext rfl)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hab
    subst hab
    exact h b.isLt
end Formalism.GradedWeylDivisibility
