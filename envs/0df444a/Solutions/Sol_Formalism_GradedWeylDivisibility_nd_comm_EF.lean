-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_comm_EF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:00.47543+00:00
-- url     : https://prove2.me/submissions/49dbdf16-5fa1-4cca-a84f-dc6190141f67

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndE R r n l j (ndF R r n l j g) =
      ndF R r n l j (ndE R r n l j g) + (ndEul R r n l g - ndEul R r n j g) := by
  have key : ⁅ndE R r n l j, ndF R r n l j⁆ = ndEul R r n l - ndEul R r n j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at this
  rw [← this]; abel
end Formalism.GradedWeylDivisibility
