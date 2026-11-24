-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rename_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:02.16292+00:00
-- url     : https://prove2.me/submissions/d5e67122-6712-46cb-a5e2-98cd6c2e9938

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas

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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rename (some : Fin r × Fin n → Option (Fin r × Fin n)) (rowAct R g f) =
      rowActO R g (rename some f) := by
  have key : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp (rowAct R g) =
      (rowActO R g).comp (rename some) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp [rowAct, rowActO, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun key f
end Formalism.GradedWeylDivisibility
