-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.algHom_det_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:02.594012+00:00
-- url     : https://prove2.me/submissions/9b7edc90-25d9-4e62-acf0-ff376cad9c9f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor

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
theorem _root_.solution {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) {s : ℕ} (M : Fin s → Fin s → A) :
    φ (Matrix.of M).det = (Matrix.of fun p q => φ (M p q)).det := by
  rw [AlgHom.map_det]
  rfl
end Formalism.GradedWeylDivisibility
