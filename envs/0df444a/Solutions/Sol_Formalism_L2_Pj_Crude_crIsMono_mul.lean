-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crIsMono_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:38.446564+00:00
-- url     : https://prove2.me/submissions/655de26d-d0c1-4102-9085-34f5b91caa16

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {R : Type} [CommRing R] {p q : MvPolynomial (Letter T r n) R} (hp : crIsMono p)
    (hq : crIsMono q) : crIsMono (p * q) := by
  obtain ⟨E, rfl⟩ := hp
  obtain ⟨F, rfl⟩ := hq
  exact ⟨E + F, by rw [monomial_mul, one_mul]⟩
end Formalism.L2.Pj.Crude
