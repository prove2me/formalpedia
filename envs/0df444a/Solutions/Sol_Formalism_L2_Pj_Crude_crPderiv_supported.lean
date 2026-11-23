-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crPderiv_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:03.89857+00:00
-- url     : https://prove2.me/submissions/9b837fd2-b75d-4a37-8186-c1633e8f9c20

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
theorem _root_.solution {R : Type} [CommRing R] {s : Set (Letter T r n)} (i : Letter T r n)
    {p : MvPolynomial (Letter T r n) R} (hp : p ∈ supported R s) : pderiv i p ∈ supported R s := by
  classical
  have hp' : p ∈ Algebra.adjoin R ((X : Letter T r n → MvPolynomial (Letter T r n) R) '' s) := hp
  clear hp
  show pderiv i p ∈ Algebra.adjoin R ((X : Letter T r n → MvPolynomial (Letter T r n) R) '' s)
  induction hp' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, -, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | algebraMap c =>
    rw [Derivation.map_algebraMap]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx' hy) (mul_mem hy' hx)
end Formalism.L2.Pj.Crude
