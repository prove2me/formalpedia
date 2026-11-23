-- Prove2me | solution 1 for Formalism.L2.Pj.CompFin.finiteType_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:09.454265+00:00
-- url     : https://prove2.me/submissions/0142657b-908a-43ef-a88b-dd4d77724a23

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompFin
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace Formalism.L2.Pj.CompFin
theorem _root_.solution (R : Type) [CommRing R] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_C _ r)⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (by simp))
end Formalism.L2.Pj.CompFin
