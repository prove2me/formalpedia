-- Prove2me | solution 1 for CoherentBaseChange.TwoTermComplex.natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/85fd1a74-88bd-5ee9-b40d-64adbd0c08e4

import Mathlib
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi

set_option autoImplicit false

universe u v w

open scoped TensorProduct
p2m_open "CoherentBaseChange P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.CoherentBaseChange"

namespace CoherentBaseChange
p2m_export "CoherentBaseChange" "TwoTermComplex"
namespace TwoTermComplex
p2m_export "CoherentBaseChange.TwoTermComplex" "chi C0 d C1"
namespace ChiFieldAux
p2m_open "CoherentBaseChange.TwoTermComplex CoherentBaseChange"

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w) [Field K] [Algebra R K]

noncomputable def rk : ℕ := Module.finrank K (LinearMap.range (G.d.baseChange K))

theorem h0_add_rk :
    Module.finrank K (LinearMap.ker (G.d.baseChange K)) + rk G K =
      Module.finrank K (K ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange K)
  unfold rk; omega

theorem rk_add_h1 :
    rk G K + Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) =
      Module.finrank K (K ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (G.d.baseChange K))
  unfold rk; omega

theorem main :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have h0 := h0_add_rk G K
  have h1 := rk_add_h1 G K
  rw [Module.finrank_baseChange] at h0 h1
  show _ = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)
  have h0' : (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) + (rk G K : ℤ) =
      (Module.finrank R G.C0 : ℤ) := by exact_mod_cast h0
  have h1' : (rk G K : ℤ) + (Module.finrank K ((K ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange K)) : ℤ) = (Module.finrank R G.C1 : ℤ) := by exact_mod_cast h1
  omega

end CoherentBaseChange.TwoTermComplex.ChiFieldAux

theorem solution
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  exact CoherentBaseChange.TwoTermComplex.ChiFieldAux.main G K

end S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
end P2MW
export P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi (solution)
