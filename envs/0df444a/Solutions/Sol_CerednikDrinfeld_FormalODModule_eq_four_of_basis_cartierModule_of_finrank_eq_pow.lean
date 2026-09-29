-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_four_of_basis_cartierModule_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a6de34e7-1558-5e8e-899c-745c4f3b7fd6

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_MvFormalGroup_CartierModule_nonempty_basis_quotient_smul_top_of_finrank_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_four_of_basis_cartierModule_of_finrank_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
    (X : CerednikDrinfeld.FormalODModule p k)
    (b : Module.Basis (Fin 4) (WittVector p k) (MvFormalGroup.CartierModule p X.F))
    (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X.F.nthSeries p))) = p ^ h) :
    h = 4 := by
  classical

  obtain ⟨B⟩ := MvFormalGroup.CartierModule.nonempty_basis_quotient_smul_top_of_finrank_eq_pow p X.F h hdeg

  set I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)} with hI
  haveI : Nontrivial (WittVector p k ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.2 (by
      rw [hI, Ne, Ideal.span_singleton_eq_top]
      exact (WittVector.irreducible p).not_isUnit)
  let e : ((WittVector p k ⧸ I) ⊗[WittVector p k] MvFormalGroup.CartierModule p X.F) ≃ₗ[WittVector p k]
      (MvFormalGroup.CartierModule p X.F ⧸ (I • ⊤ : Submodule (WittVector p k) (MvFormalGroup.CartierModule p X.F))) :=
    TensorProduct.quotTensorEquivQuotSMul (MvFormalGroup.CartierModule p X.F) I
  let e' : ((WittVector p k ⧸ I) ⊗[WittVector p k] MvFormalGroup.CartierModule p X.F) ≃ₗ[WittVector p k ⧸ I]
      (MvFormalGroup.CartierModule p X.F ⧸ (I • ⊤ : Submodule (WittVector p k) (MvFormalGroup.CartierModule p X.F))) :=
    e.toAddEquiv.toLinearEquiv (fun c x => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      show e ((algebraMap (WittVector p k) (WittVector p k ⧸ I) c) • x) =
        (algebraMap (WittVector p k) (WittVector p k ⧸ I) c) • e x
      rw [algebraMap_smul, algebraMap_smul, map_smul])
  let B4 : Module.Basis (Fin 4) (WittVector p k ⧸ I)
      (MvFormalGroup.CartierModule p X.F ⧸ (I • ⊤ : Submodule (WittVector p k) (MvFormalGroup.CartierModule p X.F))) :=
    (b.baseChange (WittVector p k ⧸ I)).map e'

  have := Fintype.card_congr (B.indexEquiv B4)
  simpa using this

end S_CerednikDrinfeld_FormalODModule_eq_four_of_basis_cartierModule_of_finrank_eq_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_four_of_basis_cartierModule_of_finrank_eq_pow (solution)
