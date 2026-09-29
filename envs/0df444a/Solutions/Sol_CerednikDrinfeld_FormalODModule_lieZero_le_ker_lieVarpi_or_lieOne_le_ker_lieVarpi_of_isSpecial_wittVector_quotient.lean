-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/20570bff-15bd-5fe6-b558-d48d39dbcbcf

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4) :
    Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi ∨
      Φ.lieOne ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi := by
  classical
  haveI hirr : Irreducible (p : WittVector p k) := WittVector.irreducible p
  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
    CharP.quotient (WittVector p k) p (mt isUnit_iff_exists_inv.mp (fun h => hirr.not_isUnit (isUnit_iff_exists_inv.mpr h)))
  let X₀ : SpecialFormalODModule p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := { toFormalODModule := Φ, isSpecial := hΦ, hasHeight := hΦ4 }
  rcases CerednikDrinfeld.SpecialFormalODModule.forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
      ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) X₀ with h | h
  · exact Or.inl fun m hm => LinearMap.mem_ker.mpr (h m hm)
  · exact Or.inr fun m hm => LinearMap.mem_ker.mpr (h m hm)

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient (solution)
