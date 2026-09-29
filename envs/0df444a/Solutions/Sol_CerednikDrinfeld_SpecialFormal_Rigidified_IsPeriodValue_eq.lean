-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/114e2545-30bb-5c14-a21b-f4cdf5598116

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (d d' : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hd : t.IsPeriodValue ι hcΦ rΦ ψ d) (hd' : t.IsPeriodValue ι hcΦ rΦ ψ d') : d = d' := by
  obtain ⟨Q, hQ, hQd⟩ := hd
  obtain ⟨Q', hQ', hQ'd'⟩ := hd'
  have hiso : Q.IsIsomorphic Q' :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ hB t ht Q Q' hQ hQ'
  have hQ'd : Q'.IsQuadrupleOf d :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic hQd hiso
  have hπ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  exact (CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique hπ hQ'd' hQ'd)

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_eq (solution)
