-- Prove2me | solution 1 for CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.pt_frobeniusTwist_eq_specMap_frobenius_comp_pt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b814826f-31e4-5bbf-9920-fcd1aa93916f

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_CerednikDrinfeld_QMModuliWitnessD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM IsDedekindDomain
open scoped Quaternion TensorProduct NumberField

theorem solution
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' D : ℕ}
    (w : M.ModuliWitnessD Λ N q q' D)
    (k : Type) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (Ā Āℓ : FakeEllipticCurve Λ N k) (hFV : FakeEllipticCurve.HasFrobeniusVerschiebung ℓ Ā Āℓ) :
    (w.pt k sk Āℓ).1 = Spec.map (CommRingCat.ofHom (frobenius k ℓ)) ≫ (w.pt k sk Ā).1 := by
  classical
  obtain ⟨Dfv⟩ := hFV
  apply w.pt_pullback k k (frobenius k ℓ) sk sk ?_ Ā Āℓ Dfv.isPullback

  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)) ⟶ CommRingCat.of k, Spec.map φ = sk :=
    ⟨Spec.preimage sk, Spec.map_preimage sk⟩
  rw [← hφ, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers ((D : ℕ) : ℤ))
  exact RingHom.ext_int _ _

end S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt
end P2MW
export P2MW.S_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_pt_frobeniusTwist_eq_specMap_frobenius_comp_pt (solution)
