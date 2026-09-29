-- Prove2me | solution 1 for CerednikDrinfeld.mTorsionNeBot_of_isTwoNewEigenformIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d271793e-36f0-5f5b-89cb-23a71faf02f1

import Definitions.Def_ModularCurve_EigenformIdeal
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_ModularCurve_TwoNewEigenformIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal

set_option Elab.async false

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "IsEigenformIdeal EigenformSupportAt HeckeAlg MTorsionNeBot EigenformSupport IsTwoNewEigenformIdeal"
p2m_open "ModularCurve"

namespace IsTwoNewEigenformIdeal

private theorem _root_.ModularCurve.IsTwoNewEigenformIdeal.isEigenformIdeal {M q q' : ℕ} {𝔪 : Ideal HeckeAlg}
    (h : IsTwoNewEigenformIdeal M q q' 𝔪) : IsEigenformIdeal M 𝔪 := by
  obtain ⟨f, hf, -, -, k, hk, hkfin, 𝒪, h𝒪, φ, h𝔪⟩ := h
  exact ⟨f, hf, k, hk, hkfin, 𝒪, h𝒪, φ, h𝔪⟩

end IsTwoNewEigenformIdeal
p2m_export "ModularCurve" "IsTwoNewEigenformIdeal.isEigenformIdeal"
end ModularCurve

namespace CerednikDrinfeld

p2m_open "ModularCurve P2MW.S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal.ModularCurve"

private theorem eigenformSupport_twoNew_of_eigenformSupportAt {M q q' : ℕ} (p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    (hES : EigenformSupportAt M p J) :
    EigenformSupport p J (IsTwoNewEigenformIdeal M q q') :=
  fun 𝔪 h𝔪 hp => hES 𝔪 h𝔪.isEigenformIdeal hp

private theorem mTorsionNeBot_of_isTwoNewEigenformIdeal {M q q' : ℕ} (p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    (hES : EigenformSupportAt M p J) {𝔪 : Ideal HeckeAlg}
    (h𝔪 : IsTwoNewEigenformIdeal M q q' 𝔪) (hp : (p : HeckeAlg) ∈ 𝔪) :
    MTorsionNeBot HeckeAlg J 𝔪 :=
  hES 𝔪 h𝔪.isEigenformIdeal hp

end CerednikDrinfeld

set_option pp.deepTerms true in
set_option pp.proofs true in
#check @CerednikDrinfeld.mTorsionNeBot_of_isTwoNewEigenformIdeal

set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal.ModularCurve"
open CerednikDrinfeld

theorem solution {M q q' : ℕ} (p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    (hES : EigenformSupportAt M p J) {𝔪 : Ideal HeckeAlg}
    (h𝔪 : IsTwoNewEigenformIdeal M q q' 𝔪) (hp : (p : HeckeAlg) ∈ 𝔪) :
    MTorsionNeBot HeckeAlg J 𝔪 := by
  exact CerednikDrinfeld.mTorsionNeBot_of_isTwoNewEigenformIdeal p J hES h𝔪 hp

end S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal
end P2MW
export P2MW.S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal (solution)
