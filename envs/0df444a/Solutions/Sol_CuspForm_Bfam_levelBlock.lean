-- Prove2me | solution 1 for CuspForm.Bfam.levelBlock
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fd3891eb-f8ce-5a3a-aa3b-b1c36cb22078

import Definitions.Def_CuspForm_CornerPairingFamily
import Theorems.Thm_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_Bfam_levelBlock
p2m_attr_erase "instance" "ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.PDPairing.CentralExt.lift_apply ModularCurve.PDPairing.mem_Gamma0Upper ModularCurve.PDPairing.CentralExt.snd_apply ModularCurve.PDPairing.pairZ_apply ModularCurve.PDPairing.conjUpperMat_apply_11 ModularCurve.PDPairing.sect_snd ModularCurve.PDPairing.conjUpperMat_apply_10 HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

open CohCarrier

set_option linter.unusedVariables false in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    ∀ (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1),
      IsUnit ((H.index : ℕ) : 𝒪) →
      Function.Bijective (CuspForm.Bfam 𝒪 M H h₁) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], (ℓ.Prime ∨ ℓ ∣ M) →
        ∀ (x y Tx Ty : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
            (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
          (Tx : H1 M H 𝒪) = heckeT M H ℓ 𝒪 x → (Ty : H1 M H 𝒪) = heckeT M H ℓ 𝒪 y →
          CuspForm.Bfam 𝒪 M H h₁ Tx y = CuspForm.Bfam 𝒪 M H h₁ x Ty) ∧
      (∀ (d : (ZMod M)ˣ) (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
            (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
          diamondL M H 𝒪 d (x : H1 M H 𝒪) = x) :=
  (Classical.epsilon_spec
    (p := fun B => CuspForm.Bfam.LevelBlock 𝒪 B ∧ CuspForm.Bfam.DegeneracyBlock 𝒪 B)
    (CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms
      p hp hp2 hpu)).1

end S_CuspForm_Bfam_levelBlock
end P2MW
export P2MW.S_CuspForm_Bfam_levelBlock (solution)
