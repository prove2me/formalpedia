-- Prove2me | solution 1 for CuspForm.Bfam0.block
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/55afe0e1-2f61-5929-a6ec-30eb2dd42f21

import Definitions.Def_CuspForm_CornerPairingFamily
import Theorems.Thm_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_Bfam0_block
p2m_attr_erase "instance" "ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.PDPairing.CentralExt.lift_apply ModularCurve.PDPairing.mem_Gamma0Upper ModularCurve.PDPairing.CentralExt.snd_apply ModularCurve.PDPairing.pairZ_apply ModularCurve.PDPairing.conjUpperMat_apply_11 ModularCurve.PDPairing.sect_snd ModularCurve.PDPairing.conjUpperMat_apply_10 HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

set_option linter.unusedVariables false in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    (∀ (M : ℕ) [NeZero M],
      Function.Bijective (CuspForm.Bfam₀ 𝒪 M) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
          (Tx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 x →
          (Ty : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 y →
          CuspForm.Bfam₀ 𝒪 M Tx y = CuspForm.Bfam₀ 𝒪 M x Ty) ∧
      (∀ (d : (ZMod M)ˣ) (x y Dx Dy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
          (Dx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d x →
          (Dy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d y →
          CuspForm.Bfam₀ 𝒪 M Dx y = CuspForm.Bfam₀ 𝒪 M x Dy)) ∧
    (∀ (M M' : ℕ) [NeZero M'] (d d' : ℕ) [NeZero d] [NeZero d']
        (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (h' : CohCarrier.LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
        (x : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪))
        (y : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
        (ix : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
        (jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
        (ix : CohCarrier.H1 M' ⊤ 𝒪) = CohCarrier.iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x →
        (jy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y →
        CuspForm.Bfam₀ 𝒪 M jy x = CuspForm.Bfam₀ 𝒪 M' y ix) :=
  Classical.epsilon_spec (p := CuspForm.Bfam₀.Block 𝒪)
    (CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms p hp hp2 hpu)

end S_CuspForm_Bfam0_block
end P2MW
export P2MW.S_CuspForm_Bfam0_block (solution)
