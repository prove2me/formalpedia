-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostEFGTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:52:05.046351+00:00
-- url     : https://prove2.me/submissions/d0837717-dba3-42cc-b1db-390119395980

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent
import Theorems.Thm_Formalism_FrobeniusOrbits_EFG_two_isPrime
import Theorems.Thm_Formalism_FrobeniusOrbits_EFG_card_trivial_first_component
import Theorems.Thm_Formalism_FrobeniusOrbits_EFG_card_Psi
import Theorems.Thm_Formalism_FrobeniusOrbits_EFG_coprime_two_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_ConjReal_conj_main
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_coprime_two_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostConj_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_hostReal_of
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_isPrime
import Theorems.Thm_UpperTheory_Reformulated_B_JumpSetsAlt_hostReal_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open EFG
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hI : HostInertia) (hD : HostDecomp) : HostEFGTwo := by
  intro e q d hh L _ _ ζ a b h
  have hqd := hh.toHypOdd
  obtain ⟨hEgal, hfin, hmulE, hbijE⟩ := hostGalois e q d hqd L ζ a b h
  have := hEgal
  have : IsGaloisGroup Gal(hostE ζ a b/ℚ) ℤ (𝓞 (hostE ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)
  have := Formalism.FrobeniusOrbits.EFG.two_isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(2 : ℤ)}).primesOver (𝓞 (hostE ζ a b))) :=
    inferInstance
  have hcardG : Nat.card Gal(hostE ζ a b/ℚ) = 2 ^ (e + 2) := by
    rw [IsGalois.card_aut_eq_finrank, hfin]

  have hIn : Nat.card (P.inertia Gal(hostE ζ a b/ℚ)) = 2 ^ e := by
    rw [← card_trivial_first_component e]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => ?_))
    rw [AddSubgroup.mem_inertia]
    exact (hI e q d hh L ζ a b h σ).1 P
  have heE : (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostE ζ a b)) = 2 ^ e := by
    rw [← card_inertia_eq_ramificationIdxIn (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P, hIn]

  have hq2 : q ≠ 2 := by have := hh.2.2.1; omega
  have hd2 : d ≠ 2 := by have := hh.2.2.2.1; omega
  have hDec := fun σ => hD e q d hh L ζ a b h
    (ZMod.unitOfCoprime q (coprime_two_pow hh.1 hq2 e))
    (ZMod.unitOfCoprime d (coprime_two_pow hh.2.1 hd2 e))
    (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _) σ
  have hStab : Nat.card (MulAction.stabilizer Gal(hostE ζ a b/ℚ) P) = 2 ^ (e + 1) := by
    rw [← card_Psi e]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => (hDec σ).1 P))
  have hfE : (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostE ζ a b)) = 2 := by
    have := card_stabilizer_eq (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P
    rw [hStab, heE, pow_succ] at this
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
  have hgE : (primesOver (span {(2 : ℤ)}) (𝓞 (hostE ζ a b))).ncard = 2 := by
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)})
      (𝓞 (hostE ζ a b)) Gal(hostE ζ a b/ℚ)
    rw [heE, hfE, hcardG, show 2 ^ (e + 2) = 2 * (2 ^ e * 2) by ring] at this
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this

  have hcomm : IsMulCommutative Gal(hostE ζ a b/ℚ) :=
    ⟨⟨fun σ τ => hbijE.1 (by rw [hmulE, hmulE, mul_comm])⟩⟩
  have hAb : IsAbelianGalois ℚ (hostE ζ a b) := {}
  have hFab : IsAbelianGalois ℚ (hostF ζ a b) :=
    IsAbelianGalois.tower_bot ℚ (hostF ζ a b) (hostE ζ a b)
  have : IsGaloisGroup Gal(hostF ζ a b/ℚ) ℤ (𝓞 (hostF ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostF ζ a b)
  obtain ⟨hFfin, hFmem⟩ :=
    hostReal_of hostGalois hostGalSpec (hostConj_of hostGalois hostGalSpec) e q d hqd L ζ a b h
  have hcardF : Nat.card Gal(hostF ζ a b/ℚ) = 2 ^ (e + 1) := by
    rw [IsGalois.card_aut_eq_finrank, hFfin]
  obtain ⟨-, σc, -, -, hσc, -⟩ := ConjReal.conj_main hostGalois hostGalSpec hqd h
  have hσcP : σc • P ≠ P := by
    intro heq
    have hmem : σc ∈ MulAction.stabilizer Gal(hostE ζ a b/ℚ) P := heq
    rw [(hDec σc).1 P, hσc] at hmem
    exact (hostGroup e).2.2.1 hmem
  have hfixF : ∀ x : 𝓞 (hostF ζ a b),
      σc • (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x) =
        algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x := by
    intro x
    apply RingOfIntegers.coe_injective
    have hx : (((x : hostF ζ a b) : hostE ζ a b)) ∈ hostF ζ a b := (x : hostF ζ a b).2
    exact ((hFmem _).1.1 hx) σc hσc
  let PF := P.under (𝓞 (hostF ζ a b))
  have hσcPl : (σc • P).LiesOver PF := by
    constructor
    ext x
    show x ∈ P.under (𝓞 (hostF ζ a b)) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_eq_iff.mpr (hfixF x).symm]
  have hgF : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard = 1 := by
    have ht := ncard_primesOver_mul_ncard_primesOver (A := ℤ) (p := span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ) (𝓞 (hostE ζ a b))
      Gal(hostE ζ a b/ℚ)
    rw [hgE] at ht
    have hne : (PF.primesOver (𝓞 (hostE ζ a b))).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht; exact absurd ht (by norm_num)
    have h2le : 2 ≤ (PF.primesOver (𝓞 (hostE ζ a b))).ncard := by
      have hsub : ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))) ⊆
          PF.primesOver (𝓞 (hostE ζ a b)) := by
        intro I hI
        rcases hI with rfl | rfl
        · exact ⟨hPp, inferInstance⟩
        · exact ⟨inferInstance, hσcPl⟩
      calc 2 = ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))).ncard :=
            (Set.ncard_pair hσcP.symm).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero hne)
    have hF0 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≠ 0 := by
      intro h0; rw [h0, zero_mul] at ht; exact absurd ht (by norm_num)
    have hF1 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≤ 1 := by
      by_contra hc
      have hc' := not_le.mp hc
      nlinarith
    omega

  have hte := Ideal.ramificationIdx_tower (R := ℤ) PF P
  have htf := Ideal.inertiaDeg_tower (R := ℤ) PF P
  have heF0 := ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)
  have hfF0 := inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)
  have heE0 := ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)
  have hfE0 := inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)
  have hfundF := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)})
    (𝓞 (hostF ζ a b)) Gal(hostF ζ a b/ℚ)
  rw [hgF, hcardF, one_mul, heF0, hfF0] at hfundF
  rw [← heE0, heE] at hte
  rw [← hfE0, hfE] at htf
  have hpos : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ ≠ 0 := by
    rw [hfundF]; positivity
  have hprod : P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b)) = 1 := by
    have : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ * 1 = PF.ramificationIdx ℤ * PF.inertiaDeg ℤ *
        (P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b))) := by
      rw [mul_one]
      calc PF.ramificationIdx ℤ * PF.inertiaDeg ℤ = 2 ^ e * 2 := by rw [hfundF, pow_succ]
        _ = (PF.ramificationIdx ℤ * P.ramificationIdx (𝓞 (hostF ζ a b))) *
            (PF.inertiaDeg ℤ * P.inertiaDeg (𝓞 (hostF ζ a b))) := by rw [← hte, ← htf]
        _ = _ := by ring
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this).symm
  have he1 := Nat.eq_one_of_mul_eq_one_right hprod
  have hf1 := Nat.eq_one_of_mul_eq_one_left hprod
  rw [he1, mul_one] at hte
  rw [hf1, mul_one] at htf
  exact ⟨heE, hfE, hgE, hgF, heF0.trans hte.symm, hfF0.trans htf.symm⟩
end Formalism.FrobeniusOrbits
