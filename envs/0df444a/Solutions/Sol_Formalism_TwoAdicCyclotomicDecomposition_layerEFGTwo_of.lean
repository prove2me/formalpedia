-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerEFGTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:27.452313+00:00
-- url     : https://prove2.me/submissions/ebce354e-6d1e-423a-b993-746fd2401be1

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_stab_fix
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_sgn_eq_one_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_isPrime
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_efg_L
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (hG : LayerGalois) (hR : LayerReal) : LayerEFGTwo := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  obtain ⟨-, hmemK, hdegK⟩ := hR n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (primesOver (span {(2 : ℤ)}) (𝓞 L)) := inferInstance
  obtain ⟨he, hf, hg⟩ := efg_L hG hn hqd h P
  have hq8 := hqd.2.2.2
  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hb : b ^ 2 = ((4 * (2 * c') + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  refine ⟨by rw [ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ), he],
    by rw [inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(L/ℚ), hf], hg, ?_⟩

  set K := maximalRealSubfield L with hKdef
  obtain ⟨τ, hτ⟩ := hbij.2 (JJ n)
  have hτK : ∀ x : L, x ∈ K → τ x = x := fun x hx => (hmemK x).mp hx τ hτ
  have hτb : τ b ≠ b := by
    intro hfix
    have : (galMap h.1 a b τ).2.2 = -1 := by rw [hτ]; rfl
    change sgn τ b = -1 at this
    rw [(sgn_eq_one_iff τ b).mpr hfix] at this
    exact absurd this (by decide)
  have hτP : τ • P ≠ P := fun heq =>
    hτb (stab_fix b c' hb P τ (MulAction.mem_stabilizer_iff.mpr heq))
  have hset : primesOver (span {(2 : ℤ)}) (𝓞 L) = {P, τ • P} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro Q hQ
      rcases hQ with rfl | hQ
      · exact ⟨inferInstance, inferInstance⟩
      · rw [Set.mem_singleton_iff] at hQ
        subst hQ
        exact ⟨inferInstance, inferInstance⟩
    · rw [hg, Set.ncard_pair hτP.symm]
    · exact Set.finite_of_ncard_ne_zero (by rw [hg]; norm_num)
  set S := 𝓞 K
  set Pp : Ideal S := P.under S with hPp_def
  have hunder : (τ • P).under S = Pp := by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      hPp_def, Ideal.under_def, Ideal.mem_comap]
    have hfx : τ⁻¹ • (algebraMap S (𝓞 L) x) = algebraMap S (𝓞 L) x := by
      apply RingOfIntegers.coe_injective
      show τ⁻¹ ((algebraMap S (𝓞 L) x : 𝓞 L) : L) = ((algebraMap S (𝓞 L) x : 𝓞 L) : L)
      have hmem : ((algebraMap S (𝓞 L) x : 𝓞 L) : L) ∈ K := by
        show ((x : K) : L) ∈ K
        exact (x : K).2
      have h1 := hτK _ hmem
      calc τ⁻¹ ((algebraMap S (𝓞 L) x : 𝓞 L) : L)
          = τ⁻¹ (τ ((algebraMap S (𝓞 L) x : 𝓞 L) : L)) := by rw [h1]
        _ = _ := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [hfx]
  have hsetK : primesOver (span {(2 : ℤ)}) S = {Pp} := by
    ext Q
    constructor
    · rintro ⟨hQp, hQl⟩
      obtain ⟨⟨R, hRp, hRl⟩⟩ : Nonempty (Q.primesOver (𝓞 L)) := inferInstance
      have : R.LiesOver (span {(2 : ℤ)}) := Ideal.LiesOver.trans R Q (span {(2 : ℤ)})
      have hR2 : R ∈ primesOver (span {(2 : ℤ)}) (𝓞 L) := ⟨hRp, this⟩
      rw [hset] at hR2
      rw [Set.mem_singleton_iff, Ideal.over_def R Q]
      rcases hR2 with rfl | hR2
      · rfl
      · rw [Set.mem_singleton_iff] at hR2
        rw [hR2, hunder]
    · rintro hQ
      rw [Set.mem_singleton_iff] at hQ
      subst hQ
      exact ⟨inferInstance, inferInstance⟩

  have : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun x y => hbij.1 (by rw [hmul, hmul, mul_comm])⟩⟩
  have : IsAbelianGalois ℚ L := { }
  have : IsGalois ℚ K := (IsAbelianGalois.tower_bot ℚ K L).toIsGalois
  have : IsGaloisGroup Gal(K/ℚ) ℤ S := IsGaloisGroup.of_isFractionRing _ _ _ ℚ K
  have hfundK := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(2 : ℤ)}) S Gal(K/ℚ)
  rw [IsGalois.card_aut_eq_finrank, hdegK, hsetK, Set.ncard_singleton, one_mul,
    ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) Pp Gal(K/ℚ),
    inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) Pp Gal(K/ℚ)] at hfundK
  rw [hsetK, Set.ncard_singleton,
    ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) Pp Gal(K/ℚ),
    inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) Pp Gal(K/ℚ)]
  have hte := Ideal.ramificationIdx_tower (R := ℤ) Pp P
  have htf := Ideal.inertiaDeg_tower (R := ℤ) Pp P
  have hte' := P.ramificationIdx_pos S
  have htf' := P.inertiaDeg_pos S
  rw [he] at hte
  rw [hf] at htf
  set e := Pp.ramificationIdx ℤ
  set f := Pp.inertiaDeg ℤ
  have he1 : e ≤ 2 ^ (n - 1) := by rw [hte]; exact Nat.le_mul_of_pos_right _ hte'
  have hf1 : f ≤ 2 := by rw [htf]; exact Nat.le_mul_of_pos_right _ htf'
  have hN : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [hN] at hfundK
  have hpk : 0 < 2 ^ (n - 1) := by positivity
  have he2 : e = 2 ^ (n - 1) := by
    apply le_antisymm he1
    by_contra hlt
    push Not at hlt
    have : e * f < 2 ^ (n - 1) * 2 := by
      calc e * f ≤ e * 2 := Nat.mul_le_mul_left _ hf1
        _ < 2 ^ (n - 1) * 2 := by omega
    omega
  refine ⟨rfl, he2, ?_⟩
  rw [he2] at hfundK
  exact Nat.eq_of_mul_eq_mul_left hpk hfundK
end Formalism.TwoAdicCyclotomicDecomposition
