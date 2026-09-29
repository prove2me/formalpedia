-- Prove2me | solution 1 for CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d135dc41-019c-50fd-b0fb-dea3b6398959

import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_CohCarrier_Inst
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.GroupTheory.Index
import Theorems.Thm_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
import Theorems.Thm_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem

set_option autoImplicit false

open CohCarrier IharaLemma IsLocalRing

namespace DiamondInv

noncomputable def localSplitting (R : Type) [CommRing R] [IsLocalRing R] : IdempotentSplitting R where
  n := 1
  e := fun _ => 1
  𝔪 := fun _ => maximalIdeal R
  coi := CompleteOrthogonalIdempotents.unique_iff.mpr rfl
  isMaximal := fun _ => maximalIdeal.isMaximal R
  exists_eq := fun _ hI => ⟨⟨0, Nat.one_pos⟩, (IsLocalRing.eq_maximalIdeal hI).symm⟩
  mem_iff := fun i j =>
    ⟨fun h => ((maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)).elim,
     fun h => (h (Subsingleton.elim i j)).elim⟩

end DiamondInv

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ)
    (hunit : IsUnit ((H.index : ℕ) : 𝒪))
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L H 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)), x • m = 0) → x = 0)
    (d : (ZMod L)ˣ) (t : 𝕋) (ht : ∀ v : H1 L H 𝒪, t • v = diamondL L H 𝒪 d v) (h1 : t - 1 ∈ Sp.𝔪 i)
    (v : H1 L H 𝒪) (hv : v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)) :
    diamondL L H 𝒪 d v = v := by
  classical
  obtain ⟨hmul, hone, -⟩ := CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem L H 𝒪
  obtain ⟨-, -, hmem⟩ := CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem L H 𝒪
  set n := H.index with hn

  have hdpow : ∀ k : ℕ, diamondL L H 𝒪 (d ^ k) = diamondL L H 𝒪 d ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hdn : diamondL L H 𝒪 d ^ n = 1 := by rw [← hdpow, hmem _ (Subgroup.pow_index_mem H d)]

  have htpow : ∀ (k : ℕ) (v : H1 L H 𝒪), (t ^ k) • v = (diamondL L H 𝒪 d ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
    | succ k ih => intro v; rw [pow_succ, mul_smul, ht, ih, pow_succ, Module.End.mul_apply]

  let R := Sp.CornerRing i
  let tc : R := Sp.toCornerRing i t
  have hcs : ∀ (y : 𝕋) (m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))),
      ((Sp.toCornerRing i y • m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))) : H1 L H 𝒪) = y • (m : H1 L H 𝒪) := by
    intro y m
    rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, Sp.e_smul_coe i m]
    exact Sp.e_smul_coe i ⟨_, Submodule.smul_mem _ _ m.2⟩

  have htcn : tc ^ n = 1 := by
    rw [← sub_eq_zero]
    apply hfaith
    intro m
    rw [show (tc ^ n - 1) • m = tc ^ n • m - (1 : R) • m from sub_smul _ _ m, one_smul, sub_eq_zero]
    apply Subtype.ext
    rw [show tc ^ n = Sp.toCornerRing i (t ^ n) from (map_pow _ _ _).symm, hcs, htpow, hdn, Module.End.one_apply]

  have htc1 : tc - 1 ∈ maximalIdeal R := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff R (Sp.𝔪 i) (t - 1)).mpr h1
    rwa [map_sub, map_one] at this

  have hnR : IsUnit ((n : ℕ) : R) := by simpa using hunit.map (algebraMap 𝒪 R)

  have key := IharaLemma.smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one (DiamondInv.localSplitting R) ⟨0, Nat.one_pos⟩
    tc n hnR htcn htc1 (⟨v, hv⟩ : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)))
      ⟨⟨v, hv⟩, by change (1 : R) • (⟨v, hv⟩ : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))) = _; exact one_smul _ _⟩
  have := congrArg Subtype.val key
  rw [hcs, ht] at this
  exact this

end S_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem
end P2MW
export P2MW.S_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem (solution)
