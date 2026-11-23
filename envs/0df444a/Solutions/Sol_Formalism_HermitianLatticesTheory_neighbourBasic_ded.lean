-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourBasic_ded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:56.150752+00:00
-- url     : https://prove2.me/submissions/2c63c3df-050a-4f9f-8789-8fe8972a9059

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (P : Ideal R) (hP : P.IsMaximal) (c c' : K)
    (hc : ∀ p ∈ P, algebraMap R K p * c ∈ Set.range (algebraMap R K))
    (hc' : ∀ p ∈ P, algebraMap R K p * c' ∈ Set.range (algebraMap R K))
    (hnc : c' ∉ Set.range (algebraMap R K)) :
    ∃ a b : R, c = algebraMap R K a + algebraMap R K b * c' := by
  by_cases hbot : P = ⊥
  · exfalso
    apply hnc
    have hF : IsField R := Ring.isField_iff_maximal_bot.mpr (hbot ▸ hP)
    exact (IsFractionRing.surjective_iff_isField (R := R) (K := K)).mpr hF c'
  let J : Ideal R :=
    { carrier := {t | ∃ p ∈ P, ∃ q ∈ P, algebraMap R K t = algebraMap R K p +
        algebraMap R K q * c'}
      add_mem' := by
        rintro x y ⟨p, hp, q, hq, hx⟩ ⟨p', hp', q', hq', hy⟩
        refine ⟨p + p', P.add_mem hp hp', q + q', P.add_mem hq hq', ?_⟩
        simp only [map_add, hx, hy]; ring
      zero_mem' := ⟨0, P.zero_mem, 0, P.zero_mem, by simp⟩
      smul_mem' := by
        rintro r x ⟨p, hp, q, hq, hx⟩
        refine ⟨r * p, P.mul_mem_left r hp, r * q, P.mul_mem_left r hq, ?_⟩
        simp only [smul_eq_mul, map_mul, hx]; ring }
  have hPJ : P ≤ J := fun p hp => ⟨p, hp, 0, P.zero_mem, by simp⟩
  by_cases hJ : J = ⊤
  · have h1 : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨p, hp, q, hq, h1⟩ := h1
    obtain ⟨a, ha⟩ := hc p hp
    obtain ⟨b, hb⟩ := hc q hq
    refine ⟨a, b, ?_⟩
    rw [ha, hb]
    calc c = algebraMap R K 1 * c := by simp
      _ = _ := by rw [h1]; ring
  · exfalso
    have hPJ' : P = J := hP.eq_of_le hJ hPJ
    apply hnc
    have hinj := IsFractionRing.injective R K
    let N : Submodule R K := Submodule.map (Algebra.linearMap R K) P
    have hN : N ≠ ⊥ := by
      intro h0
      apply hbot
      rw [eq_bot_iff]
      intro p hp
      have : algebraMap R K p ∈ N := Submodule.mem_map_of_mem hp
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by rw [this, map_zero])
    have hN' : N.FG := (IsNoetherian.noetherian P).map _
    have hint : IsIntegral R c' := by
      refine isIntegral_of_smul_mem_submodule N hN hN' c' ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hn
      obtain ⟨t, ht⟩ := hc' q hq
      have htJ : t ∈ J := ⟨0, P.zero_mem, q, hq, by rw [ht]; simp⟩
      rw [← hPJ'] at htJ
      refine Submodule.mem_map.mpr ⟨t, htJ, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [ht, mul_comm]
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
end Formalism.HermitianLatticesTheory
