-- Prove2me | solution 1 for Formalism.NG.points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:46.054472+00:00
-- url     : https://prove2.me/submissions/7d06d3fa-c1bf-4d86-a9a0-0121aaa0008e

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CongMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatPoints := by
  intro O B Ω _ _ _ _ _ _ _ _ _ _ hinj b hb
  by_contra hb0
  have hnil : b ∉ sInf (minimalPrimes B) := by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes]
    intro h
    have h' : b ∈ nilradical B := h
    rw [nilradical_eq_zero] at h'
    exact hb0 h'
  obtain ⟨P, hP, hbP⟩ : ∃ P ∈ minimalPrimes B, b ∉ P := by
    rw [Ideal.mem_sInf] at hnil
    push Not at hnil
    exact hnil
  have hPprime : P.IsPrime := hP.1.1
  have hcomap : P.comap (algebraMap O B) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    by_contra ha0
    have hnzd : algebraMap O B a ∈ nonZeroDivisors B := by
      rw [mem_nonZeroDivisors_iff_right]
      intro x hx
      have hs : a • x = 0 := by rw [Algebra.smul_def, mul_comm, hx]
      exact (smul_eq_zero.mp hs).resolve_left ha0
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha hnzd
  have : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  have hinjS : Function.Injective (algebraMap O (B ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : algebraMap O B a ∈ P := by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at ha
      exact ha
    have : a ∈ P.comap (algebraMap O B) := ha'
    rw [hcomap] at this
    exact (Ideal.mem_bot).mp this
  have : Module.IsTorsionFree O (B ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjS
  have : Module.IsTorsionFree O Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  let L : (B ⧸ P) →ₐ[O] Ω := IsAlgClosed.lift
  have hker : RingHom.ker (L : (B ⧸ P) →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap O Ω a = 0 := by
      rw [← L.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hinj (by rw [this, map_zero])
  have hφ := hb (L.comp (Ideal.Quotient.mkₐ O P))
  have hmem : Ideal.Quotient.mk P b ∈ RingHom.ker (L : (B ⧸ P) →+* Ω) := by
    rw [RingHom.mem_ker]
    exact hφ
  rw [hker, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hbP hmem
end Formalism.NG
