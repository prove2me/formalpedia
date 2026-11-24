-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.stabLevelProG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:56:38.499579+00:00
-- url     : https://prove2.me/submissions/75cdaade-efd9-4bc7-9cba-c9de8c328d15

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_congruenceTorsion
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_sepLemma
import Theorems.Thm_Formalism_BehrendSets_FinalE_trivStab
import Theorems.Thm_Formalism_BehrendSets_trivStab
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfM_bc_pr_incl
import Theorems.Thm_Formalism_UG_Final_AdelicStabFinite
import Theorems.Thm_Formalism_UG_Final_InclInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.HermitianLattices.FiltrationBoundaryCriterion
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution : StabLevelProG := by
  intro F E _ _ _ _ _ k σ J hσ hH hdet hdef U hU w g hg hgw hk hUw y
  classical
  have hfinS := Formalism.UG.Final.AdelicStabFinite F E (Fin k) σ J hσ hH hdet hdef y
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨by simp [Formalism.UG.stabAt], ?_⟩
  intro γ hγ
  have hγ' : y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y ∈
      U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) := hγ
  have hfo : IsOfFinOrder γ := by
    rw [← finite_powers]
    refine Set.Finite.subset (Set.finite_coe_iff.1 hfinS) ?_
    rintro _ ⟨n, rfl⟩
    show y⁻¹ * ((γ ^ n : _) : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y ∈
      (Formalism.UG.levelAf σ J).subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))
    have e1 : y⁻¹ * ((γ ^ n : _) : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y =
        (y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y) ^ n := by
      have := conj_pow (a := y⁻¹) (b := (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F))) (i := n)
      simpa using this.symm
    rw [e1]
    have := Subgroup.pow_mem _ hγ' n
    exact Subgroup.mem_subgroupOf.2 (hU (Subgroup.mem_subgroupOf.1 this))
  obtain ⟨γ₀, hγ₀, hγ₀eq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hinj := Formalism.UG.Final.InclInj F E (Fin k) (w.adicCompletion F) inferInstance
  obtain ⟨n, hn, hγn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
  have h0n : γ₀ ^ n = 1 := by
    apply hinj
    rw [map_one, map_pow, ← PfM.bc_pr_incl, hγ₀eq]
    have := congrArg (fun z => Formalism.UG.bc (Formalism.UG.prV (E := E) w)
      ((z : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
        Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (congrArg Subtype.val hγn)
    simpa using this
  have hfo0 : IsOfFinOrder γ₀ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h0n⟩
  obtain ⟨s, hx⟩ := hUw _ (Subgroup.mem_subgroupOf.1 hγ')
  set yw := Formalism.UG.bc (Formalism.UG.prV (E := E) w)
    (y : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hyw
  have hxw : Formalism.UG.bc (Formalism.UG.prV (E := E) w)
      ((y⁻¹ * (γ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) * y :
        Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
        Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      yw⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ * yw := by
    rw [← PfM.bc_pr_incl, hγ₀eq]
    simp [hyw]
  rw [hxw] at hx
  set X := yw⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ * yw with hX
  have hord : orderOf X = orderOf γ₀ := by
    have h1 := orderOf_injective
      ((MulAut.conj yw⁻¹).toMonoidHom.comp (Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F))))
      ((MulAut.conj yw⁻¹).injective.comp hinj) γ₀
    simpa [MulAut.conj_apply] using h1
  have hXn : X ^ n = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord, orderOf_dvd_iff_pow_eq_one]; exact h0n

  obtain ⟨A, hRA, hsep⟩ := sepLemma (E := E) w g hgw
  choose r hr hr' using hx
  let B : Matrix (Fin k) (Fin k) A := fun i j => (1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩
  have hB : B.map A.subtype = (X : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) ^ (g ^ s) := by
    ext i j
    have := hr' i j
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    show (((1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩ : A) :
      E ⊗[F] w.adicCompletion F) = _
    by_cases hij : i = j
    · subst hij; simp [add_comm]
    · simp [hij]
  have hinjA : Function.Injective (A.subtype.mapMatrix (m := Fin k)) := by
    intro M N hMN
    ext i j
    exact congrFun (congrFun hMN i) j
  have hBn : B ^ n = 1 := by
    apply hinjA
    rw [map_pow, map_one]
    show (B.map A.subtype) ^ n = 1
    rw [hB, ← pow_mul, mul_comm, pow_mul]
    have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F) =>
      (z : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F))) hXn
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [this, one_pow]
  obtain ⟨m, hm⟩ := congruenceTorsion A (Ideal.span {(g : A)}) g k hg (Ideal.mem_span_singleton_self _) hsep B
    (fun i j => by
      have e : (B - 1) i j = (g : A) * ⟨r i j, hRA (hr i j)⟩ := by
        show ((1 : Matrix (Fin k) (Fin k) A) i j + (g : A) * ⟨r i j, hRA (hr i j)⟩) -
          (1 : Matrix (Fin k) (Fin k) A) i j = _
        ring
      rw [e]
      exact Ideal.mul_mem_right _ (Ideal.span {(g : A)}) (Ideal.mem_span_singleton_self (g : A))) n hn hBn
  have hXg : X ^ (g ^ (s + m)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_add, pow_mul, ← hB]
    have := congrArg (A.subtype.mapMatrix (m := Fin k)) hm
    rw [map_pow, map_one] at this
    exact this
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow hg).1 (orderOf_dvd_of_pow_eq_one hXg)
  rw [hord] at ht
  have hbot := Formalism.BehrendSets.FinalE.trivStab E k g hg hk (Subgroup.zpowers γ₀)
    (Set.finite_coe_iff.2 (finite_zpowers.2 hfo0))
    (IsPGroup.of_card (n := t) (by rw [Nat.card_zpowers, ht]))
  have h1 : γ₀ = 1 := Subgroup.zpowers_eq_bot.1 hbot
  apply Subtype.ext
  apply Subtype.ext
  rw [← hγ₀eq, h1]
  simp
end Formalism.HermitianLattices.StabilizerLevels.PfB
