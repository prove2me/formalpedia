-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/69aebb52-e147-5d6d-92f8-e03427f11e51

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing
import Theorems.Thm_MvFormalGroup_CartierModule_eq_of_map_eq
import Theorems.Thm_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
import Theorems.Thm_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace P2mKcK2bAssembly

section Ideal

variable {R : Type u} [CommRing R] {n : ℕ}

def pivot (e : Fin n →₀ ℕ) (he : e ≠ 0) : Fin n :=
  e.support.min' (Finsupp.support_nonempty_iff.mpr he)

theorem pivot_mem (e : Fin n →₀ ℕ) (he : e ≠ 0) : pivot e he ∈ e.support :=
  Finset.min'_mem _ _

theorem one_le_pivot (e : Fin n →₀ ℕ) (he : e ≠ 0) : 1 ≤ e (pivot e he) :=
  Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (pivot_mem e he))

def part (g : MvPowerSeries (Fin n) R) (j : Fin n) : MvPowerSeries (Fin n) R := fun e' =>
  if h : e' + Finsupp.single j 1 ≠ 0 then
    if pivot (e' + Finsupp.single j 1) h = j then coeff (e' + Finsupp.single j 1) g else 0
  else 0

theorem coeff_part (g : MvPowerSeries (Fin n) R) (j : Fin n) (e' : Fin n →₀ ℕ) :
    coeff e' (part g j) =
      if h : e' + Finsupp.single j 1 ≠ 0 then
        if pivot (e' + Finsupp.single j 1) h = j then coeff (e' + Finsupp.single j 1) g else 0
      else 0 := rfl

theorem coeff_X_mul_part (g : MvPowerSeries (Fin n) R) (j : Fin n) (e : Fin n →₀ ℕ) :
    coeff e (X j * part g j) =
      if h : e ≠ 0 then (if pivot e h = j then coeff e g else 0) else 0 := by
  classical
  rw [X, coeff_monomial_mul, one_mul]
  by_cases hle : Finsupp.single j 1 ≤ e
  · rw [if_pos hle, coeff_part]
    have hsum : e - Finsupp.single j 1 + Finsupp.single j 1 = e := tsub_add_cancel_of_le hle
    have he : e ≠ 0 := by
      intro h0
      rw [h0] at hle
      have := hle j
      simp at this
    simp only [hsum, dif_pos he, ne_eq]
  · rw [if_neg hle]
    by_cases he : e = 0
    · rw [dif_neg (not_not.mpr he)]
    · rw [dif_pos he]
      by_cases hp : pivot e he = j
      · exfalso
        apply hle
        intro i
        rw [Finsupp.single_apply]
        split_ifs with hij
        · subst hij
          rw [← hp]
          exact one_le_pivot e he
        · exact Nat.zero_le _
      · rw [if_neg hp]

theorem eq_sum_X_mul_part (g : MvPowerSeries (Fin n) R) (hg : g.constantCoeff = 0) :
    g = ∑ j, X j * part g j := by
  classical
  ext e
  rw [map_sum]
  simp only [coeff_X_mul_part]
  by_cases he : e = 0
  · subst he
    simp only [ne_eq, not_true_eq_false, dif_neg, not_false_eq_true, Finset.sum_const_zero,
      coeff_zero_eq_constantCoeff_apply, hg]
  · simp only [dif_pos he, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem subst_mem_span_range {τ : Type*} {a : Fin n → MvPowerSeries τ R} (ha : HasSubst a)
    (g : MvPowerSeries (Fin n) R) (hg : g.constantCoeff = 0) :
    subst a g ∈ Ideal.span (Set.range a) := by
  rw [eq_sum_X_mul_part g hg, ← coe_substAlgHom ha, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha, subst_X ha]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

end Ideal

section QuasiInverse

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

def quasiInv (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ) (hc : ∀ g, ∃ f, θ f = c • g) :
    M' →+ M where
  toFun g := Classical.choose (hc g)
  map_zero' := hinj (by rw [Classical.choose_spec (hc 0), smul_zero, map_zero])
  map_add' g g' := hinj (by
    rw [Classical.choose_spec (hc _), map_add, Classical.choose_spec (hc g),
      Classical.choose_spec (hc g'), smul_add])

theorem apply_quasiInv (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ)
    (hc : ∀ g, ∃ f, θ f = c • g) (g : M') : θ (quasiInv θ hinj c hc g) = c • g :=
  Classical.choose_spec (hc g)

theorem quasiInv_apply (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ)
    (hc : ∀ g, ∃ f, θ f = c • g) (f : M) : quasiInv θ hinj c hc (θ f) = c • f :=
  hinj (by rw [apply_quasiInv, map_nsmul])

theorem quasiInv_comm (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ)
    (hc : ∀ g, ∃ f, θ f = c • g) (T : M →+ M) (T' : M' →+ M') (hT : ∀ f, θ (T f) = T' (θ f))
    (g : M') : quasiInv θ hinj c hc (T' g) = T (quasiInv θ hinj c hc g) :=
  hinj (by rw [apply_quasiInv, hT, apply_quasiInv, map_nsmul])

end QuasiInverse

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]

omit [IsAlgClosed k] in

theorem toPowerSeries_eq_of_map_eq {d d' : ℕ} {G : MvFormalGroup d k} {G' : MvFormalGroup d' k}
    [G.IsComm] [G'.IsComm] (φ ψ : G.Hom G')
    (h : ∀ f : MvFormalGroup.CartierModule p G, map φ f = map ψ f) :
    φ.toPowerSeries = ψ.toPowerSeries :=
  congrArg MvFormalGroup.Hom.toPowerSeries (MvFormalGroup.CartierModule.eq_of_map_eq p G G' φ ψ h)

theorem main (jj : Zp2 p →+* k) (Φ Φ' : SpecialFormalODModule p jj) :
    ∃ (ρ : Series k) (h : ℕ),
      IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ h := by
  classical

  obtain ⟨θ, hinj, hF, hV, hH, hAct, hPi, N, hN⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
      p k jj Φ Φ'
  set θ' := quasiInv θ hinj (p ^ N) hN with hθ'

  obtain ⟨ρ, hρ⟩ := MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing p Φ.F Φ'.F θ hF hV hH
  obtain ⟨ρ', hρ'⟩ := MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing p Φ'.F Φ.F θ'
    (fun g => quasiInv_comm θ hinj _ hN frobenius frobenius hF g)
    (fun g => quasiInv_comm θ hinj _ hN verschiebung verschiebung hV g)
    (fun a g => quasiInv_comm θ hinj _ hN (homothety a) (homothety a) (hH a) g)

  have hODact : ∀ a, (ρ.comp (Φ.actEnd a)).toPowerSeries = ((Φ'.actEnd a).comp ρ).toPowerSeries := by
    intro a
    refine toPowerSeries_eq_of_map_eq _ _ fun f => ?_
    rw [MvFormalGroup.CartierModule.map_comp, MvFormalGroup.CartierModule.map_comp, hρ, ← endAct_apply, hAct, endAct_apply, hρ]
  have hODvarpi : (ρ.comp Φ.varpiEnd).toPowerSeries = (Φ'.varpiEnd.comp ρ).toPowerSeries := by
    refine toPowerSeries_eq_of_map_eq _ _ fun f => ?_
    rw [MvFormalGroup.CartierModule.map_comp, MvFormalGroup.CartierModule.map_comp, hρ, ← endAct_apply, hPi, endAct_apply, hρ]
  have hquasi : (ρ'.comp ρ).toPowerSeries = Φ.F.nthSeries (p ^ N) := by
    rw [← MvFormalGroup.End.toPowerSeries_natCast]
    refine toPowerSeries_eq_of_map_eq (ρ'.comp ρ) ((p ^ N : ℕ) : MvFormalGroup.End Φ.F) fun f => ?_
    rw [MvFormalGroup.CartierModule.map_comp, hρ, hρ', hθ', quasiInv_apply, ← endAct_apply, endAct_natCast]
  have hOD : IsODHom Φ.toFormalODModule Φ'.toFormalODModule ρ.toPowerSeries :=
    ⟨IsLawHom.of_hom ρ, fun a => hODact a, hODvarpi⟩

  set J : Ideal (MvPowerSeries (Fin 2) k) := Ideal.span (Set.range ρ.toPowerSeries) with hJ
  set I : Ideal (MvPowerSeries (Fin 2) k) := Ideal.span (Set.range (Φ.F.nthSeries (p ^ N))) with hI
  have hIJ : I ≤ J := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← hquasi]
    exact subst_mem_span_range ρ.hasSubst_toPowerSeries (ρ'.toPowerSeries i) (ρ'.constantCoeff_eq_zero i)
  have hp1 : Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (Φ.F.nthSeries p))) =
      p ^ 4 := by
    have h4 := Φ.hasHeight.2.2 k (RingHom.id k)
    rw [Series.map_ringHom_id, act_natCast] at h4
    exact h4
  have hpN : Module.finrank k (MvPowerSeries (Fin 2) k ⧸ I) = p ^ (N * 4) :=
    MvFormalGroup.finrank_quotient_span_nthSeries_pow_eq_pow p Φ.F 4 hp1 N
  haveI hfinI : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ I) :=
    Module.finite_of_finrank_pos (by rw [hpN]; exact pow_pos hp.out.pos _)
  have hfinJ : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ k hIJ).toLinearMap
      (Ideal.Quotient.factor_surjective hIJ)

  obtain ⟨h, hh⟩ := MvFormalGroup.Hom.exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm p k Φ.F Φ'.F ρ hfinJ
  refine ⟨ρ.toPowerSeries, h, hOD, hfinJ, inferInstance, fun κ _ f => ?_⟩
  exact hh κ f

end P2mKcK2bAssembly

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ (ρ : CerednikDrinfeld.SpecialFormal.Series k) (h : ℕ),
      CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule
        ρ h :=
  P2mKcK2bAssembly.main j Φ Φ'

end

end S_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed (solution)
