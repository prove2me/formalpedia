-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/955f23c5-4c8a-5d01-83aa-e5a1618f238f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_MvFormalGroup_CartierModule_length_quotient_range_mapLinear_eq_of_finrank_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace LinearMap p2m_export "LinearMap" "mem_range range mk frobenius_def comp ker" end LinearMap
p2m_open_scoped "LinearMap" in

theorem LinearMap.R1a_exists_forall_exists_eq_pow_smul {R : Type*} [CommRing R] [IsLocalRing R]
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (π : R) (hπ : ¬ IsUnit π)
    (hfl : IsFiniteLength R (M' ⧸ LinearMap.range f)) :
    ∃ n : ℕ, ∀ m : M', ∃ a : M, f a = π ^ n • m := by
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  have hloc : ∀ w : R, IsUnit (1 - w * π) := fun w =>
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (fun hu => hπ (isUnit_of_mul_isUnit_right hu))
  have hkill : ∀ q : M' ⧸ LinearMap.range f, ∃ n : ℕ, π ^ n • q = 0 := by
    intro q
    haveI := hart
    let g : ℕ →o (Submodule R (M' ⧸ LinearMap.range f))ᵒᵈ :=
      ⟨fun n => OrderDual.toDual (Submodule.span R {π ^ n • q}), fun a b hab => by
         change Submodule.span R {π ^ b • q} ≤ Submodule.span R {π ^ a • q}
         rw [Submodule.span_singleton_le_iff_mem]
         obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
         rw [pow_add, mul_comm, mul_smul]
         exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
    obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes g
    have hmem : π ^ n • q ∈ Submodule.span R {π ^ (n + 1) • q} := by
      have := hn (n + 1) (Nat.le_succ n)
      change OrderDual.toDual (Submodule.span R {π ^ n • q}) =
        OrderDual.toDual (Submodule.span R {π ^ (n + 1) • q}) at this
      rw [← OrderDual.toDual.injective this]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp hmem
    rw [pow_succ', mul_smul] at hw
    exact ⟨n, (hloc w).smul_eq_zero.mp (by rw [sub_smul, one_smul, mul_smul, hw, sub_self])⟩
  haveI := hnoeth
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (⊤ : Submodule R (M' ⧸ LinearMap.range f))
  choose nq hnq using hkill
  refine ⟨s.sup nq, fun m => ?_⟩
  have hunif : ∀ q : M' ⧸ LinearMap.range f, π ^ (s.sup nq) • q = 0 := by
    intro q
    have hq : q ∈ Submodule.span R (s : Set (M' ⧸ LinearMap.range f)) := by rw [hs]; exact Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := nq) hx)
      rw [hc, pow_add, mul_comm, mul_smul, hnq, smul_zero]
    | zero => exact smul_zero _
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_comm, hx, smul_zero]
  have h0 := hunif (Submodule.Quotient.mk m)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at h0
  exact h0

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    (∃ h : ℕ, ∀ m : MvFormalGroup.CartierModule p (t'.XbarS (Rigidified.awayHom (1 : K))).F,
        ∃ a : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).F, Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K)) a = p ^ h • m) ∧
      Function.Injective (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) := by

  have hS1 : Function.Injective (algebraMap K (Rigidified.Baway (1 : K))) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 (one_mem _))
  haveI : Nontrivial (Rigidified.Baway (1 : K)) := hS1.nontrivial
  have hpS : pIdeal p (Rigidified.Baway (1 : K)) = ⊥ := by
    refine Ideal.span_singleton_eq_bot.mpr ?_
    rw [← map_natCast (algebraMap K (Rigidified.Baway (1 : K))) p, CharP.cast_eq_zero, map_zero]
  haveI hntK' : Nontrivial (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [hpS]; exact bot_ne_top)
  have hsurjS : Function.Surjective (algebraMap K (Rigidified.Baway (1 : K))) := by
    intro z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (Submonoid.powers (1 : K)) z
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    refine ⟨x, ?_⟩
    rw [← hxs]
    have hs1 : ((s : K)) = 1 := by rw [← hn, one_pow]
    rw [hs1, map_one, mul_one]
  let e0 : K →+* Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K)) :=
    (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))).comp (algebraMap K (Rigidified.Baway (1 : K)))
  have he0surj : Function.Surjective e0 := Ideal.Quotient.mk_surjective.comp hsurjS
  have he0inj : Function.Injective e0 := RingHom.injective e0
  have hfield : IsField (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) :=
    MulEquiv.isField (Field.toIsField K) (RingEquiv.ofBijective e0 ⟨he0inj, he0surj⟩).symm.toMulEquiv
  haveI : (pIdeal p (Rigidified.Baway (1 : K))).IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  letI instF : Field (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) := Ideal.Quotient.field _
  haveI : CharP (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) p :=
    charP_of_injective_ringHom he0inj p
  haveI : PerfectRing (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) p := by
    refine PerfectRing.ofSurjective _ p fun x => ?_
    obtain ⟨y, rfl⟩ := he0surj x
    obtain ⟨z, rfl⟩ := (bijective_frobenius K p).2 y
    exact ⟨e0 z, by simp only [frobenius_def, map_pow]⟩

  have hdeg : Module.finrank (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K)))
      (MvPowerSeries (Fin 2) (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) ⧸
        Ideal.span (Set.range ((ht'.2.2.1.1.map (reduceMap (Rigidified.awayHom (1 : K)))).toHom.toPowerSeries))) =
      p ^ (4 * t'.n) :=
    ht'.2.2.2.2.2 _ (reduceMap (Rigidified.awayHom (1 : K)))
  have hlen := MvFormalGroup.CartierModule.length_quotient_range_mapLinear_eq_of_finrank_eq_pow p
    (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).F (t'.XbarS (Rigidified.awayHom (1 : K))).F
    ((ht'.2.2.1.1.map (reduceMap (Rigidified.awayHom (1 : K)))).toHom) (4 * t'.n) hdeg

  have hfl := Module.length_ne_top_iff.mp (by rw [hlen]; exact ENat.coe_ne_top _)
  obtain ⟨h, hh⟩ := LinearMap.R1a_exists_forall_exists_eq_pow_smul _ _ (WittVector.irreducible p).not_isUnit hfl

  refine ⟨⟨h, fun m => ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hh m
    refine ⟨a, ?_⟩
    rw [MvFormalGroup.CartierModule.mapLinear_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at ha
    exact ha

  · have hfin : Module.Finite (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K)))
        (MvPowerSeries (Fin 2) (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) ⧸
          Ideal.span (Set.range ((ht'.2.2.1.1.map (reduceMap (Rigidified.awayHom (1 : K)))).toHom.toPowerSeries))) :=
      Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos (Fact.out : p.Prime).pos _)
    exact MvFormalGroup.CartierModule.map_injective_of_finite_quotient p _ _
      ((ht'.2.2.1.1.map (reduceMap (Rigidified.awayHom (1 : K)))).toHom) hfin

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed (solution)
