-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c1e1ba59-ba31-59b3-86ff-d342e1b93ace

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
import Theorems.Thm_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic
import Theorems.Thm_CerednikDrinfeld_exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible
import Theorems.Thm_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

noncomputable section

open MvPowerSeries
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

namespace R4LocQisogAdm

variable {p : ℕ} [hp : Fact p.Prime]

theorem ofAdd_pow (v c : ℤ) : (Multiplicative.ofAdd v) ^ c = Multiplicative.ofAdd (c * v) := by
  rw [← ofAdd_zsmul, smul_eq_mul]

theorem nu_eq_two_mul
    (vdet ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[p]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[p]) =
        algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) * (algebraMap ℤ_[p] ℚ_[p] ((p : ℕ) : ℤ_[p])) ^ n)
    (c : ℤ) (hc : ∀ g, ν g = (vdet g) ^ c)
    (h4 : ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p],
      (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) →
        ν g = Multiplicative.ofAdd (4 : ℤ))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) :
    ν g = Multiplicative.ofAdd (2 * Multiplicative.toAdd (vdet g)) := by
  have hdet : ((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  set gr := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hgr
  have hgr_coe : (gr : Matrix (Fin 2) (Fin 2) ℚ_[p]) = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
    rfl
  have hv2 : vdet gr = Multiplicative.ofAdd 2 := by
    refine (hvdet gr 2).2 ⟨1, ?_⟩
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgr_coe, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin, Units.val_one, map_one, one_mul, map_natCast, zpow_ofNat]
  have hc2 : c = 2 := by
    have := h4 gr hgr_coe
    rw [hc, hv2, ofAdd_pow] at this
    have h' : c * 2 = 4 := Multiplicative.ofAdd.injective this
    omega
  rw [hc g, hc2]
  conv_lhs => rw [show vdet g = Multiplicative.ofAdd (Multiplicative.toAdd (vdet g)) from rfl]
  rw [ofAdd_pow]

private theorem _root_.R4LocQisogAdm.mem_centralizer_iff {B : Type u} [CommRing B] (X : FormalODModule p B) (e : MvFormalGroup.End X.F) :
    e ∈ Subring.centralizer (Set.range X.actEnd ∪ {X.varpiEnd}) ↔
      (∀ a, X.actEnd a * e = e * X.actEnd a) ∧ X.varpiEnd * e = e * X.varpiEnd := by
  rw [Subring.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Set.mem_union_left _ ⟨a, rfl⟩), h _ (Set.mem_union_right _ (Set.mem_singleton _))⟩
  · rintro ⟨h1, h2⟩ g hg
    rcases hg with ⟨a, rfl⟩ | hg
    · exact h1 a
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact h2

p2m_export "R4LocQisogAdm" "mem_centralizer_iff"

theorem isODHom_of_mem_centralizer {B : Type u} [CommRing B] (X : FormalODModule p B)
    (e : Subring.centralizer (Set.range X.actEnd ∪ {X.varpiEnd})) :
    IsODHom X X (e : MvFormalGroup.End X.F).toPowerSeries := by
  obtain ⟨h1, h2⟩ := (mem_centralizer_iff X e).1 e.2
  refine ⟨IsLawHom.of_hom _, fun a => ?_, ?_⟩
  · have := congrArg MvFormalGroup.Hom.toPowerSeries (h1 a).symm
    rw [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_mul] at this
    exact this
  · have := congrArg MvFormalGroup.Hom.toPowerSeries h2.symm
    rw [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_mul] at this
    exact this

theorem exists_isIsogenyOfHeight_self_four_mul_add_two (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) :
    ∃ (e : Series k) (m : ℕ), IsIsogenyOfHeight Φ.toFormalODModule Φ.toFormalODModule e (4 * m + 2) := by
  obtain ⟨θ, hθinj, m, hsurj, hsand⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed p k j Φ
  obtain ⟨ν, hν4, hν⟩ :=
    CerednikDrinfeld.FormalODModule.exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
      k Φ.toFormalODModule Φ.hasHeight θ ⟨hθinj, m, hsurj, hsand⟩

  set A : Matrix (Fin 2) (Fin 2) ℤ_[p] := Matrix.diagonal ![((p : ℕ) : ℤ_[p]), 1] with hA
  obtain ⟨e, he⟩ := hsurj A
  have hAmap : A.map ((↑) : ℤ_[p] → ℚ_[p]) = Matrix.diagonal ![(p : ℚ_[p]), 1] := by
    rw [hA]
    ext i i'
    fin_cases i <;> fin_cases i' <;> simp [Matrix.diagonal, Matrix.map_apply]
  have hdetθ : (θ e).det = (p : ℚ_[p]) ^ (2 * m + 1) := by
    rw [he, hAmap, Matrix.det_smul, Matrix.det_diagonal, Fintype.card_fin, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    ring
  have hdet : (θ e).det ≠ 0 := by
    rw [hdetθ]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  set g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hg
  have hg_coe : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = θ e := rfl
  obtain ⟨h₁, hνg, hfin, hfib⟩ := hν e g hg_coe

  obtain ⟨vdet, hvdet⟩ :=
    CerednikDrinfeld.exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible ℤ_[p] inferInstance
      (p : ℤ_[p]) PadicInt.irreducible_p ℚ_[p] (Fin 2)
  obtain ⟨c, hc⟩ :=
    CerednikDrinfeld.exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic vdet hvdet ν
  have hνg' := nu_eq_two_mul vdet ν hvdet c hc hν4 g
  have hvg : vdet g = Multiplicative.ofAdd ((2 * m + 1 : ℕ) : ℤ) := by
    refine (hvdet g _).2 ⟨1, ?_⟩
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg_coe, hdetθ, Units.val_one, map_one, one_mul, map_natCast,
      zpow_natCast]
  rw [hνg, hvg] at hνg'
  have hh₁ : (h₁ : ℤ) = 2 * ((2 * m + 1 : ℕ) : ℤ) := by
    have := Multiplicative.ofAdd.injective hνg'
    rw [toAdd_ofAdd] at this
    exact this
  have hh₁' : h₁ = 4 * m + 2 := by push_cast at hh₁; omega

  haveI : Module.Free k (KerAlgebra (e : MvFormalGroup.End Φ.F).toPowerSeries) := Module.Free.of_divisionRing _ _
  refine ⟨(e : MvFormalGroup.End Φ.F).toPowerSeries, m, isODHom_of_mem_centralizer Φ.toFormalODModule e,
    hfin, Module.Projective.of_free, fun κ _ f => ?_⟩
  rw [← hh₁']
  exact hfib κ f

theorem isIsogenyOfHeight_comp (k : Type u) [Field k]
    {X Y Z : FormalODModule p k} {ψ φ : Series k} {h h' : ℕ}
    (hψ : IsIsogenyOfHeight Y Z ψ h) (hφ : IsIsogenyOfHeight X Y φ h') :
    IsIsogenyOfHeight X Z (ψ.comp φ) (h + h') := by
  refine ⟨hψ.1.comp hφ.1, ?_⟩
  have hψ0 : ∀ i, constantCoeff (ψ i) = 0 := hψ.1.constantCoeff
  have hφ0 : ∀ i, constantCoeff (φ i) = 0 := hφ.1.constantCoeff

  obtain ⟨hfinψ, -, hfibψ⟩ := hψ.2
  obtain ⟨hfinφ, -, hfibφ⟩ := hφ.2
  obtain ⟨hfin, -⟩ :=
    MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul (k := k) ψ φ hψ0 hφ0 hfinψ hfinφ
  haveI : Module.Finite k (KerAlgebra (ψ.comp φ)) := hfin
  haveI : Module.Free k (KerAlgebra (ψ.comp φ)) := Module.Free.of_divisionRing _ _
  refine ⟨hfin, Module.Projective.of_free, fun κ _ f => ?_⟩

  have hp0 : (p : ℕ) ^ h ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hmap : (ψ.comp φ).map f = (ψ.map f).comp (φ.map f) := Series.map_comp f ψ φ hφ0
  have hψ0' : ∀ i, constantCoeff ((ψ.map f) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map f (ψ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hψ0, map_zero]
  have hφ0' : ∀ i, constantCoeff ((φ.map f) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map f (φ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hφ0, map_zero]
  have hfinψ' : Module.Finite κ (KerAlgebra (ψ.map f)) :=
    Module.finite_of_finrank_pos (by rw [hfibψ κ f]; exact pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero))
  have hfinφ' : Module.Finite κ (KerAlgebra (φ.map f)) :=
    Module.finite_of_finrank_pos (by rw [hfibφ κ f]; exact pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero))
  obtain ⟨-, hrk⟩ :=
    MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul (k := κ) (ψ.map f) (φ.map f)
      hψ0' hφ0' hfinψ' hfinφ'
  rw [hmap]
  show Module.finrank κ (KerAlgebra ((ψ.map f).comp (φ.map f))) = p ^ (h + h')
  rw [pow_add, ← hfibψ κ f, ← hfibφ κ f]
  exact hrk

theorem main (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : Zp2 p →+* k) (Φ Φ' : SpecialFormalODModule p j) :
    ∃ (ρ : Series k) (n : ℕ), IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ (4 * n) := by
  obtain ⟨ρ, h, hρ⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed p k j Φ Φ'
  obtain ⟨a, ha⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.even_of_isIsogenyOfHeight_of_isAlgClosed p k j Φ Φ' ρ h hρ
  rcases Nat.even_or_odd a with ⟨n, hn⟩ | ⟨n, hn⟩
  · refine ⟨ρ, n, ?_⟩
    rw [show 4 * n = h by omega]
    exact hρ
  · obtain ⟨e, m, he⟩ := exists_isIsogenyOfHeight_self_four_mul_add_two k j Φ
    refine ⟨ρ.comp e, n + m + 1, ?_⟩
    rw [show 4 * (n + m + 1) = h + (4 * m + 2) by omega]
    exact isIsogenyOfHeight_comp k hρ he

end R4LocQisogAdm

end

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ (ρ : CerednikDrinfeld.SpecialFormal.Series k) (n : ℕ),
      CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule
        ρ (4 * n) :=
  R4LocQisogAdm.main k j Φ Φ'

end S_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_four_mul_of_isAlgClosed (solution)
