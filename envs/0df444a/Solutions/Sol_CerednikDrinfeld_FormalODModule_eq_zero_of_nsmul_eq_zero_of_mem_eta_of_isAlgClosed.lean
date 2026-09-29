-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6c0c920d-5c72-53b5-8c0e-728df08135ad

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace B28ETF

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)

theorem nsmul_nMk (k : ℕ) (m m' : D.M) : k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nMk_eq_zero_iff (a b : D.M) :
    D.nMk (a, b) = 0 ↔ ∃ m : D.M, a = D.verschiebung m ∧ b = -D.varpi m := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m, hm⟩
    rw [nRelMap_apply, Prod.mk.injEq] at hm
    refine ⟨D.ofSigma m, hm.1.symm, ?_⟩
    have h2 := congrArg D.ofSigma hm.2
    rw [ofSigma_toSigma, ofSigma_toSigma] at h2
    exact h2.symm
  · rintro ⟨m, rfl, rfl⟩
    exact ⟨D.toSigma m, by rw [nRelMap_apply, ofSigma_toSigma]⟩

theorem nMk_zero_eq_zero_iff (hV : Function.Injective D.verschiebung) (b : D.M) :
    D.nMk (0, b) = 0 ↔ b = 0 := by
  rw [nMk_eq_zero_iff]
  constructor
  · rintro ⟨m, h1, h2⟩
    have : m = 0 := hV (by rw [← h1, map_zero])
    rw [h2, this, map_zero, neg_zero]
  · intro h
    exact ⟨0, by rw [map_zero], by rw [h, map_zero, neg_zero]⟩

theorem nsmul_p_nMk (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x) (x x' : D.M) :
    (p : ℕ) • D.nMk (x, x') = D.nMk (0, D.frobenius (D.lambda (D.nMk (x, x')))) := by
  rw [nsmul_nMk, lambda_nMk, map_add, ← D.varpi_frobenius, D.frobenius_verschiebung, ← hVF x]
  have : (D.verschiebung (D.frobenius x), (p : ℕ) • x') =
      (D.verschiebung (D.frobenius x), -D.varpi (D.frobenius x)) + (0, D.varpi (D.frobenius x) + (p : ℕ) • x') := by
    ext <;> simp
  rw [this, map_add, nMk_verschiebung_neg_varpi, zero_add]

theorem varpi_lambda_eq_verschiebung_lambda
    (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (x x' : D.M)
    (hfix : D.phi L hL.map_verschiebung (D.nMk (x, x')) = D.nMk (x, x')) :
    D.varpi (D.lambda (D.nMk (x, x'))) = D.verschiebung (D.lambda (D.nMk (x, x'))) := by
  have h1 : D.lambda (D.phi L hL.map_verschiebung (D.nMk (x, x'))) = D.frobenius x + D.varpi x' := by
    rw [phi_nMk, map_add, hL.lambda_comp, lambda_nMk, map_zero, add_zero]
  rw [hfix, lambda_nMk] at h1
  rw [lambda_nMk, map_add, D.varpi_varpi, ← hVF, D.varpi_verschiebung, ← map_add, h1, map_add]

theorem mem_piece_of_verschiebung_mem (hV : Function.Injective D.verschiebung) (k : Fin 2) (y : D.M)
    (hy : D.verschiebung y ∈ D.piece (k + 1)) : y ∈ D.piece k := by
  have hc := D.isCompl_piece
  have hk1 : k + 1 + 1 = k := by fin_cases k <;> rfl

  have hck : IsCompl (D.piece k) (D.piece (k + 1)) := by
    fin_cases k
    · exact hc
    · simpa using hc.symm
  have htop : y ∈ D.piece k ⊔ D.piece (k + 1) := by rw [hck.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp htop
  have hV1 : D.verschiebung y₁ ∈ D.piece k := by
    have := D.verschiebung_mem (k + 1) y₁ hy₁
    rwa [hk1] at this
  have hV1' : D.verschiebung y₁ ∈ D.piece (k + 1) := by
    have h0 := D.verschiebung_mem k y₀ hy₀
    have : D.verschiebung y₁ = D.verschiebung (y₀ + y₁) - D.verschiebung y₀ := by rw [map_add]; abel
    rw [this]
    exact Submodule.sub_mem _ hy h0
  have hzero : D.verschiebung y₁ = 0 := by
    have := hck.disjoint
    rw [Submodule.disjoint_def] at this
    exact this _ hV1 hV1'
  have : y₁ = 0 := hV (by rw [hzero, map_zero])
  rw [this, add_zero]; exact hy₀

end Datum

section Model

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p]
  (j : Zp2 p →+* K) (X : FormalODModule p K)
  (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
  (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))

local notation "𝔇" => X.toGradedCartierModuleData j hc

theorem hVinj : Function.Injective (verschiebungInt (p := p) (Φ := X.F)) :=
  verschiebungInt_injective_of_isNilpotent p (by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero) X.F

theorem hVF (f : CartierModule p X.F) : verschiebungInt (frobenius f) = (p : ℕ) • f := by
  rw [verschiebungInt_apply_eq_verschiebung]; exact verschiebung_frobenius f

include hγ in

theorem eq_zero_of_smul_tangent_eq_zero (i : Fin 2) (b : K) (h : b • tangent (γ i) = 0) : b = 0 := by
  set Mγ : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i k => tangent (γ i) k with hM
  have hrow : ∀ k, b * Mγ i k = 0 := by
    intro k
    have h1 := congrArg (fun v : Fin 2 → K => v k) h
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [hM, Matrix.of_apply]
    exact h1
  have hunit : Mγ * Mγ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hγ.2
  have h1 := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N i i) hunit
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  calc b = b * 1 := (mul_one b).symm
    _ = b * ∑ k : Fin 2, Mγ i k * Mγ⁻¹ k i := by rw [h1]
    _ = ∑ k : Fin 2, b * Mγ i k * Mγ⁻¹ k i := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := Finset.sum_eq_zero fun k _ => by rw [hrow k, zero_mul]

include hγ in

theorem exists_eq_homothety_add (i : Fin 2) (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i : ℕ)) :
    ∃ (c : K) (y : CartierModule p X.F), y ∈ X.gradedPiece j ((i : ℕ) + 1) ∧
      m = homothety c (γ i) + verschiebungInt y := by
  have hLie := (FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p j
    (by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero) X γ hγ).2.2.2
  obtain ⟨⟨c, y⟩, hy, hmy⟩ := (FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
    p j X hLie γ hγ (i : ℕ) 1 m hm).exists
  refine ⟨c 0, y, hy, ?_⟩
  rw [Fin.sum_univ_one] at hmy
  have hi : (⟨((i : ℕ) + ((0 : Fin 1) : ℕ)) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = i :=
    Fin.ext (by simp only [Fin.val_zero, add_zero]; exact Nat.mod_eq_of_lt i.isLt)
  rw [hi] at hmy
  rw [verschiebungInt_apply_eq_verschiebung]
  exact hmy

variable {a : ℕ → Fin 2 → K}

omit hγ in

theorem varpi_basis (ha : X.HasStructureConstants γ a) (i : Fin 2) :
    ∃ h : CartierModule p X.F, endAct X.varpiEnd (γ i) = homothety (a 0 i) (γ (i + 1)) + verschiebungInt h := by
  obtain ⟨h, hh⟩ := ha i 1
  refine ⟨h, ?_⟩
  have hpi : FormalODModule.piIndex 0 i = i + 1 := by
    ext; fin_cases i <;> simp [FormalODModule.piIndex_val]
  simpa [Fin.sum_univ_one, hpi] using hh

include hγ in

theorem critical_of_eq_zero (ha : X.HasStructureConstants γ a) (i : Fin 2) (hi : a 0 i = 0)
    (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i : ℕ)) :
    ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  obtain ⟨c, y, -, rfl⟩ := exists_eq_homothety_add j X γ hγ i m hm
  obtain ⟨h, hh⟩ := varpi_basis X γ ha i
  rw [hi, homothety_zero_left, zero_add] at hh
  refine ⟨homothety (c ^ p) h + endAct X.varpiEnd y, ?_⟩
  rw [map_add, map_add, endAct_homothety, hh, homothety_verschiebungInt, endAct_verschiebungInt]

include hγ in

theorem exists_verschiebungInt_eq_of_ne_zero (ha : X.HasStructureConstants γ a) (i : Fin 2) (hi : a 0 i ≠ 0)
    (x : CartierModule p X.F) (hx : x ∈ X.gradedPiece j (i : ℕ))
    (hPi : ∃ w : CartierModule p X.F, verschiebungInt w = endAct X.varpiEnd x) :
    ∃ x₀ : CartierModule p X.F, verschiebungInt x₀ = x := by
  obtain ⟨c, y, -, rfl⟩ := exists_eq_homothety_add j X γ hγ i x hx
  obtain ⟨h, hh⟩ := varpi_basis X γ ha i
  obtain ⟨w, hw⟩ := hPi

  have key : endAct X.varpiEnd (homothety c (γ i) + verschiebungInt y) =
      homothety (c * a 0 i) (γ (i + 1)) + verschiebungInt (homothety (c ^ p) h + endAct X.varpiEnd y) := by
    rw [map_add, endAct_homothety, hh, map_add, homothety_mul, homothety_verschiebungInt, endAct_verschiebungInt, map_add]
    abel
  have ht := congrArg tangent (hw.trans key)
  rw [tangent_verschiebungInt, map_add, tangent_homothety, tangent_verschiebungInt, add_zero] at ht
  have hca : c * a 0 i = 0 := eq_zero_of_smul_tangent_eq_zero j X γ hγ (i + 1) _ ht.symm
  have hc0 : c = 0 := (mul_eq_zero.mp hca).resolve_right hi
  refine ⟨y, ?_⟩
  rw [hc0, homothety_zero_left, zero_add]

omit hγ in

theorem frobenius_eq_varpi (u ℓ : CartierModule p X.F) (hℓ : verschiebungInt ℓ = endAct X.varpiEnd u) :
    frobenius u = endAct X.varpiEnd ℓ := by
  apply hVinj X
  rw [hVF, ← endAct_verschiebungInt, hℓ]
  exact (FormalODModule.endAct_varpiEnd_endAct_varpiEnd X u).symm

include hγ in

theorem homog (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (ha : X.HasStructureConstants γ a) (hmul0 : a 0 0 = 0 ∨ a 0 1 = 0)
    (k : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung k)
    (hpz : (p : ℕ) • z = 0) : z = 0 := by
  classical
  have hV : Function.Injective (𝔇).verschiebung := B28ETF.hVinj X
  have hVF : ∀ x : (𝔇).M, (𝔇).verschiebung ((𝔇).frobenius x) = (p : ℕ) • x := fun x => B28ETF.hVF X x
  obtain ⟨hzeta, hzpiece⟩ := AddSubgroup.mem_inf.mp hz
  obtain ⟨⟨x, x'⟩, hxx', rfl⟩ := AddSubgroup.mem_map.mp hzpiece
  obtain ⟨hx, hx'⟩ := AddSubgroup.mem_prod.mp hxx'
  have hx : x ∈ (𝔇).piece k := hx
  have hx' : x' ∈ (𝔇).piece k := hx'
  have hfix : (𝔇).phi L hL.isCartierLMap.map_verschiebung ((𝔇).nMk (x, x')) = (𝔇).nMk (x, x') :=
    ((𝔇).mem_eta_iff L _ _).mp hzeta

  have htors : (𝔇).frobenius ((𝔇).lambda ((𝔇).nMk (x, x'))) = 0 := by
    rw [B28ETF.nsmul_p_nMk (𝔇) hVF] at hpz
    exact (B28ETF.nMk_zero_eq_zero_iff (𝔇) hV _).mp hpz

  have hβ := B28ETF.varpi_lambda_eq_verschiebung_lambda (𝔇) hVF L hL.isCartierLMap x x' hfix
  by_cases hk : a 0 k = 0
  ·
    have crit : ∀ m ∈ (𝔇).piece k, ∃ g : (𝔇).M, (𝔇).verschiebung g = (𝔇).varpi m :=
      B28ETF.critical_of_eq_zero j X γ hγ ha k hk
    obtain ⟨y, hy⟩ := crit x hx
    have hy_mem : y ∈ (𝔇).piece k := by
      refine B28ETF.mem_piece_of_verschiebung_mem (𝔇) hV k y ?_
      rw [hy]; exact (𝔇).varpi_mem k x hx
    have hLx : L x = (𝔇).nMk (y, 0) :=
      FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL (k : ℕ) crit x y hx hy

    have hu_mem : y + x' ∈ (𝔇).piece k := add_mem hy_mem hx'
    have hζ : (𝔇).nMk (x, x') = (𝔇).nMk (y + x', 0) := by
      rw [← hfix, phi_nMk, hLx, ← map_add, Prod.mk_add_mk, add_zero]
    obtain ⟨ℓ, hℓ⟩ := crit (y + x') hu_mem
    have hℓ_mem : ℓ ∈ (𝔇).piece k := by
      refine B28ETF.mem_piece_of_verschiebung_mem (𝔇) hV k ℓ ?_
      rw [hℓ]; exact (𝔇).varpi_mem k _ hu_mem
    have hLu : L (y + x') = (𝔇).nMk (ℓ, 0) :=
      FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL (k : ℕ) crit (y + x') ℓ hu_mem hℓ

    have hfix' : (𝔇).phi L hL.isCartierLMap.map_verschiebung ((𝔇).nMk (y + x', 0)) = (𝔇).nMk (y + x', 0) := by
      rw [← hζ]; exact hfix
    rw [phi_nMk, hLu, ← map_add, Prod.mk_add_mk] at hfix'
    simp only [add_zero] at hfix'
    have hdiff : (𝔇).nMk (ℓ - (y + x'), 0) = 0 := by
      have : (ℓ - (y + x'), (0 : (𝔇).M)) = (ℓ, (0 : (𝔇).M)) - (y + x', 0) := by ext <;> simp
      rw [this, map_sub, hfix', sub_self]
    obtain ⟨m, hm1, hm2⟩ := (B28ETF.nMk_eq_zero_iff (𝔇) _ _).mp hdiff
    have hPim : (𝔇).varpi m = 0 := by
      have : -(𝔇).varpi m = 0 := hm2.symm
      rwa [neg_eq_zero] at this

    rw [hζ, lambda_nMk, map_zero, add_zero] at htors
    have hFℓ : (𝔇).frobenius ℓ = 0 := by
      apply hV
      rw [hVF, map_zero, ← (𝔇).frobenius_verschiebung, hℓ]
      exact htors
    have hFu : (𝔇).frobenius (y + x') = (𝔇).varpi ℓ := B28ETF.frobenius_eq_varpi X (y + x') ℓ hℓ
    have hℓu : ℓ = (y + x') + (𝔇).verschiebung m := by rw [← hm1]; abel
    have hVℓ : (𝔇).verschiebung ℓ = 0 := by
      have e1 : (𝔇).frobenius ℓ = (𝔇).frobenius (y + x') := by
        rw [hℓu, map_add, (𝔇).frobenius_verschiebung, ← (𝔇).varpi_varpi, hPim, map_zero, add_zero]
      have e2 : (𝔇).varpi ℓ = (𝔇).verschiebung ℓ := by
        conv_lhs => rw [hℓu]
        rw [map_add, (𝔇).varpi_verschiebung, hPim, map_zero, add_zero]
        exact hℓ.symm
      rw [← e2, ← hFu, ← e1, hFℓ]
    have hℓ0 : ℓ = 0 := hV (by rw [hVℓ, map_zero])
    have hu0 : y + x' = -(𝔇).verschiebung m := by
      have : ℓ - (y + x') = (𝔇).verschiebung m := hm1
      rw [hℓ0, zero_sub] at this
      rw [← this, neg_neg]
    rw [hζ, hu0]
    have : ((-(𝔇).verschiebung m), (0 : (𝔇).M)) = -((𝔇).verschiebung m, -(𝔇).varpi m) := by
      ext <;> simp [hPim]
    rw [this, map_neg, nMk_verschiebung_neg_varpi, neg_zero]
  ·
    have hk1 : a 0 (k + 1) = 0 := by
      fin_cases k
      · simpa using hmul0.resolve_left hk
      · simpa using hmul0.resolve_right hk
    have crit : ∀ m ∈ (𝔇).piece (k + 1), ∃ g : (𝔇).M, (𝔇).verschiebung g = (𝔇).varpi m :=
      B28ETF.critical_of_eq_zero j X γ hγ ha (k + 1) hk1
    have hv_mem : (𝔇).lambda ((𝔇).nMk (x, x')) ∈ (𝔇).piece (k + 1) := by
      rw [lambda_nMk]
      exact add_mem ((𝔇).varpi_mem k x hx) ((𝔇).verschiebung_mem k x' hx')
    obtain ⟨ℓ, hℓ⟩ := crit _ hv_mem

    have hℓv : ℓ = (𝔇).lambda ((𝔇).nMk (x, x')) := hV (by rw [hℓ]; exact hβ)
    have hFv := B28ETF.frobenius_eq_varpi X ((𝔇).lambda ((𝔇).nMk (x, x'))) ℓ hℓ
    have hFv' : (𝔇).frobenius ((𝔇).lambda ((𝔇).nMk (x, x'))) = (𝔇).varpi ((𝔇).lambda ((𝔇).nMk (x, x'))) := by
      rw [hℓv] at hFv; exact hFv
    have hv0 : (𝔇).lambda ((𝔇).nMk (x, x')) = 0 := by
      apply hV
      rw [map_zero, ← hβ, ← hFv']
      exact htors

    have hsum : (𝔇).varpi x + (𝔇).verschiebung x' = 0 := by rw [← lambda_nMk]; exact hv0
    have hPix : ∃ w : (𝔇).M, (𝔇).verschiebung w = (𝔇).varpi x := by
      refine ⟨-x', ?_⟩
      rw [map_neg, eq_comm, ← add_eq_zero_iff_eq_neg]; exact hsum
    obtain ⟨x₀, hx₀⟩ := B28ETF.exists_verschiebungInt_eq_of_ne_zero j X γ hγ ha k hk x hx hPix
    have hx₀' : (𝔇).verschiebung x₀ = x := hx₀
    have e1 : (𝔇).nMk (x, x') = (𝔇).nMk (0, x' + (𝔇).varpi x₀) := by
      have : (x, x') = ((𝔇).verschiebung x₀, -(𝔇).varpi x₀) + (0, x' + (𝔇).varpi x₀) := by
        ext
        · simp [hx₀']
        · simp
      rw [this, map_add, nMk_verschiebung_neg_varpi, zero_add]
    have e2 : x' + (𝔇).varpi x₀ = 0 := by
      apply hV
      rw [map_zero, map_add, ← (𝔇).varpi_verschiebung, hx₀', add_comm]
      exact hsum
    rw [e1, e2]
    exact (B28ETF.nMk_zero_eq_zero_iff (𝔇) hV 0).mpr rfl

end Model

end B28ETF

open B28ETF in
theorem solution
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p]
    (j : Zp2 p →+* K) (X : FormalODModule p K)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (ζ : (X.toGradedCartierModuleData j hc).NMod)
    (hζ : ζ ∈ (X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung)
    (hp : p • ζ = 0) :
    ζ = 0 := by
  classical
  obtain ⟨a, ha, hmul⟩ := FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis p j X γ hγ
  have hmul0 : a 0 0 = 0 ∨ a 0 1 = 0 := by
    rw [CharP.cast_eq_zero] at hmul; exact mul_eq_zero.mp hmul

  obtain ⟨z₀, hz₀, z₁, hz₁, rfl⟩ :=
    GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq p j (X.toGradedCartierModuleData j hc) L hL ζ hζ
  have hcN := GradedCartierModuleData.isCompl_nPiece_zero_one p j (X.toGradedCartierModuleData j hc)
  have h0 : (p : ℕ) • z₀ ∈ (X.toGradedCartierModuleData j hc).nPiece 0 := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.mp hz₀).2 _
  have h1 : (p : ℕ) • z₁ ∈ (X.toGradedCartierModuleData j hc).nPiece 1 := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_inf.mp hz₁).2 _
  have hsum : (p : ℕ) • z₀ + (p : ℕ) • z₁ = 0 := by have h := hp; rw [nsmul_add] at h; exact h
  have hpz0 : (p : ℕ) • z₀ = 0 := by
    have hneg : (p : ℕ) • z₀ = -((p : ℕ) • z₁) := eq_neg_of_add_eq_zero_left hsum
    have hmem1 : (p : ℕ) • z₀ ∈ (X.toGradedCartierModuleData j hc).nPiece 1 := by rw [hneg]; exact AddSubgroup.neg_mem _ h1
    have : (p : ℕ) • z₀ ∈ ((X.toGradedCartierModuleData j hc).nPiece 0 ⊓ (X.toGradedCartierModuleData j hc).nPiece 1) :=
      AddSubgroup.mem_inf.mpr ⟨h0, hmem1⟩
    exact (AddSubgroup.mem_bot).mp (hcN.disjoint.le_bot this)
  have hpz1 : (p : ℕ) • z₁ = 0 := by rw [hpz0, zero_add] at hsum; exact hsum
  rw [B28ETF.homog j X γ hγ hc L hL ha hmul0 0 z₀ hz₀ hpz0, B28ETF.homog j X γ hγ hc L hL ha hmul0 1 z₁ hz₁ hpz1, add_zero]

end S_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed (solution)
