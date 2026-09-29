-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/568fdbb9-eb5c-5eaa-910b-622988df3f7c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digits_eq_of_varpi_eq_verschiebung_level_two
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

namespace B29Alg

open TrivSqZeroExt DualNumber

variable {p : ℕ} [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p]

theorem pow_char_eq (δ : DualNumber κ) :
    δ ^ p = algebraMap κ (DualNumber κ) (TrivSqZeroExt.fst δ ^ p) := by
  haveI : CharP (DualNumber κ) p :=
    charP_of_injective_algebraMap (TrivSqZeroExt.inl_injective (R := κ) (M := κ)) p
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq δ]
  rw [add_pow_char, map_pow, TrivSqZeroExt.algebraMap_eq_inl]
  have : (TrivSqZeroExt.inr δ.snd : DualNumber κ) ^ p = 0 :=
    pow_eq_zero_of_le hp (by rw [pow_two, TrivSqZeroExt.inr_mul_inr])
  rw [this, add_zero]

theorem pow_char_sq_eq (δ : DualNumber κ) :
    δ ^ (p ^ 2) = algebraMap κ (DualNumber κ) (TrivSqZeroExt.fst δ ^ (p ^ 2)) := by
  rw [sq, pow_mul, pow_char_eq, TrivSqZeroExt.fst_pow, ← pow_mul]

theorem fst_snd_eq_of_digit_relations
    (a ν : ℕ → Fin 2 → κ) (hν0 : ∀ i, ν 0 i = 0) (i₀ i₁ : Fin 2) (δ₀ δ₁ : DualNumber κ)
    (h1 : δ₀ ^ p * (algebraMap κ (DualNumber κ) (a 1 i₀) + ν 1 i₀ • DualNumber.eps) +
        δ₁ * (algebraMap κ (DualNumber κ) (a 0 i₁) + ν 0 i₁ • DualNumber.eps) = δ₀)
    (h2 : δ₀ ^ (p ^ 2) * (algebraMap κ (DualNumber κ) (a 2 i₀) + ν 2 i₀ • DualNumber.eps) +
        δ₁ ^ p * (algebraMap κ (DualNumber κ) (a 1 i₁) + ν 1 i₁ • DualNumber.eps) = δ₁) :
    a 0 i₁ ^ p * TrivSqZeroExt.fst δ₀ =
        (a 0 i₁ ^ p * a 1 i₀ + a 0 i₁ * a 1 i₁) * TrivSqZeroExt.fst δ₀ ^ p +
        (a 0 i₁ ^ (p + 1) * a 2 i₀ - a 0 i₁ * a 1 i₀ ^ p * a 1 i₁) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) ∧
      a 0 i₁ ^ p * TrivSqZeroExt.snd δ₀ =
        (a 0 i₁ ^ (p + 1) * ν 2 i₀ - a 0 i₁ * a 1 i₀ ^ p * ν 1 i₁) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) +
        (a 0 i₁ ^ p * ν 1 i₀ + a 0 i₁ * ν 1 i₁) * TrivSqZeroExt.fst δ₀ ^ p := by
  rw [pow_char_eq δ₀] at h1
  rw [pow_char_sq_eq δ₀, pow_char_eq δ₁] at h2
  have e1 := congrArg TrivSqZeroExt.fst h1
  have e2 := congrArg TrivSqZeroExt.fst h2
  have e3 := congrArg TrivSqZeroExt.snd h1
  have e4 := congrArg TrivSqZeroExt.snd h2
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, DualNumber.fst_eps, DualNumber.snd_eps,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hν0, mul_zero, add_zero, zero_add,
    mul_one, smul_zero] at e1 e2 e3 e4

  have hf : a 0 i₁ ^ p * TrivSqZeroExt.fst δ₁ ^ p =
      TrivSqZeroExt.fst δ₀ ^ p - a 1 i₀ ^ p * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) := by
    have : a 0 i₁ * TrivSqZeroExt.fst δ₁ = TrivSqZeroExt.fst δ₀ - a 1 i₀ * TrivSqZeroExt.fst δ₀ ^ p := by
      linear_combination e1
    have h := congrArg (· ^ p) this
    simp only [mul_pow, sub_pow_char, ← pow_mul, ← sq] at h
    linear_combination h
  constructor
  · linear_combination (-(a 0 i₁ ^ p)) * e1 + (-(a 0 i₁ ^ (p + 1))) * e2 + (a 0 i₁ * a 1 i₁) * hf
  · linear_combination (-(a 0 i₁ ^ p)) * e3 + (-(a 0 i₁ ^ (p + 1))) * e4 + (a 0 i₁ * ν 1 i₁) * hf

theorem fpr_algebra (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p]
    (A10 A01 A20 A11 N10 N01 N20 N11 : κ) (hN01 : N01 = 0) (δ₀ δ₁ : DualNumber κ)
    (h3 : δ₀ ^ p * (algebraMap κ (DualNumber κ) A10 + N10 • DualNumber.eps) +
        δ₁ * (algebraMap κ (DualNumber κ) A01 + N01 • DualNumber.eps) = δ₀)
    (h4 : δ₀ ^ (p ^ 2) * (algebraMap κ (DualNumber κ) A20 + N20 • DualNumber.eps) +
        δ₁ ^ p * (algebraMap κ (DualNumber κ) A11 + N11 • DualNumber.eps) = δ₁) :
    A01 ^ p * TrivSqZeroExt.fst δ₀ =
        (A01 ^ p * A10 + A01 * A11) * TrivSqZeroExt.fst δ₀ ^ p +
        (A01 ^ (p + 1) * A20 - A01 * A10 ^ p * A11) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) ∧
    A01 ^ p * TrivSqZeroExt.snd δ₀ =
        (A01 ^ (p + 1) * N20 - A01 * A10 ^ p * N11) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) +
        (A01 ^ p * N10 + A01 * N11) * TrivSqZeroExt.fst δ₀ ^ p := by
  subst hN01
  rw [pow_char_eq δ₀] at h3
  rw [pow_char_sq_eq δ₀, pow_char_eq δ₁] at h4
  have e1 := congrArg TrivSqZeroExt.fst h3
  have e2 := congrArg TrivSqZeroExt.fst h4
  have e3 := congrArg TrivSqZeroExt.snd h3
  have e4 := congrArg TrivSqZeroExt.snd h4
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, DualNumber.fst_eps, DualNumber.snd_eps,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_zero, add_zero, zero_add,
    mul_one, smul_zero] at e1 e2 e3 e4
  have hf : A01 ^ p * TrivSqZeroExt.fst δ₁ ^ p =
      TrivSqZeroExt.fst δ₀ ^ p - A10 ^ p * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) := by
    have : A01 * TrivSqZeroExt.fst δ₁ = TrivSqZeroExt.fst δ₀ - A10 * TrivSqZeroExt.fst δ₀ ^ p := by
      linear_combination e1
    have h := congrArg (· ^ p) this
    simp only [mul_pow, sub_pow_char, ← pow_mul, ← sq] at h
    linear_combination h
  constructor
  · linear_combination (-(A01 ^ p)) * e1 + (-(A01 ^ (p + 1))) * e2 + (A01 * A11) * hf
  · linear_combination (-(A01 ^ p)) * e3 + (-(A01 ^ (p + 1))) * e4 + (A01 * N11) * hf

end B29Alg

namespace DigitKit

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData WittVector

section Witt

variable (p : ℕ) [hp : Fact p.Prime]

private theorem frobenius_teichmuller_aux₁ {R : Type} (x : MvPolynomial R ℚ) :
    frobenius (teichmuller p x) = teichmuller p (x ^ p) := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R ℚ)).1
  funext n
  rw [ghostMap_apply, ghostMap_apply, ghostComponent_frobenius, ghostComponent_teichmuller,
    ghostComponent_teichmuller, ← pow_mul, ← pow_succ']

private theorem frobenius_teichmuller_aux₂ {R : Type} (x : MvPolynomial R ℤ) :
    frobenius (teichmuller p x) = teichmuller p (x ^ p) := by
  refine map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  rw [WittVector.IsPoly.map (WittVector.frobenius_isPoly p), map_teichmuller, map_teichmuller, map_pow,
    frobenius_teichmuller_aux₁]

theorem frobenius_teichmuller {S : Type} [CommRing S] (a : S) :
    frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  obtain ⟨x, rfl⟩ := MvPolynomial.counit_surjective S a
  rw [← map_teichmuller, ← WittVector.IsPoly.map (WittVector.frobenius_isPoly p), frobenius_teichmuller_aux₂,
    map_teichmuller, map_pow]

theorem exists_natCast_eq_teichmuller_add_verschiebung {S : Type} [CommRing S] :
    ∃ ε : WittVector p S, ((p : ℕ) : WittVector p S) = teichmuller p (p : S) + verschiebung ε := by
  have h0 : (((p : ℕ) : WittVector p S) - teichmuller p (p : S)).coeff 0 = 0 := by
    have := add_coeff_zero (teichmuller p (p : S)) (((p : ℕ) : WittVector p S) - teichmuller p (p : S))
    rw [add_sub_cancel, teichmuller_coeff_zero, ← constantCoeff_apply, map_natCast] at this
    exact left_eq_add.mp this
  refine ⟨(((p : ℕ) : WittVector p S) - teichmuller p (p : S)).shift 1, ?_⟩
  have := eq_iterate_verschiebung (x := ((p : ℕ) : WittVector p S) - teichmuller p (p : S)) (n := 1)
    (by intro i hi; interval_cases i; exact h0)
  rw [Function.iterate_one] at this
  rw [← this, add_sub_cancel]

end Witt

section Datum

variable {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S}

theorem fin2_add_one_add_one : ∀ i : Fin 2, i + 1 + 1 = i := by decide

theorem fin2_add_one_ne : ∀ i : Fin 2, i + 1 ≠ i := by decide

theorem sum_univ_fin2 {M : Type} [AddCommMonoid M] (l : Fin 2) (f : Fin 2 → M) :
    ∑ i : Fin 2, f i = f l + f (l + 1) := by
  fin_cases l
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two, add_comm]

theorem isCompl_piece_succ (D : GradedCartierModuleData p S jS) (i : Fin 2) :
    IsCompl (D.piece i) (D.piece (i + 1)) := by
  fin_cases i
  · exact D.isCompl_piece
  · exact D.isCompl_piece.symm

theorem exists_piece_decomp (D : GradedCartierModuleData p S jS) (i : Fin 2) (m : D.M) :
    ∃ m₀ m₁ : D.M, m₀ ∈ D.piece i ∧ m₁ ∈ D.piece (i + 1) ∧ m = m₀ + m₁ := by
  have hm : m ∈ D.piece i ⊔ D.piece (i + 1) := by
    rw [(isCompl_piece_succ D i).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨m₀, h₀, m₁, h₁, h⟩ := Submodule.mem_sup.mp hm
  exact ⟨m₀, m₁, h₀, h₁, h.symm⟩

theorem eq_zero_of_mem_piece_of_mem_piece_succ (D : GradedCartierModuleData p S jS) (i : Fin 2) (m : D.M)
    (h₀ : m ∈ D.piece i) (h₁ : m ∈ D.piece (i + 1)) : m = 0 :=
  (Submodule.disjoint_def.mp (isCompl_piece_succ D i).disjoint) m h₀ h₁

theorem exists_eq_teichmuller_smul_add_verschiebung (D : GradedCartierModuleData p S jS) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2) (m : D.M) (hm : m ∈ D.piece l) :
    ∃ (c : S) (y : D.M), y ∈ D.piece (l + 1) ∧ m = teichmuller p c • γ l + D.verschiebung y := by
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 m
  obtain ⟨y₀, y₁, hy₀, hy₁, rfl⟩ := exists_piece_decomp D l y
  simp only at hcy
  rw [sum_univ_fin2 l, map_add] at hcy

  have hA : teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀ ∈ D.piece (l + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 (l + 1))) (D.verschiebung_mem l y₀ hy₀)
  have hB : teichmuller p (c l) • γ l + D.verschiebung y₁ ∈ D.piece l := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 l)) ?_
    have := D.verschiebung_mem (l + 1) y₁ hy₁
    rwa [fin2_add_one_add_one] at this
  have hA' : teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀ ∈ D.piece l := by
    have : teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀ =
        m - (teichmuller p (c l) • γ l + D.verschiebung y₁) := by rw [hcy]; abel
    rw [this]
    exact Submodule.sub_mem _ hm hB
  have hA0 := eq_zero_of_mem_piece_of_mem_piece_succ D l _ hA' hA
  refine ⟨c l, y₁, hy₁, ?_⟩
  calc m = (teichmuller p (c l) • γ l + D.verschiebung y₁) +
        (teichmuller p (c (l + 1)) • γ (l + 1) + D.verschiebung y₀) := by rw [hcy]; abel
    _ = teichmuller p (c l) • γ l + D.verschiebung y₁ := by rw [hA0, add_zero]

theorem teichmuller_smul_add_verschiebung_inj (D : GradedCartierModuleData p S jS) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2) {c c' : S} {y y' : D.M}
    (h : teichmuller p c • γ l + D.verschiebung y = teichmuller p c' • γ l + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 (teichmuller p c • γ l + D.verschiebung y)
  have e : ∀ (c₀ : S) (y₀ : D.M), teichmuller p c₀ • γ l + D.verschiebung y₀ =
      (∑ i : Fin 2, teichmuller p (Function.update (fun _ : Fin 2 => (0 : S)) l c₀ i) • γ i) + D.verschiebung y₀ := by
    intro c₀ y₀
    rw [sum_univ_fin2 l, Function.update_self, Function.update_of_ne (fin2_add_one_ne l)]
    simp [map_zero]
  have h1 := huniq (Function.update (fun _ : Fin 2 => (0 : S)) l c, y) (e c y)
  have h2 := huniq (Function.update (fun _ : Fin 2 => (0 : S)) l c', y') (h.trans (e c' y'))
  have h12 := h1.trans h2.symm
  refine ⟨?_, congrArg Prod.snd h12⟩
  have := congrArg (fun q => q.1 l) h12
  simpa using this

end Datum

section More

variable {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S}

open WittVector

theorem mem_piece_succ_of_verschiebung_mem (D : GradedCartierModuleData p S jS) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2) (y : D.M) (hy : D.verschiebung y ∈ D.piece l) :
    y ∈ D.piece (l + 1) := by
  obtain ⟨y₀, y₁, hy₀, hy₁, rfl⟩ := exists_piece_decomp D (l + 1) y

  rw [fin2_add_one_add_one] at hy₁
  have hV1 : D.verschiebung y₁ ∈ D.piece (l + 1) := D.verschiebung_mem l y₁ hy₁
  have hV0 : D.verschiebung y₀ ∈ D.piece l := by
    have := D.verschiebung_mem (l + 1) y₀ hy₀
    rwa [fin2_add_one_add_one] at this
  have hV1' : D.verschiebung y₁ ∈ D.piece l := by
    have : D.verschiebung y₁ = D.verschiebung (y₀ + y₁) - D.verschiebung y₀ := by rw [map_add]; abel
    rw [this]
    exact Submodule.sub_mem _ hy hV0
  have h0 : D.verschiebung y₁ = 0 := eq_zero_of_mem_piece_of_mem_piece_succ D l _ hV1' hV1
  have hy1 : y₁ = 0 := hγ.verschiebung_injective (by rw [h0, map_zero])
  rw [hy1, add_zero]
  exact hy₀

theorem exists_eq_teichmuller_add_verschiebung' (w : WittVector p S) :
    ∃ w₁ : WittVector p S, w = teichmuller p (w.coeff 0) + verschiebung w₁ := by
  have h0 : (w - teichmuller p (w.coeff 0)).coeff 0 = 0 := by
    have h := add_coeff_zero (teichmuller p (w.coeff 0)) (w - teichmuller p (w.coeff 0))
    rw [add_sub_cancel, teichmuller_coeff_zero] at h
    exact left_eq_add.mp h
  refine ⟨(w - teichmuller p (w.coeff 0)).shift 1, ?_⟩
  have := eq_iterate_verschiebung (x := w - teichmuller p (w.coeff 0)) (n := 1)
    (by intro i hi; interval_cases i; exact h0)
  rw [Function.iterate_one] at this
  rw [← this, add_sub_cancel]

theorem eq_verschiebung_shift_of_coeff_zero (w : WittVector p S) (h : w.coeff 0 = 0) :
    w = verschiebung (w.shift 1) ∧ (w.shift 1).coeff 0 = w.coeff 1 := by
  refine ⟨?_, by rw [shift_coeff, add_zero]⟩
  have := eq_iterate_verschiebung (x := w) (n := 1) (by intro i hi; interval_cases i; exact h)
  rwa [Function.iterate_one] at this

theorem smul_teichmuller_smul_add_verschiebung (D : GradedCartierModuleData p S jS) (w w₁ : WittVector p S)
    (hw : w = teichmuller p (w.coeff 0) + verschiebung w₁) (k : S) (g y : D.M) :
    w • (teichmuller p k • g + D.verschiebung y) =
      teichmuller p (w.coeff 0 * k) • g +
        D.verschiebung (WittVector.frobenius (teichmuller p (w.coeff 0)) • y +
          w₁ • D.frobenius (teichmuller p k • g + D.verschiebung y)) := by
  conv_lhs => rw [hw]
  rw [add_smul, ← D.verschiebung_smul_frobenius, smul_add, smul_smul, ← map_mul, D.smul_verschiebung, map_add, map_add]
  abel

theorem coeff_one_teichmuller_add_mem_span (α β : S) :
    (teichmuller p α + teichmuller p β - teichmuller p (α + β)).coeff 1 ∈ Ideal.span {α} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← WittVector.map_coeff (Ideal.Quotient.mk (Ideal.span {α}))]
  have hα : Ideal.Quotient.mk (Ideal.span {α}) α = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self α)
  rw [map_sub, map_add, map_teichmuller, map_teichmuller, map_teichmuller, map_add, hα, teichmuller_zero, zero_add, zero_add,
    sub_self, WittVector.zero_coeff]

end More

end DigitKit

theorem FPR.verschiebung_one_eq_natCast (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] :
    (WittVector.verschiebung (1 : WittVector p R)) = (p : WittVector p R) := by
  ext n
  cases n with
  | zero => rw [WittVector.verschiebung_coeff_zero, WittVector.coeff_p_zero]
  | succ n =>
    rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_p]
    cases n with
    | zero => simp
    | succ n => simp [WittVector.one_coeff_eq_of_pos]

theorem FPR.piIndex_facts (i₀ : Fin 2) :
    i₀ + 1 = FormalODModule.piIndex 0 i₀ ∧ FormalODModule.piIndex 1 i₀ = i₀ ∧
      FormalODModule.piIndex 2 i₀ = FormalODModule.piIndex 0 i₀ ∧
      FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i₀) = i₀ ∧
      FormalODModule.piIndex 1 (FormalODModule.piIndex 0 i₀) = FormalODModule.piIndex 0 i₀ := by
  fin_cases i₀ <;> decide

theorem FPR.digit_eq_zero_of_eq_verschiebung {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) (l : Fin 2)
    {c : B} {y s : D.M} (h : WittVector.teichmuller p c • γ l + D.verschiebung y = D.verschiebung s) : c = 0 := by
  have h' : WittVector.teichmuller p c • γ l + D.verschiebung y = WittVector.teichmuller p (0 : B) • γ l + D.verschiebung s := by
    rw [h, WittVector.teichmuller_zero, zero_smul, zero_add]
  exact (DigitKit.teichmuller_smul_add_verschiebung_inj D hγ l h').1

theorem FPR.tsmul {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (a : B) (f : (X.toGradedCartierModuleData j hc).M) :
    WittVector.teichmuller p a • f = homothety a (f : CartierModule p X.F) :=
  teichmuller_smul a f

set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (a ν : ℕ → Fin 2 → κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + ν m i • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i₀ : ℕ))
    (hinv : endAct X.varpiEnd m = verschiebungInt m) :
    ∃ (δ₀ δ₁ : DualNumber κ) (t : CartierModule p X.F),
      m = homothety δ₀ (γ i₀) + verschiebungInt (homothety δ₁ (γ (FormalODModule.piIndex 0 i₀)) + verschiebungInt t) ∧
      (tangent m = fun k => δ₀ * tangent (γ i₀) k) ∧
      δ₀ ^ p * (algebraMap κ (DualNumber κ) (a 1 i₀) + ν 1 i₀ • DualNumber.eps) +
        δ₁ * (algebraMap κ (DualNumber κ) (a 0 (FormalODModule.piIndex 0 i₀)) + ν 0 (FormalODModule.piIndex 0 i₀) • DualNumber.eps) = δ₀ ∧
      δ₀ ^ (p ^ 2) * (algebraMap κ (DualNumber κ) (a 2 i₀) + ν 2 i₀ • DualNumber.eps) +
        δ₁ ^ p * (algebraMap κ (DualNumber κ) (a 1 (FormalODModule.piIndex 0 i₀)) + ν 1 (FormalODModule.piIndex 0 i₀) • DualNumber.eps) = δ₁ ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.fst δ₀ =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * a 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ p +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * a 2 i₀ - a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.snd δ₀ =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * ν 2 i₀ - a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ (p ^ 2) +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * ν 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst δ₀ ^ p := by
  classical

  haveI hcharP : CharP (DualNumber κ) p :=
    charP_of_injective_algebraMap (TrivSqZeroExt.inl_injective (R := κ) (M := κ)) p
  have hp0 : ((p : ℕ) : DualNumber κ) = 0 := CharP.cast_eq_zero (DualNumber κ) p
  have hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j ⟨1, by rw [pow_one, hp0]⟩ X
  have hγD : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j X γ hγ hc).1
  obtain ⟨hi1, hp1i, hp2i, hp0i', hp1i'⟩ := FPR.piIndex_facts i₀
  set i₁ := FormalODModule.piIndex 0 i₀ with hi₁def
  set A : ℕ → Fin 2 → DualNumber κ := fun m i => algebraMap κ (DualNumber κ) (a m i) + ν m i • DualNumber.eps with hAdef
  have hA00 : A 0 i₀ = 0 := by
    simp only [hAdef, ha0, hν0, map_zero, zero_smul, add_zero]

  obtain ⟨h3, hh3⟩ := hA i₀ 3
  obtain ⟨h2, hh2⟩ := hA i₁ 2
  set xi : CartierModule p X.F := WittVector.teichmuller p (A 1 i₀) • γ i₀ +
    verschiebungInt (WittVector.teichmuller p (A 2 i₀) • γ i₁ + verschiebungInt h3) with hxi
  set xnext : CartierModule p X.F := WittVector.teichmuller p (A 1 i₁) • γ i₁ + verschiebungInt h2 with hxnext
  have hz0 : homothety (A 0 i₀) (γ (FormalODModule.piIndex 0 i₀)) = 0 := by
    rw [hA00, ← teichmuller_smul, WittVector.teichmuller_zero]; exact zero_smul (WittVector p (DualNumber κ)) (γ (FormalODModule.piIndex 0 i₀))
  have hcrit : endAct X.varpiEnd (γ i₀) = verschiebungInt xi := by
    rw [hh3, Fin.sum_univ_three, hxi]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Function.iterate_zero, Function.iterate_one,
      Function.iterate_succ, Function.comp_apply, id_eq, map_add]
    rw [hz0, hp1i, hp2i, ← teichmuller_smul, ← teichmuller_smul, zero_add]
    abel
  have hnext : endAct X.varpiEnd (γ (i₀ + 1)) = WittVector.teichmuller p (A 0 i₁) • γ i₀ + verschiebungInt xnext := by
    rw [hi1, hh2, Fin.sum_univ_two, hxnext]
    simp only [Fin.val_zero, Fin.val_one, Function.iterate_zero, Function.iterate_one,
      Function.iterate_succ, Function.comp_apply, id_eq, map_add]
    rw [hp0i', hp1i', ← teichmuller_smul, ← teichmuller_smul]
    abel
  have hcritD : (X.toGradedCartierModuleData j hc).varpi (γ i₀) = (X.toGradedCartierModuleData j hc).verschiebung xi := hcrit

  have hmD : m ∈ (X.toGradedCartierModuleData j hc).piece i₀ := hm
  have hinvD : (X.toGradedCartierModuleData j hc).varpi m = (X.toGradedCartierModuleData j hc).verschiebung m := hinv
  obtain ⟨c, d, e, h, g, k, m₂, x', x'', xn', fr', ω, hmE, hxiE, hx'E, hxnE, hFE, hω, hω0, hL1, hL2⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_digits_eq_of_varpi_eq_verschiebung_level_two
      p j (X.toGradedCartierModuleData j hc) γ hγD i₀ xi xnext (A 0 i₁) hcritD hnext m hmD hinvD

  obtain ⟨he, hx'⟩ := DigitKit.teichmuller_smul_add_verschiebung_inj (X.toGradedCartierModuleData j hc) hγD i₀
    (c := e) (c' := A 1 i₀) (y := x') (y' := WittVector.teichmuller p (A 2 i₀) • γ i₁ + verschiebungInt h3)
    (hxiE.symm.trans hxi)
  obtain ⟨hh, -⟩ := DigitKit.teichmuller_smul_add_verschiebung_inj (X.toGradedCartierModuleData j hc) hγD (i₀ + 1)
    (c := h) (c' := A 2 i₀) (y := x'') (y' := h3) (by rw [← hx'E, hx', hi1]; rfl)
  obtain ⟨hg, -⟩ := DigitKit.teichmuller_smul_add_verschiebung_inj (X.toGradedCartierModuleData j hc) hγD (i₀ + 1)
    (c := g) (c' := A 1 i₁) (y := xn') (y' := h2) (by rw [← hxnE, hxnext, hi1]; rfl)

  have hFγ : (X.toGradedCartierModuleData j hc).frobenius (γ i₀) = (X.toGradedCartierModuleData j hc).varpi xi := hγD.verschiebung_injective (by
    rw [(X.toGradedCartierModuleData j hc).verschiebung_frobenius, FPR.verschiebung_one_eq_natCast, Nat.cast_smul_eq_nsmul,
      ← (X.toGradedCartierModuleData j hc).varpi_varpi, hcritD, (X.toGradedCartierModuleData j hc).varpi_verschiebung])
  rw [hxiE, map_add, map_smul, hcritD, (X.toGradedCartierModuleData j hc).varpi_verschiebung, (X.toGradedCartierModuleData j hc).smul_verschiebung, ← map_add] at hFγ
  have hk : k = 0 := FPR.digit_eq_zero_of_eq_verschiebung (X.toGradedCartierModuleData j hc) hγD (i₀ + 1) (hFE.symm.trans hFγ)
  rw [hk, mul_zero, add_zero] at hL2

  have h3' : c ^ p * A 1 i₀ + d * A 0 i₁ = c := by rw [he] at hL1; linear_combination (-1 : DualNumber κ) * hL1
  have h4' : c ^ (p ^ 2) * A 2 i₀ + d ^ p * A 1 i₁ = d := by
    rw [hg, hh] at hL2; rw [sq, pow_mul]; linear_combination (-1 : DualNumber κ) * hL2
  refine ⟨c, d, m₂, ?_, ?_, h3', h4', ?_⟩
  · rw [hmE, hi1, FPR.tsmul, FPR.tsmul]
    rfl
  · rw [hmE]
    show tangent (WittVector.teichmuller p c • γ i₀ +
      (verschiebungInt (WittVector.teichmuller p d • γ (i₀ + 1) + verschiebungInt m₂))) = _
    rw [map_add, teichmuller_smul, tangent_homothety, tangent_verschiebungInt, add_zero]
    funext k'
    rfl
  · exact B29Alg.fpr_algebra p (a 1 i₀) (a 0 i₁) (a 2 i₀) (a 1 i₁) (ν 1 i₀) (ν 0 i₁) (ν 2 i₀) (ν 1 i₁) (hν0 _) c d h3' h4'

end S_CerednikDrinfeld_FormalODModule_exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber (solution)
