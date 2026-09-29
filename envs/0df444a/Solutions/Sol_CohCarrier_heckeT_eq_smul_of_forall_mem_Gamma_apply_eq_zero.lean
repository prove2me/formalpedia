-- Prove2me | solution 1 for CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b6e36450-6ca8-5df5-8dbb-c4396d373088

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_iDeg_interchange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace CohCarrier
p2m_export "CohCarrier" "Gamma0Upper mem_Gamma0Upper GammaH GammaH_le_Gamma0 GammaH_top H1 conjUpperMat GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjLowerMat LevelLE iotaDeg iDeg' uMat uMat_apply_00 uMat_apply_01 uMat_apply_11 uElt coe_uElt coe_iotaDeg_one heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd iDeg_heckeT_comm_of_coprime heckeT_iDeg_interchange"
namespace CongruenceEisAll
p2m_open "CohCarrier"

section Naturality

open Subgroup Subgroup.leftTransversals

theorem transfer_comp {G : Type*} [Group G] {K : Subgroup G} [K.FiniteIndex] {C C' : Type*}
    [CommGroup C] [CommGroup C'] (g : C →* C') (θ : K →* C) :
    MonoidHom.transfer (g.comp θ) = g.comp (MonoidHom.transfer θ) := by
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default]
  simp only [diff, MonoidHom.coe_comp, Function.comp_apply, map_prod]

theorem heckeT_comp_coeff (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (φ : H1 M H A) :
    heckeT M H ℓ B (f.comp φ) = f.comp (heckeT M H ℓ A φ) := by
  have hθ : (AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL M H ℓ)
      = (AddMonoidHom.toMultiplicative f).comp
          ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)) := by
    ext; rfl
  change MonoidHom.toAdditiveLeft (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL M H ℓ)))
    = f.comp (MonoidHom.toAdditiveLeft (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ))))
  rw [hθ, transfer_comp]
  ext; rfl

theorem diff_eq_prod_ext {G : Type*} [Group G] {K : Subgroup G} [K.FiniteIndex] {C : Type*}
    [CommGroup C] (θ : K →* C) (E : G → C) (hE : ∀ (g : G) (hg : g ∈ K), E g = θ ⟨g, hg⟩)
    (S T : K.LeftTransversal) :
    diff θ S T = ∏ q : G ⧸ K,
      E ((S.2.leftQuotientEquiv q : G)⁻¹ * (T.2.leftQuotientEquiv q : G)) := by
  simp only [diff]
  exact Finset.prod_congr rfl fun q _ => (hE _ _).symm

end Naturality

section MapN

abbrev mapN (n : ℕ) : SL(2, ℤ) →* SL(2, ZMod n) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))

theorem mapN_apply (n : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapN n g) i j = ((g i j : ℤ) : ZMod n) := rfl

theorem mapN_eq_iff (n : ℕ) (g g' : SL(2, ℤ)) :
    mapN n g = mapN n g' ↔ ∀ i j, (n : ℤ) ∣ g' i j - g i j := by
  constructor
  · intro h i j
    have hij : (mapN n g) i j = (mapN n g') i j := by rw [h]
    rw [mapN_apply, mapN_apply] at hij
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hij
  · intro h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [mapN_apply, mapN_apply]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i j)

theorem mapN_eq_of_dvd {m n : ℕ} (hmn : m ∣ n) {g g' : SL(2, ℤ)} (h : mapN n g = mapN n g') :
    mapN m g = mapN m g' := by
  rw [mapN_eq_iff] at h ⊢
  exact fun i j => dvd_trans (Int.natCast_dvd_natCast.mpr hmn) (h i j)

theorem mapN_mul_eq {P M₁ : ℕ} (hcop : Nat.Coprime P M₁) {g g' : SL(2, ℤ)}
    (hP : mapN P g = mapN P g') (hM : mapN M₁ g = mapN M₁ g') :
    mapN (P * M₁) g = mapN (P * M₁) g' := by
  rw [mapN_eq_iff] at hP hM ⊢
  intro i j
  push_cast
  exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr hcop) (hP i j) (hM i j)

theorem mapN_eq_one_iff (n : ℕ) (g : SL(2, ℤ)) : mapN n g = 1 ↔ g ∈ Gamma n :=
  (Gamma_mem'.symm)

end MapN

section CRT

variable {N : ℕ} {P M₁ : ℕ} [NeZero P] [NeZero M₁]

theorem exists_crt (hcop : Nat.Coprime P M₁) (g : SL(2, ℤ)) :
    ∃ g₁ : SL(2, ℤ), mapN P g₁ = mapN P g ∧ mapN M₁ g₁ = 1 := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (P : ℤ) (M₁ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  haveI : NeZero (P * M₁) := ⟨mul_ne_zero (NeZero.ne P) (NeZero.ne M₁)⟩
  set n : ℕ := P * M₁ with hn
  set e : ℤ := y * M₁ with he
  set f : ℤ := x * P with hf
  have hef : e + f = 1 := by rw [he, hf]; linear_combination hxy
  have hef' : (n : ℤ) ∣ e * f := ⟨x * y, by rw [hn, he, hf]; push_cast; ring⟩
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h

  have hE : ((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hef
  have hEF : ((e : ℤ) : ZMod n) * ((f : ℤ) : ZMod n) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hef'
  have hD : ((g 0 0 : ℤ) : ZMod n) * ((g 1 1 : ℤ) : ZMod n)
      - ((g 0 1 : ℤ) : ZMod n) * ((g 1 0 : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hdet
  let Y : SL(2, ZMod n) :=
    ⟨!![((e * g 0 0 + f : ℤ) : ZMod n), ((e * g 0 1 : ℤ) : ZMod n);
        ((e * g 1 0 : ℤ) : ZMod n), ((e * g 1 1 + f : ℤ) : ZMod n)], by
      rw [Matrix.det_fin_two_of]
      push_cast
      linear_combination ((e : ℤ) : ZMod n) ^ 2 * hD
        + (((g 0 0 : ℤ) : ZMod n) + ((g 1 1 : ℤ) : ZMod n) - 2) * hEF
        + (((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) + 1) * hE⟩
  obtain ⟨g₁, hg₁⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod n Y
  have hent : ∀ i j : Fin 2, (mapN n g₁) i j = Y i j := fun i j => by rw [← hg₁]
  have h00 : (n : ℤ) ∣ (e * g 0 0 + f) - g₁ 0 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [mapN_apply, Y] using hent 0 0)
  have h01 : (n : ℤ) ∣ (e * g 0 1) - g₁ 0 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [mapN_apply, Y] using hent 0 1)
  have h10 : (n : ℤ) ∣ (e * g 1 0) - g₁ 1 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [mapN_apply, Y] using hent 1 0)
  have h11 : (n : ℤ) ∣ (e * g 1 1 + f) - g₁ 1 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [mapN_apply, Y] using hent 1 1)
  have hPn : (P : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_right _ _
  have hMn : (M₁ : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_left _ _
  have hPe : (P : ℤ) ∣ e - 1 := ⟨-x, by rw [he]; linear_combination hxy⟩
  have hPf : (P : ℤ) ∣ f := ⟨x, by rw [hf]; ring⟩
  have hMe : (M₁ : ℤ) ∣ e := ⟨y, by rw [he]; ring⟩
  have hMf : (M₁ : ℤ) ∣ f - 1 := ⟨-y, by rw [hf]; linear_combination hxy⟩
  refine ⟨g₁, ?_, ?_⟩
  · rw [mapN_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (P : ℤ) ∣ g 0 0 - g₁ 0 0
      have : g 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - (e - 1) * g 0 0 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h00) (dvd_mul_of_dvd_left hPe _)) hPf
    · show (P : ℤ) ∣ g 0 1 - g₁ 0 1
      have : g 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - (e - 1) * g 0 1 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h01) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 0 - g₁ 1 0
      have : g 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - (e - 1) * g 1 0 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h10) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 1 - g₁ 1 1
      have : g 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - (e - 1) * g 1 1 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h11) (dvd_mul_of_dvd_left hPe _)) hPf
  · rw [← map_one (mapN M₁), mapN_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 0 - g₁ 0 0
      have : (1 : SL(2, ℤ)) 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - e * g 0 0 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h00) (dvd_mul_of_dvd_left hMe _)) hMf
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 1 - g₁ 0 1
      have : (1 : SL(2, ℤ)) 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - e * g 0 1 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h01) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 0 - g₁ 1 0
      have : (1 : SL(2, ℤ)) 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - e * g 1 0 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h10) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 1 - g₁ 1 1
      have : (1 : SL(2, ℤ)) 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - e * g 1 1 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h11) (dvd_mul_of_dvd_left hMe _)) hMf

noncomputable def crtLift (hcop : Nat.Coprime P M₁) (hNM₁ : N ∣ M₁) (g : SL(2, ℤ)) :
    ↥(GammaH N ⊤) :=
  ⟨Classical.choose (exists_crt hcop g), by
    rw [GammaH_top, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := (Classical.choose_spec (exists_crt hcop g)).2
    have h10 := ((mapN_eq_iff M₁ _ _).mp (h.trans (map_one (mapN M₁)).symm)) 1 0
    simp only [Matrix.SpecialLinearGroup.coe_one, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, zero_sub, dvd_neg] at h10
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hNM₁) h10⟩

theorem mapN_crtLift_P (hcop : Nat.Coprime P M₁) (hNM₁ : N ∣ M₁) (g : SL(2, ℤ)) :
    mapN P ((crtLift hcop hNM₁ g : ↥(GammaH N ⊤)) : SL(2, ℤ)) = mapN P g :=
  (Classical.choose_spec (exists_crt hcop g)).1

theorem mapN_crtLift_M₁ (hcop : Nat.Coprime P M₁) (hNM₁ : N ∣ M₁) (g : SL(2, ℤ)) :
    mapN M₁ ((crtLift hcop hNM₁ g : ↥(GammaH N ⊤)) : SL(2, ℤ)) = 1 :=
  (Classical.choose_spec (exists_crt hcop g)).2

end CRT

section Char

variable {N : ℕ} {A : Type*} [AddCommGroup A]

def Vanish (M : ℕ) (φ : H1 N ⊤ A) : Prop :=
  ∀ γ : ↥(GammaH N ⊤), (γ : SL(2, ℤ)) ∈ Gamma M → φ (Additive.ofMul γ) = 0

theorem apply_mul (φ : H1 N ⊤ A) (g h : ↥(GammaH N ⊤)) :
    φ (Additive.ofMul (g * h)) = φ (Additive.ofMul g) + φ (Additive.ofMul h) := by
  rw [ofMul_mul, map_add]

theorem apply_inv (φ : H1 N ⊤ A) (g : ↥(GammaH N ⊤)) :
    φ (Additive.ofMul g⁻¹) = - φ (Additive.ofMul g) := by
  rw [ofMul_inv, map_neg]

theorem eq_of_mapN_eq {M : ℕ} (φ : H1 N ⊤ A) (hφ : Vanish M φ) {g₁ g₂ : ↥(GammaH N ⊤)}
    (h : mapN M (g₁ : SL(2, ℤ)) = mapN M (g₂ : SL(2, ℤ))) :
    φ (Additive.ofMul g₁) = φ (Additive.ofMul g₂) := by
  have hmem : ((g₁ * g₂⁻¹ : ↥(GammaH N ⊤)) : SL(2, ℤ)) ∈ Gamma M := by
    rw [← mapN_eq_one_iff, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, mul_inv_cancel]
  have h0 := hφ _ hmem
  rw [apply_mul, apply_inv, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0

theorem Vanish.of_dvd {M M' : ℕ} {φ : H1 N ⊤ A} (hφ : Vanish M φ) (h : M ∣ M') : Vanish M' φ := by
  intro γ hγ
  apply hφ
  rw [← mapN_eq_one_iff] at hγ ⊢
  rw [← map_one (mapN M)]
  exact mapN_eq_of_dvd h (hγ.trans (map_one _).symm)

variable {P M₁ : ℕ} [NeZero P] [NeZero M₁]

theorem eq_of_mapN_eq₂ (hcop : Nat.Coprime P M₁) (φ : H1 N ⊤ A) (hφ : Vanish (P * M₁) φ)
    {γ γ' : ↥(GammaH N ⊤)}
    (hP : mapN P (γ : SL(2, ℤ)) = mapN P (γ' : SL(2, ℤ)))
    (hM : mapN M₁ (γ : SL(2, ℤ)) = mapN M₁ (γ' : SL(2, ℤ))) :
    φ (Additive.ofMul γ) = φ (Additive.ofMul γ') :=
  eq_of_mapN_eq φ hφ (mapN_mul_eq hcop hP hM)

noncomputable def bigPhi (hcop : Nat.Coprime P M₁) (hNM₁ : N ∣ M₁) (φ : H1 N ⊤ A)
    (hφ : Vanish (P * M₁) φ) : H1 1 ⊤ A where
  toFun x := φ (Additive.ofMul (crtLift hcop hNM₁ ((Additive.toMul x : ↥(GammaH 1 ⊤)) : SL(2, ℤ))))
  map_zero' := by
    rw [toMul_zero, Subgroup.coe_one, ← map_zero φ, ← ofMul_one]
    apply eq_of_mapN_eq₂ hcop φ hφ
    · rw [mapN_crtLift_P, Subgroup.coe_one]
    · rw [mapN_crtLift_M₁, Subgroup.coe_one, map_one]
  map_add' x y := by
    rw [toMul_add, Subgroup.coe_mul, ← apply_mul]
    apply eq_of_mapN_eq₂ hcop φ hφ
    · rw [mapN_crtLift_P, Subgroup.coe_mul, map_mul, map_mul, mapN_crtLift_P, mapN_crtLift_P]
    · rw [mapN_crtLift_M₁, Subgroup.coe_mul, map_mul, mapN_crtLift_M₁, mapN_crtLift_M₁, mul_one]

theorem bigPhi_apply (hcop : Nat.Coprime P M₁) (hNM₁ : N ∣ M₁) (φ : H1 N ⊤ A)
    (hφ : Vanish (P * M₁) φ) (g : ↥(GammaH 1 ⊤)) :
    bigPhi hcop hNM₁ φ hφ (Additive.ofMul g)
      = φ (Additive.ofMul (crtLift hcop hNM₁ (g : SL(2, ℤ)))) := rfl

theorem levelLE_one (N : ℕ) : LevelLE 1 N ⊤ ⊤ 1 :=
  ⟨one_dvd N, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

noncomputable abbrev res (N : ℕ) (A : Type*) [AddCommGroup A] : H1 1 ⊤ A →+ H1 N ⊤ A :=
  iDeg' 1 N ⊤ ⊤ 1 A (levelLE_one N)

theorem res_apply (Ψ : H1 1 ⊤ A) (γ : ↥(GammaH N ⊤)) :
    res N A Ψ (Additive.ofMul γ) = Ψ (Additive.ofMul (iotaDeg 1 N ⊤ ⊤ 1 (levelLE_one N) γ)) := rfl

theorem vanish_sub_res (hcop : Nat.Coprime P M₁) (hNM₁ : N ∣ M₁) (φ : H1 N ⊤ A)
    (hφ : Vanish (P * M₁) φ) : Vanish M₁ (φ - res N A (bigPhi hcop hNM₁ φ hφ)) := by
  intro γ hγ
  rw [AddMonoidHom.sub_apply, res_apply, bigPhi_apply, sub_eq_zero]
  apply eq_of_mapN_eq₂ hcop φ hφ
  · rw [mapN_crtLift_P, coe_iotaDeg_one]
  · rw [mapN_crtLift_M₁]
    exact (mapN_eq_one_iff M₁ _).mpr hγ

end Char

section Unipotent

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem uElt_mul (s t : ℤ) : uElt M H s * uElt M H t = uElt M H (s + t) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Subgroup.coe_mul, coe_uElt, coe_uElt, coe_uElt]
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uElt_zero : uElt M H 0 = 1 := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_uElt, Subgroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uElt_inv (t : ℤ) : (uElt M H t)⁻¹ = uElt M H (-t) := by
  rw [inv_eq_iff_mul_eq_one, uElt_mul, add_neg_cancel, uElt_zero]

theorem uElt_pow (t : ℤ) (n : ℕ) : uElt M H t ^ n = uElt M H (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uElt_zero]
  | succ n ih =>
    rw [pow_succ, ih, uElt_mul]
    congr 1
    push_cast
    ring

variable {M H} (ℓ : ℕ)

def lab (g : ↥(GammaH M H)) : ZMod ℓ :=
  (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) * (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ)

variable {ℓ}

theorem c_eq_zero (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) : (((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod ℓ) = 0 := by
  have hg0 : (g : SL(2, ℤ)) ∈ Gamma0 M := GammaH_le_Gamma0 H g.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓM) hg0

theorem ad_eq_one (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) :
    (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (Int.cast : ℤ → ZMod ℓ) hdet
  push_cast at h
  linear_combination h + (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) * c_eq_zero hℓM g

theorem inv_mul_apply_01 (x y : SL(2, ℤ)) :
    (x⁻¹ * y : SL(2, ℤ)) 0 1 = x 1 1 * y 0 1 - x 0 1 * y 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem mk_eq_mk_uElt_iff (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) (t : ℤ) :
    (QuotientGroup.mk g : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ) = QuotientGroup.mk (uElt M H t)
      ↔ ((t : ℤ) : ZMod ℓ) = lab ℓ g := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_Gamma0Upper, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_uElt, inv_mul_apply_01]
  simp only [uMat_apply_01, uMat_apply_11, mul_one]
  push_cast
  have had := ad_eq_one hℓM g
  unfold lab
  constructor
  · intro h
    linear_combination (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) * h - ((t : ℤ) : ZMod ℓ) * had
  · intro h
    linear_combination (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) * h
      + (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) * had

variable [NeZero ℓ]

theorem mk_eq_mk_uElt_lab (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) :
    (QuotientGroup.mk g : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ)
      = QuotientGroup.mk (uElt M H ((lab ℓ g).val : ℤ)) :=
  (mk_eq_mk_uElt_iff hℓM g _).mpr (by rw [Int.cast_natCast, ZMod.natCast_zmod_val])

theorem lab_eq_of_mk_eq (hℓM : ℓ ∣ M) {g g' : ↥(GammaH M H)}
    (h : (QuotientGroup.mk g : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ) = QuotientGroup.mk g') :
    lab ℓ g = lab ℓ g' := by
  have h1 := mk_eq_mk_uElt_lab hℓM g
  rw [h, mk_eq_mk_uElt_iff hℓM, Int.cast_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

theorem lab_uElt (t : ℤ) : lab ℓ (uElt M H t) = ((t : ℤ) : ZMod ℓ) := by
  simp [lab]

theorem lab_Tinv_mul (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) :
    lab ℓ ((uElt M H 1)⁻¹ * g) = lab ℓ g - 1 := by
  have had := ad_eq_one hℓM g
  have hc := c_eq_zero hℓM g
  rw [uElt_inv]
  simp only [lab, Subgroup.coe_mul, coe_uElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, uMat_apply_00, uMat_apply_01, one_mul]
  push_cast
  linear_combination (-1 : ZMod ℓ) * had
    + ((((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) - (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)) * hc

noncomputable def sec (q : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ) : ↥(GammaH M H) :=
  uElt M H ((lab ℓ q.out).val : ℤ)

theorem sec_spec (hℓM : ℓ ∣ M) (q : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ) :
    (QuotientGroup.mk (sec q) : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ) = q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  exact (mk_eq_mk_uElt_lab hℓM q.out).symm

theorem sec_mk (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) :
    sec (ℓ := ℓ) (QuotientGroup.mk g) = uElt M H ((lab ℓ g).val : ℤ) := by
  unfold sec
  rw [lab_eq_of_mk_eq hℓM
    (QuotientGroup.out_eq' (QuotientGroup.mk g : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ))]

theorem uElt_natCast_mem (n : ℕ) (hn : ℓ ∣ n) : uElt M H (n : ℤ) ∈ GammaHUpper M H ℓ := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, coe_uElt, uMat_apply_01, Int.cast_natCast,
    (ZMod.natCast_eq_zero_iff _ _).mpr hn]

theorem conjL_uElt_ell (h : uElt M H (ℓ : ℤ) ∈ GammaHUpper M H ℓ) :
    conjL M H ℓ ⟨uElt M H (ℓ : ℤ), h⟩ = uElt M H 1 := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  apply Subtype.ext
  change conjUpperMat ℓ (uMat (ℓ : ℤ)) (dvd_of_mem_GammaHUpper M H ℓ ⟨uElt M H (ℓ : ℤ), h⟩) = uMat 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [conjUpperMat, uMat, Int.ediv_self hℓ0]

theorem heckeT_apply_uElt_one [Fact (1 < ℓ)] (hℓM : ℓ ∣ M) {V : Type*} [AddCommGroup V]
    (F : H1 M H V) :
    heckeT M H ℓ V F (Additive.ofMul (uElt M H 1)) = F (Additive.ofMul (uElt M H 1)) := by
  classical
  set T₁ : ↥(GammaH M H) := uElt M H 1 with hT₁
  let θ : ↥(GammaHUpper M H ℓ) →* Multiplicative V :=
    (AddMonoidHom.toMultiplicativeRight F).comp (conjL M H ℓ)
  let E : ↥(GammaH M H) → Multiplicative V := fun x =>
    if hx : (x : SL(2, ℤ)) ∈ Gamma0Upper ℓ then θ ⟨x, Subgroup.mem_subgroupOf.mpr hx⟩ else 1
  have hE : ∀ (x : ↥(GammaH M H)) (hx : x ∈ GammaHUpper M H ℓ), E x = θ ⟨x, hx⟩ := fun x hx => by
    simp only [E, dif_pos (Subgroup.mem_subgroupOf.mp hx)]
  have hE1 : E 1 = 1 := by rw [hE 1 (one_mem _)]; exact map_one θ
  let S : (GammaHUpper M H ℓ).LeftTransversal :=
    ⟨Set.range (sec (M := M) (H := H) (ℓ := ℓ)), Subgroup.isComplement_range_left (sec_spec hℓM)⟩
  have h1 : heckeT M H ℓ V F (Additive.ofMul T₁) = (MonoidHom.transfer θ T₁).toAdd := rfl
  rw [h1, MonoidHom.transfer_def θ S T₁, diff_eq_prod_ext θ E hE]
  have hα : ∀ q, (S.2.leftQuotientEquiv q : ↥(GammaH M H)) = sec q := fun q =>
    Subgroup.IsComplement.leftQuotientEquiv_apply (sec_spec hℓM) q
  have hβ : ∀ q, ((T₁ • S).2.leftQuotientEquiv q : ↥(GammaH M H)) = T₁ * sec (T₁⁻¹ • q) :=
    fun q => by rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hα, smul_eq_mul]
  simp_rw [hα, hβ]

  have hterm : ∀ g : ↥(GammaH M H),
      (sec (QuotientGroup.mk g))⁻¹ * (T₁ * sec (T₁⁻¹ • (QuotientGroup.mk g : _ ⧸ GammaHUpper M H ℓ)))
        = uElt M H (-((lab ℓ g).val : ℤ) + (1 + ((lab ℓ g - 1).val : ℤ))) := fun g => by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, sec_mk hℓM, sec_mk hℓM, lab_Tinv_mul hℓM, hT₁,
      uElt_inv, uElt_mul, uElt_mul]
  have hval1 : (1 : ZMod ℓ).val = 1 := ZMod.val_one ℓ
  rw [Fintype.prod_eq_single (QuotientGroup.mk (uElt M H 0) : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ)]
  ·
    rw [hterm, lab_uElt, Int.cast_zero, ZMod.val_zero, zero_sub, ZMod.neg_val, if_neg one_ne_zero,
      hval1]
    have hℓ1 : 1 ≤ ℓ := NeZero.one_le
    have e : (-((0 : ℕ) : ℤ) + (1 + ((ℓ - 1 : ℕ) : ℤ))) = (ℓ : ℤ) := by push_cast [hℓ1]; ring
    rw [e, hE _ (uElt_natCast_mem ℓ dvd_rfl)]
    change (Multiplicative.ofAdd (F (Additive.ofMul (conjL M H ℓ ⟨uElt M H (ℓ : ℤ), _⟩)))).toAdd = _
    rw [conjL_uElt_ell, toAdd_ofAdd]
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hj : lab ℓ g ≠ 0 := by
        intro h0
        apply hq
        rw [mk_eq_mk_uElt_iff hℓM, Int.cast_zero, h0]
      have hjv : 1 ≤ (lab ℓ g).val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero _).mpr hj)
      rw [hterm, ZMod.val_sub (by rw [hval1]; exact hjv), hval1]
      have e : (-(((lab ℓ g).val : ℕ) : ℤ) + (1 + (((lab ℓ g).val - 1 : ℕ) : ℤ))) = 0 := by
        push_cast [hjv]; ring
      rw [e, uElt_zero, hE1]

end Unipotent

section LevelOne

theorem mem_GammaH_one (g : SL(2, ℤ)) : g ∈ GammaH 1 ⊤ := by
  rw [GammaH_top, Gamma0_mem]
  exact Subsingleton.elim _ _

def toLevelOne : SL(2, ℤ) →* ↥(GammaH 1 ⊤) where
  toFun g := ⟨g, mem_GammaH_one g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {A : Type*} [AddCommGroup A]

theorem eq_zero_of_apply_T (Ψ : H1 1 ⊤ A) (hT : Ψ (Additive.ofMul (uElt 1 ⊤ 1)) = 0) : Ψ = 0 := by
  let Ψ' : SL(2, ℤ) →* Multiplicative A := (AddMonoidHom.toMultiplicativeRight Ψ).comp toLevelOne
  have hιT : toLevelOne ModularGroup.T = uElt 1 ⊤ 1 := Subtype.ext rfl
  have hT' : Ψ' ModularGroup.T = 1 := by
    change Multiplicative.ofAdd (Ψ (Additive.ofMul (toLevelOne ModularGroup.T))) = 1
    rw [hιT, hT]
    rfl
  have hrel : ModularGroup.S * ModularGroup.S
      = ModularGroup.S * ModularGroup.T * (ModularGroup.S * ModularGroup.T)
          * (ModularGroup.S * ModularGroup.T) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hS' : Ψ' ModularGroup.S = 1 := by
    have h := congrArg Ψ' hrel
    simp only [map_mul, hT', mul_one] at h
    have h' : Ψ' ModularGroup.S * Ψ' ModularGroup.S * 1
        = Ψ' ModularGroup.S * Ψ' ModularGroup.S * Ψ' ModularGroup.S := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have hΨ' : Ψ' = 1 :=
    MonoidHom.eq_of_eqOn_dense SpecialLinearGroup.SL2Z_generators (by
      rintro g (rfl | rfl)
      · exact hS'
      · exact hT')
  refine AddMonoidHom.ext fun x => ?_
  have hx : Ψ x = (Ψ' ((Additive.toMul x : ↥(GammaH 1 ⊤)) : SL(2, ℤ))).toAdd := by
    conv_lhs => rw [← ofMul_toMul x]
    rfl
  rw [hx, hΨ']
  rfl

theorem heckeT_levelOne (A : Type) [AddCommGroup A] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (Φ : H1 1 ⊤ A) : heckeT 1 ⊤ ℓ A Φ = (ℓ + 1) • Φ := by
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  haveI : NeZero (1 * ℓ) := ⟨by rw [one_mul]; exact NeZero.ne ℓ⟩
  have h₁ : LevelLE 1 (1 * ℓ) (⊤ : Subgroup (ZMod 1)ˣ) (⊤ : Subgroup (ZMod (1 * ℓ))ˣ) 1 :=
    ⟨one_dvd _, one_dvd _, fun _ _ => Subgroup.mem_top _⟩
  have hq : LevelLE 1 (1 * ℓ) (⊤ : Subgroup (ZMod 1)ˣ) (⊤ : Subgroup (ZMod (1 * ℓ))ˣ) ℓ :=
    ⟨one_dvd _, by rw [Nat.div_one, one_mul], fun _ _ => Subgroup.mem_top _⟩
  have hℓ1 : ¬ ℓ ∣ 1 := fun h => hℓ.one_lt.ne' (Nat.dvd_one.mp h)
  have key := CohCarrier.heckeT_iDeg_interchange (N := 1) (q := ℓ) hℓ hℓ1 h₁ hq Φ

  set T' : ↥(GammaH (1 * ℓ) ⊤) := uElt (1 * ℓ) ⊤ 1 with hT'
  set T₁ : ↥(GammaH 1 ⊤) := uElt 1 ⊤ 1 with hT₁
  have hι1 : iotaDeg 1 (1 * ℓ) ⊤ ⊤ 1 h₁ T' = T₁ := by
    apply Subtype.ext
    rw [coe_iotaDeg_one]
    rfl
  have hιq : iotaDeg 1 (1 * ℓ) ⊤ ⊤ ℓ hq T' = uElt 1 ⊤ (ℓ : ℤ) := by
    apply Subtype.ext
    change conjLowerMat ℓ (uMat 1) (hq.dvd_entry T') = uMat (ℓ : ℤ)
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjLowerMat, uMat]
  have hev := DFunLike.congr_fun key (Additive.ofMul T')
  rw [heckeT_apply_uElt_one (M := 1 * ℓ) (H := ⊤) (dvd_mul_left ℓ 1)
    (iDeg' 1 (1 * ℓ) ⊤ ⊤ 1 A h₁ Φ), AddMonoidHom.sub_apply] at hev
  change Φ (Additive.ofMul (iotaDeg 1 (1 * ℓ) ⊤ ⊤ 1 h₁ T'))
    = heckeT 1 ⊤ ℓ A Φ (Additive.ofMul (iotaDeg 1 (1 * ℓ) ⊤ ⊤ 1 h₁ T'))
      - Φ (Additive.ofMul (iotaDeg 1 (1 * ℓ) ⊤ ⊤ ℓ hq T')) at hev
  rw [hι1, hιq, show ((ℓ : ℕ) : ℤ) = (ℓ : ℕ) * (1 : ℤ) by ring, ← uElt_pow, ofMul_pow,
    map_nsmul] at hev

  have hT : (heckeT 1 ⊤ ℓ A Φ - (ℓ + 1) • Φ) (Additive.ofMul T₁) = 0 := by
    rw [hT₁] at hev ⊢
    rw [AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply, add_smul, one_smul, sub_eq_zero,
      ← eq_sub_iff_add_eq.mp hev, add_comm]
  have h0 := eq_zero_of_apply_T _ hT
  rwa [sub_eq_zero] at h0

end LevelOne

section MainZero

theorem heckeT_eq_smul_of_vanish₀ (N : ℕ) (A : Type) [AddCommGroup A] (φ : H1 N ⊤ A) (M : ℕ)
    (hM : 0 < M) (hφ : Vanish M φ) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ := by
  have hN : N ≠ 0 := by rintro rfl; exact hℓN (dvd_zero ℓ)
  have hM'0 : N * M ≠ 0 := mul_ne_zero hN hM.ne'

  set P : ℕ := ordProj[ℓ] (N * M) with hP
  set M₁ : ℕ := ordCompl[ℓ] (N * M) with hM₁
  haveI : NeZero P := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  haveI : NeZero M₁ := ⟨(Nat.ordCompl_pos ℓ hM'0).ne'⟩
  have hPM : P * M₁ = N * M := Nat.ordProj_mul_ordCompl_eq_self (N * M) ℓ
  have hcop : Nat.Coprime P M₁ := (Nat.coprime_ordCompl hℓ hM'0).pow_left _
  have hℓM₁ : ¬ ℓ ∣ M₁ := Nat.not_dvd_ordCompl hℓ hM'0
  have hNM₁ : N ∣ M₁ := by
    have hNP : Nat.Coprime N P :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
    have hdiv : N ∣ P * M₁ := by rw [hPM]; exact dvd_mul_right N M
    exact (Nat.Coprime.dvd_mul_left hNP).mp hdiv
  have hφ' : Vanish (P * M₁) φ := by rw [hPM]; exact hφ.of_dvd (dvd_mul_left M N)

  set Φ : H1 1 ⊤ A := bigPhi hcop hNM₁ φ hφ' with hΦ
  have hrest : Vanish M₁ (φ - res N A Φ) := vanish_sub_res hcop hNM₁ φ hφ'
  have h1 := CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd N A
    (φ - res N A Φ) M₁ (NeZero.pos M₁) hrest ℓ hℓ hℓN hℓM₁
  have h2 := CohCarrier.iDeg_heckeT_comm_of_coprime (A := A) (levelLE_one N)
    (Nat.coprime_one_right ℓ) hℓ hℓN Φ
  have h3 := heckeT_levelOne A ℓ hℓ Φ
  calc heckeT N ⊤ ℓ A φ
      = heckeT N ⊤ ℓ A (φ - res N A Φ) + heckeT N ⊤ ℓ A (res N A Φ) := by
        rw [map_sub, sub_add_cancel]
    _ = (ℓ + 1) • (φ - res N A Φ) + res N A (heckeT 1 ⊤ ℓ A Φ) := by
        rw [h1]
        change _ = _ + iDeg' 1 N ⊤ ⊤ 1 A (levelLE_one N) (heckeT 1 ⊤ ℓ A Φ)
        rw [h2]
    _ = (ℓ + 1) • φ := by rw [h3, map_nsmul, smul_sub, sub_add_cancel]

end MainZero

section Universal

theorem heckeT_eq_smul_of_vanish (N : ℕ) (A : Type*) [AddCommGroup A] (φ : H1 N ⊤ A) (M : ℕ)
    (hM : 0 < M) (hφ : Vanish M φ) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ := by
  let φ' : ↥(GammaH N ⊤) →* Multiplicative A := AddMonoidHom.toMultiplicativeRight φ
  let Λ : Type := Abelianization (↥(GammaH N ⊤) ⧸ φ'.ker)
  let u : H1 N ⊤ (Additive Λ) :=
    MonoidHom.toAdditive ((Abelianization.of).comp (QuotientGroup.mk' φ'.ker))
  let f : Additive Λ →+ A :=
    MonoidHom.toAdditiveLeft (Abelianization.lift (QuotientGroup.kerLift φ'))
  have hfu : f.comp u = φ := by
    refine AddMonoidHom.ext fun x => ?_
    conv_rhs => rw [← ofMul_toMul x]
    rfl
  have hu : Vanish M u := by
    intro γ hγ
    have hker : γ ∈ φ'.ker := by
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (φ (Additive.ofMul γ)) = 1
      rw [hφ γ hγ]
      rfl
    change Additive.ofMul (Abelianization.of (QuotientGroup.mk' φ'.ker γ)) = 0
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff γ).mpr hker, map_one, ofMul_one]
  have h0 := heckeT_eq_smul_of_vanish₀ N (Additive Λ) u M hM hu ℓ hℓ hℓN
  rw [← hfu, heckeT_comp_coeff, h0]
  refine AddMonoidHom.ext fun x => ?_
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, map_nsmul]

end Universal

end CohCarrier.CongruenceEisAll

open scoped MatrixGroups in

theorem solution
    (N : ℕ) (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (hφ : ∃ M : ℕ, 0 < M ∧ ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M → φ (Additive.ofMul γ) = 0)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    CohCarrier.heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ := by
  obtain ⟨M, hM, hφM⟩ := hφ
  exact CohCarrier.CongruenceEisAll.heckeT_eq_smul_of_vanish N A φ M hM hφM ℓ hℓ hℓN

end S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero
end P2MW
export P2MW.S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero (solution)
