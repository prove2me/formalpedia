-- Prove2me | solution 1 for CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b5fad5d4-eded-5cad-922e-85088ebe1de5

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups

namespace P2MKcDC

variable {M : ℕ} [NeZero M]

abbrev red (M : ℕ) : SL(2, ℤ) →* SL(2, ZMod M) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

theorem red_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    (red M γ).1 i j = ((γ.1 i j : ℤ) : ZMod M) := by
  simp

def e₁ (M : ℕ) : Fin 2 → ZMod M := Pi.single 0 1

theorem mulVec_e₁ (A : Matrix (Fin 2) (Fin 2) (ZMod M)) : A.mulVec (e₁ M) = fun i => A i 0 := by
  rw [e₁, Matrix.mulVec_single_one]
  rfl

def col (γ : SL(2, ℤ)) : Fin 2 → ZMod M := (red M γ).1.mulVec (e₁ M)

theorem col_apply (γ : SL(2, ℤ)) (i : Fin 2) : col (M := M) γ i = ((γ.1 i 0 : ℤ) : ZMod M) := by
  rw [col, mulVec_e₁]
  exact red_apply γ i 0

theorem col_mul (a b : SL(2, ℤ)) : col (M := M) (a * b) = (red M a).1.mulVec (col b) := by
  rw [col, col, Matrix.mulVec_mulVec, map_mul]
  rfl

theorem col_one : col (M := M) 1 = e₁ M := by
  rw [col, map_one]
  show (1 : Matrix (Fin 2) (Fin 2) (ZMod M)).mulVec (e₁ M) = e₁ M
  rw [Matrix.one_mulVec]

theorem torsion_vec (v : Fin 2 → ZMod M) : M • v = 0 := by
  ext i
  simp

theorem addOrderOf_eq_of_combination (v : Fin 2 → ZMod M) (x y : ZMod M)
    (h : x * v 0 + y * v 1 = 1) : addOrderOf v = M := by
  apply Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero (torsion_vec v))
  have key : ∀ n : ℕ, n • v = 0 → M ∣ n := by
    intro n hn
    have h0 : (n : ZMod M) * v 0 = 0 := by
      have := congrFun hn 0; simpa [nsmul_eq_mul] using this
    have h1 : (n : ZMod M) * v 1 = 0 := by
      have := congrFun hn 1; simpa [nsmul_eq_mul] using this
    have : (n : ZMod M) = 0 := by
      calc (n : ZMod M) = (n : ZMod M) * (x * v 0 + y * v 1) := by rw [h, mul_one]
        _ = x * ((n : ZMod M) * v 0) + y * ((n : ZMod M) * v 1) := by ring
        _ = 0 := by rw [h0, h1, mul_zero, mul_zero, add_zero]
    exact (ZMod.natCast_eq_zero_iff n M).mp this
  exact key _ (addOrderOf_nsmul_eq_zero v)

theorem addOrderOf_col (γ : SL(2, ℤ)) : addOrderOf (col (M := M) γ) = M := by
  apply addOrderOf_eq_of_combination _ ((γ.1 1 1 : ℤ) : ZMod M) (-((γ.1 0 1 : ℤ) : ZMod M))
  rw [col_apply, col_apply]
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  push_cast at this
  linear_combination this

theorem exists_combination_of_addOrderOf_eq (v : Fin 2 → ZMod M) (hv : addOrderOf v = M) :
    ∃ x y : ZMod M, x * v 0 + y * v 1 = 1 := by
  set a : ℕ := (v 0).val with ha
  set c : ℕ := (v 1).val with hc
  set d : ℕ := Nat.gcd (Nat.gcd a c) M with hd
  have hdM : d ∣ M := Nat.gcd_dvd_right _ _
  have hda : d ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hdc : d ∣ c := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by
    intro h; rw [h] at hdM; exact (NeZero.ne M) (Nat.eq_zero_of_zero_dvd hdM))

  have hkill : (M / d) • v = 0 := by
    have hv0 : v 0 = (a : ZMod M) := by rw [ha, ZMod.natCast_zmod_val]
    have hv1 : v 1 = (c : ZMod M) := by rw [hc, ZMod.natCast_zmod_val]
    have h : ∀ b : ℕ, d ∣ b → ((M / d : ℕ) : ZMod M) * (b : ZMod M) = 0 := by
      intro b hb
      obtain ⟨b', rfl⟩ := hb
      rw [← Nat.cast_mul, show M / d * (d * b') = M * b' by
        rw [← mul_assoc, Nat.div_mul_cancel hdM]]
      simp
    ext i
    fin_cases i
    · simpa [nsmul_eq_mul, hv0] using h a hda
    · simpa [nsmul_eq_mul, hv1] using h c hdc
  have hdvd : M ∣ M / d := by
    have := addOrderOf_dvd_of_nsmul_eq_zero hkill
    rwa [hv] at this
  have hd1 : d = 1 := by
    have hle : M ≤ M / d := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hM0 hdM) hd0) hdvd
    by_contra hne
    have h2 : 2 ≤ d := by omega
    have : M / d < M := Nat.div_lt_self hM0 h2
    omega

  have hg : ((Nat.gcd a c : ℕ) : ℤ) = a * Nat.gcdA a c + c * Nat.gcdB a c := Nat.gcd_eq_gcd_ab a c
  have h1 : ((Nat.gcd (Nat.gcd a c) M : ℕ) : ℤ) =
      (Nat.gcd a c : ℕ) * Nat.gcdA (Nat.gcd a c) M + M * Nat.gcdB (Nat.gcd a c) M :=
    Nat.gcd_eq_gcd_ab _ _
  rw [← hd, hd1] at h1
  refine ⟨((Nat.gcdA a c * Nat.gcdA (Nat.gcd a c) M : ℤ) : ZMod M),
    ((Nat.gcdB a c * Nat.gcdA (Nat.gcd a c) M : ℤ) : ZMod M), ?_⟩
  have hv0 : v 0 = ((a : ℤ) : ZMod M) := by rw [Int.cast_natCast, ha, ZMod.natCast_zmod_val]
  have hv1 : v 1 = ((c : ℤ) : ZMod M) := by rw [Int.cast_natCast, hc, ZMod.natCast_zmod_val]
  have key := congrArg (fun z : ℤ => (z : ZMod M)) h1
  simp only [hg] at key
  push_cast at key
  rw [ZMod.natCast_self, zero_mul, add_zero] at key
  rw [hv0, hv1]
  push_cast
  linear_combination -key

theorem exists_col_eq (v : Fin 2 → ZMod M) (hv : addOrderOf v = M) : ∃ γ : SL(2, ℤ), col γ = v := by
  obtain ⟨x, y, hxy⟩ := exists_combination_of_addOrderOf_eq v hv

  let m : SL(2, ZMod M) := ⟨!![v 0, -y; v 1, x], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod M m
  refine ⟨γ, ?_⟩
  rw [col, hγ, mulVec_e₁]
  ext i
  fin_cases i <;> rfl

variable (H : Subgroup (ZMod M)ˣ)

theorem mem_GammaH_iff_col (γ : SL(2, ℤ)) :
    γ ∈ CohCarrier.GammaH M H ↔ ∃ h : (ZMod M)ˣ, h ∈ H ∧ col γ = (h : ZMod M) • e₁ M := by
  constructor
  · intro hγ
    obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    refine ⟨(CohCarrier.gamma0Units M ⟨γ, h0⟩)⁻¹, H.inv_mem hH, ?_⟩
    have hc : ((γ.1 1 0 : ℤ) : ZMod M) = 0 := by exact_mod_cast (CongruenceSubgroup.Gamma0_mem.mp h0)
    ext i
    fin_cases i
    · rw [col_apply]
      simp [e₁]
      rfl
    · rw [col_apply]
      simp [e₁]
      exact hc
  · rintro ⟨h, hh, hcol⟩
    have hc : ((γ.1 1 0 : ℤ) : ZMod M) = 0 := by
      have := congrFun hcol 1
      rw [col_apply] at this
      simpa [e₁] using this
    have ha : ((γ.1 0 0 : ℤ) : ZMod M) = h := by
      have := congrFun hcol 0
      rw [col_apply] at this
      simpa [e₁] using this
    have h0 : γ ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr (by exact_mod_cast hc)
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨h0, ?_⟩
    have hu : (CohCarrier.gamma0Units M ⟨γ, h0⟩)⁻¹ = h := by
      ext
      show ((γ.1 0 0 : ℤ) : ZMod M) = h
      exact ha
    rw [← inv_inv (CohCarrier.gamma0Units M ⟨γ, h0⟩), hu]
    exact H.inv_mem hh

variable (g : SL(2, ℤ))

theorem mk_inv_eq_mk_inv_iff (γ γ' : SL(2, ℤ)) :
    DoubleCoset.mk (CohCarrier.GammaH M H) (Subgroup.zpowers g) γ⁻¹ =
        DoubleCoset.mk (CohCarrier.GammaH M H) (Subgroup.zpowers g) γ'⁻¹ ↔
      ∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧ col γ' = (h : ZMod M) • (red M (g ^ k)).1.mulVec (col γ) := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨δ, hδ, κ, hκ, hEq⟩
    rw [Subgroup.mem_zpowers_iff] at hκ
    obtain ⟨k, rfl⟩ := hκ

    have hγ' : γ' = g ^ (-k) * (γ * δ⁻¹) := by
      have := congrArg (fun z => z⁻¹) hEq
      simp only [inv_inv, mul_inv_rev] at this
      rw [this, zpow_neg]
    obtain ⟨h, hh, hcol⟩ := (mem_GammaH_iff_col H δ⁻¹).mp ((CohCarrier.GammaH M H).inv_mem hδ)
    refine ⟨-k, h, hh, ?_⟩
    rw [hγ', col_mul, col_mul, hcol, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rfl
  · rintro ⟨k, h, hh, hcol⟩

    set y : SL(2, ℤ) := (g ^ k * γ)⁻¹ * γ' with hy
    have hycol : col (M := M) y = (h : ZMod M) • e₁ M := by
      have h1 : col (M := M) γ' = (red M (g ^ k * γ)).1.mulVec ((h : ZMod M) • e₁ M) := by
        rw [Matrix.mulVec_smul, hcol, map_mul]
        congr 1
        show _ = ((red M (g ^ k)).1 * (red M γ).1).mulVec (e₁ M)
        rw [← Matrix.mulVec_mulVec]
        rfl
      have h2 : col (M := M) y = (red M (g ^ k * γ)⁻¹).1.mulVec (col γ') := by
        rw [hy, col_mul]
      rw [h2, h1, Matrix.mulVec_mulVec, map_inv, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have hyH : y ∈ CohCarrier.GammaH M H := (mem_GammaH_iff_col H y).mpr ⟨h, hh, hycol⟩
    refine ⟨y⁻¹, (CohCarrier.GammaH M H).inv_mem hyH, g ^ (-k), Subgroup.zpow_mem_zpowers g (-k), ?_⟩
    rw [hy]
    simp only [mul_inv_rev, inv_inv, zpow_neg]
    group

noncomputable def lift (v : {v : Fin 2 → ZMod M // addOrderOf v = M}) : SL(2, ℤ) :=
  Classical.choose (exists_col_eq v.1 v.2)

theorem col_lift (v : {v : Fin 2 → ZMod M // addOrderOf v = M}) : col (lift v) = v.1 :=
  Classical.choose_spec (exists_col_eq v.1 v.2)

noncomputable def cls (v : {v : Fin 2 → ZMod M // addOrderOf v = M}) :
    DoubleCoset.Quotient (CohCarrier.GammaH M H : Set SL(2, ℤ)) (Subgroup.zpowers g : Set SL(2, ℤ)) :=
  DoubleCoset.mk (CohCarrier.GammaH M H) (Subgroup.zpowers g) (lift v)⁻¹

theorem cls_eq_cls_iff (v v' : {v : Fin 2 → ZMod M // addOrderOf v = M}) :
    cls H g v = cls H g v' ↔ ∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧
      v'.1 = (h : ZMod M) • (red M (g ^ k)).1.mulVec v.1 := by
  rw [cls, cls, mk_inv_eq_mk_inv_iff, col_lift, col_lift]

theorem cls_surjective : Function.Surjective (cls H g) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
    let v : {v : Fin 2 → ZMod M // addOrderOf v = M} := ⟨col a⁻¹, addOrderOf_col a⁻¹⟩
    refine ⟨v, ?_⟩
    show DoubleCoset.mk _ _ (lift v)⁻¹ = DoubleCoset.mk _ _ a
    rw [← inv_inv a, mk_inv_eq_mk_inv_iff, col_lift]
    refine ⟨0, 1, H.one_mem, ?_⟩
    rw [zpow_zero, map_one, Units.val_one, one_smul]
    show col a⁻¹ = (1 : Matrix (Fin 2) (Fin 2) (ZMod M)).mulVec (col a⁻¹)
    rw [Matrix.one_mulVec]

end P2MKcDC

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ c : {v : Fin 2 → ZMod M // addOrderOf v = M} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers g : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ v v', c v = c v' ↔ ∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧
        v'.1 = (h : ZMod M) •
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g ^ k)).1.mulVec v.1) :=
  ⟨P2MKcDC.cls H g, P2MKcDC.cls_surjective H g, P2MKcDC.cls_eq_cls_iff H g⟩

end S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
end P2MW
export P2MW.S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq (solution)
