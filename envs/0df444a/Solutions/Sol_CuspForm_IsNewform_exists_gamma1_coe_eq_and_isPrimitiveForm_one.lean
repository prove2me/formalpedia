-- Prove2me | solution 1 for CuspForm.IsNewform.exists_gamma1_coe_eq_and_isPrimitiveForm_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1e30c42c-52ba-58bd-a965-d81f17b383da

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups ModularForm

namespace NewformToPrimitive

local notation "Γ₁ℝ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_gamma0 (N : ℕ) : (1 : ℝ) ∈ (Γ₀ℝ(N)).strictPeriods := by
  simp

theorem one_mem_strictPeriods_gamma1 (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ(N)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem qCoeff_zero_gamma0 {N : ℕ} {k : ℤ} (f : CuspForm Γ₀ℝ(N) k) : qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods_gamma0 N)

theorem qCoeff_zero_gamma1 {N : ℕ} {k : ℤ} (f : CuspForm Γ₁ℝ(N) k) : qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods_gamma1 N)

section FromNormalized

variable {N : ℕ} {g : CuspForm Γ₀ℝ(N) 2}

theorem hecke_T_of_isNormalizedEigenform (hg : g.IsNormalizedEigenform) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (n : ℕ) :
    qCoeff g (p * n) + (p : ℂ) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [qCoeff_zero_gamma0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  have hcop : ∀ s : ℕ, (p ^ s).Coprime m := fun s =>
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  cases r with
  | zero =>
    have hndvd : ¬ p ∣ p ^ 0 * m := by simpa using hm
    rw [if_neg hndvd, mul_zero, add_zero, pow_zero, one_mul,
      hg.qCoeff_mul_of_coprime p m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)]
  | succ s =>
    have hdvd : p ∣ p ^ (s + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero s)) m
    rw [if_pos hdvd,
      show p * (p ^ (s + 1) * m) = p ^ (s + 2) * m by ring,
      show p ^ (s + 1) * m / p = p ^ s * m by
        rw [pow_succ, mul_assoc, mul_comm p, ← mul_assoc, Nat.mul_div_cancel _ hp.pos],
      hg.qCoeff_mul_of_coprime _ _ (hcop _), hg.qCoeff_mul_of_coprime _ _ (hcop _),
      hg.qCoeff_mul_of_coprime _ _ (hcop _), hg.qCoeff_prime_pow_of_not_dvd p s hp hpN]
    ring

theorem qCoeff_pow_succ_of_dvd (hg : g.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (r : ℕ) : qCoeff g (ℓ ^ (r + 1)) = qCoeff g ℓ * qCoeff g (ℓ ^ r) := by
  cases r with
  | zero => rw [zero_add, pow_one, pow_zero, hg.qCoeff_one, mul_one]
  | succ s => rw [hg.qCoeff_prime_pow_of_dvd ℓ s hℓ hℓN]

theorem hecke_U_of_isNormalizedEigenform (hg : g.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ℓ ∣ N) (n : ℕ) : qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [qCoeff_zero_gamma0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.one_lt.ne'
  have hcop : ∀ s : ℕ, (ℓ ^ s).Coprime m := fun s =>
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm)
  rw [show ℓ * (ℓ ^ r * m) = ℓ ^ (r + 1) * m by ring, hg.qCoeff_mul_of_coprime _ _ (hcop _),
    hg.qCoeff_mul_of_coprime _ _ (hcop _), qCoeff_pow_succ_of_dvd hg hℓ hℓN r]
  ring

end FromNormalized

section Slash

variable {N : ℕ} {k : ℤ}

def dd (γ : SL(2, ℤ)) : ZMod N := ((γ 1 1 : ℤ) : ZMod N)

theorem sl_slash (f : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

theorem denom_eq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

theorem slash_eq_smul_iff (ε : DirichletCharacter ℂ N) (g : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    g ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ε (dd γ) • g ↔
      ∀ τ : UpperHalfPlane, g (γ • τ) =
        ε ((γ 1 1 : ℤ) : ZMod N) *
          ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ) := by
  constructor
  · intro h τ
    have hslash := congrFun h τ
    rw [← sl_slash, ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, denom_eq] at hslash
    have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ τ
    have hzk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne
    have key : g (γ • τ) =
        ε (dd (N := N) γ) * g τ * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hzk]
      exact hslash
    rw [key, ← zpow_neg, neg_neg, dd]
    ring
  · intro h
    funext τ
    have hpt := h τ
    rw [← sl_slash, ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, denom_eq]
    have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ τ
    rw [hpt, dd, zpow_neg]
    field_simp

theorem isUnit_dd_of_mem_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : IsUnit (dd (N := N) γ) := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact h
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hγ
  have h1 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at h
    exact h
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1)

theorem one_apply_dd_of_mem_gamma0 [NeZero N] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (1 : DirichletCharacter ℂ N) (dd γ) = 1 :=
  MulChar.one_apply (isUnit_dd_of_mem_gamma0 hγ)

end Slash

section Copies

variable {N : ℕ} [NeZero N]

def toGamma1 {k : ℤ} (g : CuspForm Γ₀ℝ(N) k) : CuspForm Γ₁ℝ(N) k where
  toFun := g
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact SlashInvariantFormClass.slash_action_eq g _
      (Subgroup.mem_map_of_mem _ (Gamma1_in_Gamma0 N hγ₀))
  holo' := CuspFormClass.holo g
  zero_at_cusps' hc := by
    apply CuspFormClass.zero_at_cusps g
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc

@[scoped simp] theorem coe_toGamma1 {k : ℤ} (g : CuspForm Γ₀ℝ(N) k) :
    (toGamma1 g : UpperHalfPlane → ℂ) = g := rfl

theorem hasNebentypus_one_toGamma1 {k : ℤ} (g : CuspForm Γ₀ℝ(N) k) :
    CuspForm.HasNebentypus (1 : DirichletCharacter ℂ N) (toGamma1 g) := by
  intro γ hγ τ
  have hs : (⇑(toGamma1 g) : UpperHalfPlane → ℂ) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
        (1 : DirichletCharacter ℂ N) (dd γ) • ⇑(toGamma1 g) := by
    rw [one_apply_dd_of_mem_gamma0 hγ, one_smul, coe_toGamma1]
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)
  exact (slash_eq_smul_iff (1 : DirichletCharacter ℂ N) _ γ).1 hs τ

def toGamma0 {k : ℤ} (h : CuspForm Γ₁ℝ(N) k)
    (hε : CuspForm.HasNebentypus (1 : DirichletCharacter ℂ N) h) : CuspForm Γ₀ℝ(N) k where
  toFun := h
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    have hs := (slash_eq_smul_iff (k := k) (1 : DirichletCharacter ℂ N) (⇑h) γ₀).2 (hε γ₀ hγ₀)
    rwa [one_apply_dd_of_mem_gamma0 hγ₀, one_smul] at hs
  holo' := CuspFormClass.holo h
  zero_at_cusps' hc := by
    apply CuspFormClass.zero_at_cusps h
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc

@[scoped simp] theorem coe_toGamma0 {k : ℤ} (h : CuspForm Γ₁ℝ(N) k)
    (hε : CuspForm.HasNebentypus (1 : DirichletCharacter ℂ N) h) :
    (toGamma0 h hε : UpperHalfPlane → ℂ) = h := rfl

end Copies

section ToNormalized

variable {N : ℕ} {k : ℤ}

structure CoeffRelations (a : ℕ → ℂ) : Prop where
  one : a 1 = 1
  T : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
    a (p * n) + (p : ℂ) ^ (k - 1) * (if p ∣ n then a (n / p) else 0) = a p * a n
  U : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ n : ℕ, a (ℓ * n) = a ℓ * a n

namespace CoeffRelations

variable {a : ℕ → ℂ}

theorem prime_mul (h : CoeffRelations (N := N) (k := k) a) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    a (p * n) = a p * a n - (if p ∣ N then 0 else (p : ℂ) ^ (k - 1) * (if p ∣ n then a (n / p) else 0)) := by
  by_cases hpN : p ∣ N
  · rw [if_pos hpN, sub_zero, h.U p hp hpN n]
  · rw [if_neg hpN, ← h.T p hp hpN n, add_sub_cancel_right]

theorem mul_of_coprime (h : CoeffRelations (N := N) (k := k) a) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      ·
        have hn : n = 1 := by simpa using hmn
        subst hn
        rw [mul_one, h.one, mul_one]
      · rw [one_mul, h.one, one_mul]
    ·
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
      obtain ⟨m', rfl⟩ := hpm
      have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm
      have hm'lt : m' < p * m' := by
        have := hp.one_lt
        nlinarith [Nat.pos_of_ne_zero hm'0]
      have hpn : ¬ p ∣ n := by
        intro hpn
        have h1 : p ∣ Nat.gcd (p * m') n := Nat.dvd_gcd (dvd_mul_right p m') hpn
        rw [hmn] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
      have hm'n : m'.Coprime n := Nat.Coprime.coprime_mul_left hmn

      have e1 : a (p * m' * n) = a p * a (m' * n) -
          (if p ∣ N then 0 else (p : ℂ) ^ (k - 1) * (if p ∣ m' * n then a (m' * n / p) else 0)) := by
        rw [mul_assoc]; exact h.prime_mul hp (m' * n)
      have e2 : a (p * m') = a p * a m' -
          (if p ∣ N then 0 else (p : ℂ) ^ (k - 1) * (if p ∣ m' then a (m' / p) else 0)) := h.prime_mul hp m'
      have e3 : a (m' * n) = a m' * a n := ih m' hm'lt n hm'n
      have hdvd_iff : (p ∣ m' * n) ↔ p ∣ m' :=
        ⟨fun hd => (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn) hd),
          fun hd => hd.mul_right n⟩
      rw [e1, e2, e3]
      by_cases hpN : p ∣ N
      · simp only [if_pos hpN]; ring
      · simp only [if_neg hpN]
        by_cases hpm' : p ∣ m'
        · obtain ⟨r, rfl⟩ := hpm'
          have hr0 : r ≠ 0 := by rintro rfl; simp at hm'0
          have hrlt : r < p * (p * r) := by
            have := hp.one_lt
            nlinarith [Nat.pos_of_ne_zero hr0]
          have hrn : r.Coprime n := Nat.Coprime.coprime_mul_left hm'n
          rw [if_pos ((dvd_mul_right p r).mul_right n), if_pos (dvd_mul_right p r),
            show p * r * n / p = r * n by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos],
            Nat.mul_div_cancel_left _ hp.pos, ih r hrlt n hrn]
          ring
        · rw [if_neg (fun hd => hpm' (hdvd_iff.1 hd)), if_neg hpm']
          ring

theorem prime_pow_of_not_dvd (h : CoeffRelations (N := N) (k := k) a) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * a (p ^ r) := by
  have hT := h.T p hp hpN (p ^ (r + 1))
  rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero r)),
    show p ^ (r + 1) / p = p ^ r by rw [pow_succ, Nat.mul_div_cancel _ hp.pos],
    show p * p ^ (r + 1) = p ^ (r + 2) by ring] at hT
  rw [← hT]; ring

theorem prime_pow_of_dvd (h : CoeffRelations (N := N) (k := k) a) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) (r : ℕ) : a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) := by
  rw [show p ^ (r + 2) = p * p ^ (r + 1) by ring, h.U p hp hpN]

end CoeffRelations

theorem isNormalizedEigenform_toGamma0 [NeZero N] (h : CuspForm Γ₁ℝ(N) 2)
    (hh : CuspForm.IsEigenformWith (1 : DirichletCharacter ℂ N) h) :
    (toGamma0 h hh.hasNebentypus).IsNormalizedEigenform := by
  have hrel : CoeffRelations (N := N) (k := (2 : ℤ)) (fun n => qCoeff h n) := by
    refine ⟨hh.qCoeff_one, fun p hp hpN n => ?_, fun ℓ hℓ hℓN n => hh.hecke_of_dvd hℓ hℓN n⟩
    have h1 := hh.hecke_of_not_dvd hp hpN n
    rw [MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd hp).2 hpN), one_mul] at h1
    exact h1
  refine ⟨hh.qCoeff_one, fun m n hmn => hrel.mul_of_coprime m n hmn, fun p r hp hpN => ?_,
    fun p r hp hpN => hrel.prime_pow_of_dvd hp hpN r⟩
  have h1 := hrel.prime_pow_of_not_dvd hp hpN r
  have h21 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [h21, zpow_one] at h1
  exact h1

end ToNormalized

theorem eq_one_of_forall_prime_not_dvd {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (ε : DirichletCharacter ℂ M) (hε : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ε (p : ZMod M) = 1) : ε = 1 := by
  haveI : NeZero M := ⟨fun h0 => by
    subst h0
    exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd hMN)⟩
  apply MulChar.ext'
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha

    have hsurj := ZMod.unitsMap_surjective hMN
    obtain ⟨v, hv⟩ := hsurj u
    obtain ⟨p, hpgt, hp, hpv⟩ := Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit v) N
    have hpN : ¬ p ∣ N := fun hd => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd
      omega
    have hpu : (u : ZMod M) = (p : ZMod M) := by
      rw [← hv, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hpv, map_natCast]
    rw [MulChar.one_apply (Units.isUnit u), hpu]
    exact hε p hp hpN
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]

theorem main {N : ℕ} [NeZero N] {g : CuspForm Γ₀ℝ(N) 2} (hg : g.IsNewform) :
    ∃ g₁ : CuspForm Γ₁ℝ(N) 2, (g₁ : UpperHalfPlane → ℂ) = (g : UpperHalfPlane → ℂ) ∧
        CuspForm.IsPrimitiveForm (1 : DirichletCharacter ℂ N) g₁ := by
  classical
  set g₁ : CuspForm Γ₁ℝ(N) 2 := toGamma1 g with hg₁
  have hcoe : (g₁ : UpperHalfPlane → ℂ) = g := rfl
  have hnorm := hg.isNormalizedEigenform

  have hqc : ∀ n : ℕ, qCoeff g₁ n = qCoeff g n := fun n => rfl
  have h21 : ((2 : ℤ) - 1) = 1 := by norm_num
  have hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      qCoeff g₁ (p * n) + (p : ℂ) ^ ((2 : ℤ) - 1) * (if p ∣ n then qCoeff g₁ (n / p) else 0) =
        qCoeff g₁ p * qCoeff g₁ n := by
    intro p hp hpN n
    simp only [hqc, h21, zpow_one]
    exact hecke_T_of_isNormalizedEigenform hnorm hp hpN n
  have hE : CuspForm.IsEigenformWith (1 : DirichletCharacter ℂ N) g₁ := by
    refine ⟨hnorm.qCoeff_one, fun p hp hpN n => ?_, fun ℓ hℓ hℓN n =>
      hecke_U_of_isNormalizedEigenform hnorm hℓ hℓN n, hasNebentypus_one_toGamma1 g⟩
    rw [MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd hp).2 hpN), one_mul]
    exact hT p hp hpN n

  obtain ⟨M, hM0, ε, g', hMN, hprim', hg'⟩ :=
    CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen N 2 g₁ hnorm.qCoeff_one
      (fun p => (p : ℂ) ^ ((2 : ℤ) - 1)) (fun p hp hpN n => hT p hp hpN n)

  have hε1 : ε = 1 := by
    refine eq_one_of_forall_prime_not_dvd hMN ε fun p hp hpN => ?_
    have h2 := (hg' p hp hpN).2
    have hp0 : (p : ℂ) ^ ((2 : ℤ) - 1) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
    have h3 : (ε (p : ZMod M) - 1) * (p : ℂ) ^ ((2 : ℤ) - 1) = 0 := by rw [sub_mul, one_mul, h2, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hp0
  subst hε1

  by_cases hMeq : M = N
  · subst hMeq

    have hEq : g₁ = qCoeff g₁ 1 • g' := by
      refine CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M 2 1 g' hprim' g₁
        hE.hasNebentypus ∅ fun p hp _ hpN n => ?_
      rw [(hg' p hp hpN).1]
      exact hE.hecke_of_not_dvd hp hpN n
    rw [show qCoeff g₁ 1 = 1 from hnorm.qCoeff_one, one_smul] at hEq
    refine ⟨g₁, hcoe, ?_⟩
    rw [hEq]
    exact hprim'
  ·
    exfalso
    have hM : NeZero M := hM0
    set g'' : CuspForm Γ₀ℝ(M) 2 := toGamma0 g' hprim'.isEigenformWith.hasNebentypus with hg''
    have hnorm'' : g''.IsNormalizedEigenform := isNormalizedEigenform_toGamma0 g' hprim'.isEigenformWith
    refine hg.2 M hMN hMeq ⟨g'', hnorm'', fun ℓ hℓ hℓN => ?_⟩
    change qCoeff g' ℓ = qCoeff g ℓ
    rw [(hg' ℓ hℓ hℓN).1, hqc]

end NewformToPrimitive
p2m_reactivate "P2MW.S_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one.NewformToPrimitive"

end
p2m_reactivate "P2MW.S_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one.NewformToPrimitive"

theorem solution
    {N : ℕ} [NeZero N] {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNewform) :
    ∃ g₁ : CuspForm (CongruenceSubgroup.Gamma1 N) 2,
      (g₁ : UpperHalfPlane → ℂ) = (g : UpperHalfPlane → ℂ) ∧
        CuspForm.IsPrimitiveForm (1 : DirichletCharacter ℂ N) g₁ :=
  NewformToPrimitive.main hg

end S_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one (solution)
