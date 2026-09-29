-- Prove2me | solution 1 for CuspForm.IsNewform.eq_of_forall_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/21f39dc0-c97f-549e-8c24-aae50729e928

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_Petersson
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_petersson_add_left
import Theorems.Thm_CuspForm_petersson_smul_left
import Theorems.Thm_CuspForm_petersson_conj_symm
import Theorems.Thm_CuspForm_petersson_self_eq_zero_iff
import Theorems.Thm_CuspForm_petersson_heckeTLin
import Theorems.Thm_CuspForm_span_heckeTLin_eigen_eq_top
import Theorems.Thm_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero
import Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_eq_zero_of_gamma0_one_weight_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_eq_of_forall_qCoeff_eq
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

noncomputable section

open ModularFormClass
open scoped MatrixGroups ModularForm

namespace AlliAux1X2

section pet

variable {N : ℕ} {k : ℤ} [NeZero N]

theorem pet_add_right (f g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (g₁ + g₂) = CuspForm.petersson f g₁ + CuspForm.petersson f g₂ := by
  rw [← CuspForm.petersson_conj_symm f (g₁ + g₂), CuspForm.petersson_add_left, map_add,
    CuspForm.petersson_conj_symm, CuspForm.petersson_conj_symm]

theorem pet_smul_right (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (c • g) = c * CuspForm.petersson f g := by
  rw [← CuspForm.petersson_conj_symm f (c • g), CuspForm.petersson_smul_left, map_mul,
    starRingEnd_self_apply, CuspForm.petersson_conj_symm]

theorem pet_sub_left (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f₁ - f₂) g = CuspForm.petersson f₁ g - CuspForm.petersson f₂ g := by
  rw [sub_eq_add_neg, CuspForm.petersson_add_left, ← neg_one_smul ℂ f₂, CuspForm.petersson_smul_left,
    map_neg, map_one]
  ring

def petR (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ℂ where
  toFun g := CuspForm.petersson f g
  map_add' := pet_add_right f
  map_smul' c g := by rw [RingHom.id_apply, smul_eq_mul]; exact pet_smul_right c f g

theorem petR_apply (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : petR f g = CuspForm.petersson f g := rfl

theorem eigen_real {g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg0 : g ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {a : ℂ} (ha : CuspForm.heckeTLin k hℓ hℓN g = a • g) :
    starRingEnd ℂ a = a := by
  have h1 := CuspForm.petersson_heckeTLin hℓ hℓN g g
  rw [ha, CuspForm.petersson_smul_left, pet_smul_right] at h1
  have hne : CuspForm.petersson g g ≠ 0 := fun h0 => hg0 ((CuspForm.petersson_self_eq_zero_iff g).mp h0)
  exact mul_right_cancel₀ hne h1

end pet

theorem hΓ (M : ℕ) [NeZero M] : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

def qCoeffLin (M n : ℕ) [NeZero M] : CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] ℂ where
  toFun G := ModularFormClass.qCoeff G n
  map_add' f g := by
    show ModularFormClass.qCoeff (⇑(f + g)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (hΓ M) f g, map_add]
  map_smul' c f := by
    show ModularFormClass.qCoeff (⇑(c • f)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul]
    rfl

theorem qCoeffLin_apply (M n : ℕ) [NeZero M] (G : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    qCoeffLin M n G = ModularFormClass.qCoeff G n := rfl

theorem qCoeff_sub' {M : ℕ} [NeZero M] (A B : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(A - B)) n = ModularFormClass.qCoeff (⇑A) n - ModularFormClass.qCoeff (⇑B) n := by
  rw [← qCoeffLin_apply, map_sub, qCoeffLin_apply, qCoeffLin_apply]

section newperp

variable {R : ℕ} [NeZero R] {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} (hg : g.IsNewform)
  {q R₀ : ℕ} (hqR : q * R₀ ∣ R) (hq : q.Prime) (hqR₀ : q * R₀ = R)
omit [NeZero R] in
include hqR₀ in
theorem R₀_dvd : R₀ ∣ R := ⟨q, by rw [← hqR₀, mul_comm]⟩

omit [NeZero R] in
include hqR₀ in
theorem not_dvd_R₀ {ℓ : ℕ} (hℓR : ¬ ℓ ∣ R) : ¬ ℓ ∣ R₀ := fun h => hℓR (h.trans (R₀_dvd hqR₀))

include hqR₀ in
theorem neZero_R₀ : NeZero R₀ :=
  ⟨fun h => NeZero.ne R (by rw [← hqR₀, h, mul_zero])⟩

include hq hqR₀ in
theorem R₀_ne : R₀ ≠ R := by
  intro h
  haveI := neZero_R₀ hqR₀
  have h1 : q * R₀ = 1 * R₀ := by rw [hqR₀, one_mul, h]
  exact hq.one_lt.ne' (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne R₀)) h1)

include hg hq hqR₀

theorem newperp_eigen (w : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2)
    (hw : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓR₀ : ¬ ℓ ∣ R₀), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓR₀ w = c • w) :
    CuspForm.petersson g (FreyPackage.ModMCarrier.rescaleLin hqR 2 w) = 0 := by
  haveI := neZero_R₀ hqR₀
  obtain ⟨_, Hg⟩ := (CuspForm.isNormalizedEigenform_iff_heckeTLin g).mp hg.1
  by_cases hA : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓR : ¬ ℓ ∣ R),
      CuspForm.heckeTLin 2 hℓ (not_dvd_R₀ hqR₀ hℓR) w = ModularFormClass.qCoeff g ℓ • w
  ·
    by_cases hw0 : w = 0
    · rw [hw0, map_zero, ← petR_apply, map_zero]
    · exfalso
      obtain ⟨h₀, hh₀, hcoef⟩ :=
        CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul hw0
          (fun ℓ => ModularFormClass.qCoeff g ℓ) {ℓ | ℓ ∣ R}
          (fun ℓ hℓ hℓR₀ hℓS => hA ℓ hℓ hℓS)
      refine hg.2 R₀ (R₀_dvd hqR₀) (R₀_ne hq hqR₀) ⟨h₀, hh₀, fun ℓ hℓ hℓR => ?_⟩
      exact hcoef ℓ hℓ (not_dvd_R₀ hqR₀ hℓR) hℓR
  ·
    push Not at hA
    obtain ⟨ℓ, hℓ, hℓR, hne⟩ := hA
    obtain ⟨c, hc⟩ := hw ℓ hℓ (not_dvd_R₀ hqR₀ hℓR)
    have hca : ModularFormClass.qCoeff g ℓ ≠ c := fun h => hne (by rw [hc, h])
    have hTv : CuspForm.heckeTLin 2 hℓ hℓR (FreyPackage.ModMCarrier.rescaleLin hqR 2 w)
        = c • FreyPackage.ModMCarrier.rescaleLin hqR 2 w := by
      rw [CuspForm.heckeTLin_rescaleLin hqR hℓ hℓR (not_dvd_R₀ hqR₀ hℓR) w, hc, map_smul]
    have hTg : CuspForm.heckeTLin 2 hℓ hℓR g = ModularFormClass.qCoeff g ℓ • g := (Hg ℓ hℓ).1 hℓR
    have hreal := eigen_real hg.ne_zero hℓ hℓR hTg
    have h1 := CuspForm.petersson_heckeTLin hℓ hℓR g (FreyPackage.ModMCarrier.rescaleLin hqR 2 w)
    rw [hTg, hTv, CuspForm.petersson_smul_left, pet_smul_right, hreal] at h1
    have h2 : (ModularFormClass.qCoeff g ℓ - c)
        * CuspForm.petersson g (FreyPackage.ModMCarrier.rescaleLin hqR 2 w) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) hca
    · exact h

theorem newperp (w : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2) :
    CuspForm.petersson g (FreyPackage.ModMCarrier.rescaleLin hqR 2 w) = 0 := by
  haveI := neZero_R₀ hqR₀
  let φ : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2 →ₗ[ℂ] ℂ :=
    (petR g).comp (FreyPackage.ModMCarrier.rescaleLin hqR 2)
  have hle : (⊤ : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 R₀) 2)) ≤ LinearMap.ker φ := by
    rw [← CuspForm.span_heckeTLin_eigen_eq_top R₀, Submodule.span_le]
    intro v hv
    exact LinearMap.mem_ker.mpr (newperp_eigen hg hqR hq hqR₀ v hv)
  exact LinearMap.mem_ker.mp (hle Submodule.mem_top)

end newperp

theorem main {M R : ℕ} [NeZero M]
    {g g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    g = g' := by
  haveI : NeZero R := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne M) hR⟩
  have hcoef : ∀ n : ℕ, Nat.Coprime n M → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n :=
    fun n hn => hg.1.qCoeff_eq_of_coprime_of_forall_prime_not_dvd hg'.1 hR hR h hn
  have hdc : ∀ n : ℕ, Nat.Coprime n M → ModularFormClass.qCoeff (⇑(g - g')) n = 0 := by
    intro n hn
    rw [qCoeff_sub', hcoef n hn, sub_self]
  rcases Nat.lt_or_ge 1 M with hM | hM
  · have hmem := CuspForm.mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero (m := R) hM hdc
    have hkill : ∀ G : CuspForm (CongruenceSubgroup.Gamma0 R) 2, G.IsNewform →
        CuspForm.petersson G (g - g') = 0 := by
      intro G hG
      have hle : Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 R) 2 |
          ∃ (q R₀ : ℕ) (hqR : q * R₀ ∣ R) (fq : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2),
            q.Prime ∧ q * R₀ = R ∧ F = FreyPackage.ModMCarrier.rescaleLin hqR 2 fq}
          ≤ LinearMap.ker (petR G) := by
        rw [Submodule.span_le]
        rintro F ⟨q, R₀, hqR, fq, hq, hqR₀, rfl⟩
        exact LinearMap.mem_ker.mpr (newperp hG hqR hq hqR₀ fq)
      exact LinearMap.mem_ker.mp (hle hmem)
    have hdd : CuspForm.petersson (g - g') (g - g') = 0 := by
      rw [pet_sub_left, hkill g hg, hkill g' hg', sub_self]
    exact sub_eq_zero.mp ((CuspForm.petersson_self_eq_zero_iff (g - g')).mp hdd)
  · have hM1 : M = 1 := le_antisymm hM (Nat.pos_of_ne_zero (NeZero.ne M))
    have hR1 : R = 1 := Nat.dvd_one.mp (hM1 ▸ hR)
    subst hR1
    exact absurd (CuspForm.eq_zero_of_gamma0_one_weight_two g) hg.ne_zero

end AlliAux1X2

theorem solution
    {M R : ℕ} [NeZero M]
    {g g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    g = g' :=
  AlliAux1X2.main hg hg' hR h

end

end S_CuspForm_IsNewform_eq_of_forall_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsNewform_eq_of_forall_qCoeff_eq (solution)
