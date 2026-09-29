-- Prove2me | solution 1 for CuspForm.sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5a831efd-db7d-5391-b95b-d5522316aa3e

import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq
import Theorems.Thm_CuspForm_heckeTLin_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open ModularForm ModularFormClass FreyPackage.ModMCarrier
open scoped ModularForm

namespace OldSpaceSol

theorem heckeDiagMatrix_one : heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem heckeDiagMatrix_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    heckeDiagMatrix a * heckeDiagMatrix b = heckeDiagMatrix (a * b) := by
  apply Units.ext
  rw [Units.val_mul, val_heckeDiagMatrix ha, val_heckeDiagMatrix hb,
    val_heckeDiagMatrix (mul_ne_zero ha hb)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem vadd_nat_apply {L : ℕ} {k : ℤ} (G : CuspForm (CongruenceSubgroup.Gamma0 L) k) (j : ℕ)
    (τ : UpperHalfPlane) : G ((j : ℝ) +ᵥ τ) = G τ := by
  apply SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact ⟨j, by simp⟩

theorem heckeU_slash_heckeDiagMatrix {L : ℕ} (G : CuspForm (CongruenceSubgroup.Gamma0 L) 2)
    {r : ℕ} (hr : r ≠ 0) :
    heckeU 2 r (⇑G ∣[(2 : ℤ)] heckeDiagMatrix r) = (r : ℂ) • ⇑G := by
  ext τ
  rw [heckeU, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have key : ∀ j ∈ Finset.range r,
      ((⇑G ∣[(2 : ℤ)] heckeDiagMatrix r) ∣[(2 : ℤ)] heckeMatrix r j) τ = G τ := by
    intro j _
    rw [slash_heckeMatrix_apply 2 hr, slash_heckeDiagMatrix_apply 2 hr]
    have hpt : heckeDiagMatrix r • heckeMatrix r j • τ = ((j : ℝ) +ᵥ τ) := by
      apply UpperHalfPlane.ext
      rw [coe_heckeDiagMatrix_smul hr, coe_heckeMatrix_smul hr, UpperHalfPlane.coe_vadd]
      rw [mul_div_cancel₀ _ hr']
      push_cast
      ring
    rw [hpt, vadd_nat_apply]
    have e : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [e, zpow_one, ← mul_assoc, inv_mul_cancel₀ hr', one_mul]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

section Level

variable {N r : ℕ} [NeZero N] (hr : r.Prime) (hrN : ¬ r ∣ N)

omit [NeZero N] in
theorem one_mul_dvd : 1 * N ∣ N * r := ⟨r, by ring⟩

omit [NeZero N] in
theorem r_mul_dvd : r * N ∣ N * r := ⟨1, by ring⟩

scoped instance neZero_mul [NeZero r] : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne r)⟩

abbrev ι₁ (r : ℕ) [NeZero r] : CuspForm (CongruenceSubgroup.Gamma0 N) 2 →ₗ[ℂ]
    CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2 :=
  rescaleLin (one_mul_dvd (N := N) (r := r)) 2

abbrev ιr (r : ℕ) [NeZero r] : CuspForm (CongruenceSubgroup.Gamma0 N) 2 →ₗ[ℂ]
    CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2 :=
  rescaleLin (r_mul_dvd (N := N) (r := r)) 2

abbrev Ur (r : ℕ) [NeZero r] : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) :=
  CuspForm.heckeULin 2 (dvd_mul_left r N)

include hr hrN in

theorem Ur_ι₁ [NeZero r] (G : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Ur r (ι₁ r G) = ι₁ r (CuspForm.heckeTLin 2 hr hrN G) - ιr r G := by
  apply DFunLike.coe_injective
  beta_reduce
  rw [CuspForm.coe_sub]
  simp only [Ur, ι₁, ιr, CuspForm.coe_heckeULin_apply, coe_rescaleLin_apply,
    CuspForm.coe_heckeTLin_apply, heckeDiagMatrix_one, SlashAction.slash_one]
  rw [heckeT_eq_heckeU_add, add_sub_cancel_right]

theorem Ur_ιr [NeZero r] (G : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Ur r (ιr r G) = (r : ℂ) • ι₁ r G := by
  apply DFunLike.coe_injective
  beta_reduce
  rw [CuspForm.IsGLPos.coe_smul]
  simp only [Ur, ι₁, ιr, CuspForm.coe_heckeULin_apply, coe_rescaleLin_apply, heckeDiagMatrix_one,
    SlashAction.slash_one]
  exact heckeU_slash_heckeDiagMatrix G (NeZero.ne r)

abbrev Q (r : ℕ) [NeZero r] (a : ℂ) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) :=
  Ur r * Ur r - a • Ur r + (r : ℂ) • 1

include hr hrN in
theorem Q_ι₁ [NeZero r] {a : ℂ} (G : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hG : CuspForm.heckeTLin 2 hr hrN G = a • G) : Q r a (ι₁ r G) = 0 := by
  have h1 : Ur r (ι₁ r G) = a • ι₁ r G - ιr r G := by rw [Ur_ι₁ hr hrN, hG, map_smul]
  simp only [Q, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, h1, map_sub, map_smul, Ur_ιr]
  module

include hr hrN in
theorem Q_ιr [NeZero r] {a : ℂ} (G : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hG : CuspForm.heckeTLin 2 hr hrN G = a • G) : Q r a (ιr r G) = 0 := by
  have h1 : Ur r (ι₁ r G) = a • ι₁ r G - ιr r G := by rw [Ur_ι₁ hr hrN, hG, map_smul]
  simp only [Q, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, Ur_ιr, map_smul, h1]
  module

end Level

section Old

variable {N r : ℕ} [NeZero N] [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N) (S : Finset ℕ)
  {M₀ : ℕ} (hM₀N : M₀ ∣ N)
  (g₀ : CuspForm (CongruenceSubgroup.Gamma0 M₀) 2) (hg₀ : g₀.IsNewform)

def bigM (N r : ℕ) (S : Finset ℕ) : ℕ := N * r * ∏ s ∈ S.filter (· ≠ 0), s

theorem bigM_ne_zero : bigM N r S ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne r)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  exact (Finset.mem_filter.mp hs).2

scoped instance neZero_bigM : NeZero (bigM N r S) := ⟨bigM_ne_zero S⟩

omit [NeZero N] [NeZero r] in
theorem L_dvd_bigM : N * r ∣ bigM N r S := Dvd.intro _ rfl

omit [NeZero N] [NeZero r] in
theorem N_dvd_bigM : N ∣ bigM N r S := (Dvd.intro _ rfl : N ∣ N * r).trans (L_dvd_bigM S)

omit [NeZero N] [NeZero r] in
theorem not_dvd_L {ℓ : ℕ} (h : ¬ ℓ ∣ bigM N r S) : ¬ ℓ ∣ N * r :=
  fun h' => h (h'.trans (L_dvd_bigM S))

omit [NeZero N] [NeZero r] in
theorem not_dvd_N {ℓ : ℕ} (h : ¬ ℓ ∣ bigM N r S) : ¬ ℓ ∣ N :=
  fun h' => h (h'.trans (N_dvd_bigM S))

omit [NeZero N] [NeZero r] in
theorem not_dvd_of_dvd_N {ℓ R : ℕ} (hR : R ∣ N) (h : ¬ ℓ ∣ bigM N r S) : ¬ ℓ ∣ R :=
  fun h' => not_dvd_N S h (h'.trans hR)

omit [NeZero N] [NeZero r] in
theorem not_dvd_of_dvd_L {ℓ R : ℕ} (hR : R ∣ N * r) (h : ¬ ℓ ∣ bigM N r S) : ¬ ℓ ∣ R :=
  fun h' => not_dvd_L S h (h'.trans hR)

omit [NeZero N] [NeZero r] in
theorem not_mem_S {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ bigM N r S) : ℓ ∉ S := by
  intro hS
  apply h
  have hmem : ℓ ∈ S.filter (· ≠ 0) := Finset.mem_filter.mpr ⟨hS, hℓ.ne_zero⟩
  exact (Finset.dvd_prod_of_mem (fun s => s) hmem).trans (Dvd.intro_left _ rfl)

def E : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  Module.End.eigenspace (CuspForm.heckeTLin 2 hr hrN) (qCoeff g₀ r) ⊓
    ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ bigM N r S),
      Module.End.eigenspace (CuspForm.heckeTLin 2 hℓ (not_dvd_N S h)) (qCoeff g₀ ℓ)

def W : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) :=
  (E hr hrN S g₀).map (ι₁ r) ⊔ (E hr hrN S g₀).map (ιr r)

def V : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) :=
  ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ bigM N r S),
    Module.End.eigenspace (CuspForm.heckeTLin 2 hℓ (not_dvd_L S h)) (qCoeff g₀ ℓ)

omit [NeZero N] [NeZero r] in
theorem mem_E_iff (G : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    G ∈ E hr hrN S g₀ ↔ CuspForm.heckeTLin 2 hr hrN G = qCoeff g₀ r • G ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ bigM N r S),
        CuspForm.heckeTLin 2 hℓ (not_dvd_N S h) G = qCoeff g₀ ℓ • G := by
  simp only [E, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

omit [NeZero N] [NeZero r] in
theorem mem_V_iff (x : CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) :
    x ∈ V (r := r) S g₀ ↔ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ bigM N r S),
        CuspForm.heckeTLin 2 hℓ (not_dvd_L S h) x = qCoeff g₀ ℓ • x := by
  simp only [V, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

omit [NeZero N] [NeZero r] in

theorem heckeTLin_mem_V {x : CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2}
    (hx : x ∈ V (r := r) S g₀) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ N * r) :
    CuspForm.heckeTLin 2 hℓ hℓL x ∈ V (r := r) S g₀ := by
  rw [mem_V_iff] at hx ⊢
  intro ℓ' hℓ' h'
  have hc := (CuspForm.heckeTLin_comm 2 hℓ' (not_dvd_L S h') hℓ hℓL).eq
  have := LinearMap.congr_fun hc x
  simp only [Module.End.mul_apply] at this
  rw [this, hx ℓ' hℓ' h', map_smul]

theorem W_le_V : W hr hrN S g₀ ≤ V (r := r) S g₀ := by
  refine sup_le ?_ ?_
  · rintro _ ⟨G, hG, rfl⟩
    rw [SetLike.mem_coe, mem_E_iff] at hG
    rw [mem_V_iff]
    intro ℓ hℓ h
    rw [ι₁, CuspForm.heckeTLin_rescaleLin _ hℓ (not_dvd_L S h) (not_dvd_N S h), hG.2 ℓ hℓ h, map_smul]
  · rintro _ ⟨G, hG, rfl⟩
    rw [SetLike.mem_coe, mem_E_iff] at hG
    rw [mem_V_iff]
    intro ℓ hℓ h
    rw [ιr, CuspForm.heckeTLin_rescaleLin _ hℓ (not_dvd_L S h) (not_dvd_N S h), hG.2 ℓ hℓ h, map_smul]

theorem Q_eq_zero_of_mem_W {x : CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2}
    (hx : x ∈ W hr hrN S g₀) : Q r (qCoeff g₀ r) x = 0 := by
  rw [W, Submodule.mem_sup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨G, hG, rfl⟩ := hy
  obtain ⟨G', hG', rfl⟩ := hz
  rw [SetLike.mem_coe, mem_E_iff] at hG hG'
  rw [map_add, Q_ι₁ hr hrN G hG.1, Q_ιr hr hrN G' hG'.1, add_zero]

omit [NeZero r] in
include hg₀ hM₀N in

theorem rescale_mem_E {d : ℕ} (hdN : d * M₀ ∣ N) : rescaleLin hdN 2 g₀ ∈ E hr hrN S g₀ := by
  have hrM₀ : ¬ r ∣ M₀ := fun h => hrN (h.trans hM₀N)
  rw [mem_E_iff]
  refine ⟨?_, fun ℓ hℓ h => ?_⟩
  · rw [CuspForm.heckeTLin_rescaleLin hdN hr hrN hrM₀,
      CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M₀ g₀ hg₀.1 r hr hrM₀, map_smul]
  · rw [CuspForm.heckeTLin_rescaleLin hdN hℓ (not_dvd_N S h) (not_dvd_of_dvd_N S hM₀N h),
      CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M₀ g₀ hg₀.1 ℓ hℓ
        (not_dvd_of_dvd_N S hM₀N h), map_smul]

include hg₀ hM₀N in

theorem rescale_mem_W {d : ℕ} (hd : d * M₀ ∣ N * r) : rescaleLin hd 2 g₀ ∈ W hr hrN S g₀ := by
  by_cases hrd : r ∣ d
  · obtain ⟨d', rfl⟩ := hrd
    have hd' : d' * M₀ ∣ N := by
      refine Nat.dvd_of_mul_dvd_mul_right hr.pos ?_
      have e : d' * M₀ * r = r * d' * M₀ := by ring
      rwa [e]
    have hd'0 : d' ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_dvd_iff] at hd'
      exact NeZero.ne N hd'
    have heq : rescaleLin hd 2 g₀ = ιr r (rescaleLin hd' 2 g₀) := by
      apply DFunLike.coe_injective
      beta_reduce
      simp only [ιr, coe_rescaleLin_apply]
      rw [← SlashAction.slash_mul, heckeDiagMatrix_mul hd'0 hr.ne_zero, mul_comm d' r]
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (rescale_mem_E hr hrN S hM₀N g₀ hg₀ hd'))
  · have hrM₀ : ¬ r ∣ M₀ := fun h => hrN (h.trans hM₀N)
    have hcop : Nat.Coprime (d * M₀) r := by
      rw [Nat.Coprime, Nat.gcd_comm]
      refine (Nat.Prime.coprime_iff_not_dvd hr).mpr ?_
      intro h
      rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact hrd h
      · exact hrM₀ h
    have hdN : d * M₀ ∣ N := hcop.dvd_of_dvd_mul_right hd
    have heq : rescaleLin hd 2 g₀ = ι₁ r (rescaleLin hdN 2 g₀) := by
      apply DFunLike.coe_injective
      beta_reduce
      simp only [ι₁, coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one]
    rw [heq]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (rescale_mem_E hr hrN S hM₀N g₀ hg₀ hdN))

def S₀ : Set (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) :=
  {F | ∃ (R d : ℕ) (hdRM : d * R ∣ N * r) (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
    CuspForm.IsNewform g ∧ F = rescaleLin hdRM 2 g}

theorem heckeTLin_rescale_newform {R d : ℕ} (hdRM : d * R ∣ N * r)
    (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg : g.IsNewform)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ bigM N r S) :
    CuspForm.heckeTLin 2 hℓ (not_dvd_L S h) (rescaleLin hdRM 2 g) = qCoeff g ℓ • rescaleLin hdRM 2 g := by
  have hRL : R ∣ N * r := (dvd_mul_left R d).trans hdRM
  rw [CuspForm.heckeTLin_rescaleLin hdRM hℓ (not_dvd_L S h) (not_dvd_of_dvd_L S hRL h),
    CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul R g hg.1 ℓ hℓ
      (not_dvd_of_dvd_L S hRL h), map_smul]

include hg₀ hM₀N in

theorem mem_W_of_mem_span (T : Finset (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2))
    (hT : (↑T : Set _) ⊆ S₀ (N := N) (r := r)) :
    ∀ y ∈ Submodule.span ℂ (↑T : Set _), y ∈ V (r := r) S g₀ → y ∈ W hr hrN S g₀ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y hy _
    rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hy
    rw [hy]
    exact zero_mem _
  | insert F T hFT ih =>
    intro y hy hyV
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hy
    obtain ⟨a, z, hz, rfl⟩ := hy
    have hF : F ∈ S₀ (N := N) (r := r) := hT (by simp)
    have hT' : (↑T : Set _) ⊆ S₀ (N := N) (r := r) := fun x hx => hT (by simp [hx])
    obtain ⟨R, d, hdR, g, hg, rfl⟩ := hF
    have hRL : R ∣ N * r := (dvd_mul_left R d).trans hdR
    by_cases hgood : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ bigM N r S → qCoeff g ℓ = qCoeff g₀ ℓ
    ·
      obtain ⟨hRM, hq⟩ := CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
        (M := bigM N r S) hg hg₀ (hRL.trans (L_dvd_bigM S)) (hM₀N.trans (N_dvd_bigM S)) hgood
      have hFW : rescaleLin hdR 2 g ∈ W hr hrN S g₀ := by
        subst hRM
        have hgg : g = g₀ :=
          CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq hg.1 hg₀.1 fun p _ => hq p
        subst hgg
        exact rescale_mem_W hr hrN S hM₀N g hg hdR
      have hzV : z ∈ V (r := r) S g₀ := by
        have h := sub_mem hyV (Submodule.smul_mem _ a (W_le_V hr hrN S g₀ hFW))
        rwa [add_sub_cancel_left] at h
      exact add_mem (Submodule.smul_mem _ a hFW) (ih hT' z hz hzV)
    ·
      push Not at hgood
      obtain ⟨ℓ, hℓ, hℓM, hne⟩ := hgood
      set Tℓ := CuspForm.heckeTLin (N := N * r) 2 hℓ (not_dvd_L S hℓM) with hTℓ
      set b : ℂ := qCoeff g ℓ with hb
      have hDF : Tℓ (rescaleLin hdR 2 g) = b • rescaleLin hdR 2 g :=
        heckeTLin_rescale_newform S hdR g hg hℓ hℓM

      have hDz : Tℓ z - b • z ∈ Submodule.span ℂ (↑T : Set _) := by
        refine Submodule.span_induction (p := fun w _ => Tℓ w - b • w ∈ Submodule.span ℂ (↑T : Set _))
          ?_ ?_ ?_ ?_ hz
        · intro w hw
          obtain ⟨R', d', hdR', g', hg', rfl⟩ := hT' hw
          rw [heckeTLin_rescale_newform S hdR' g' hg' hℓ hℓM, ← sub_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hw)
        · simp
        · intro w w' _ _ hw hw'
          have e : Tℓ (w + w') - b • (w + w') = (Tℓ w - b • w) + (Tℓ w' - b • w') := by
            rw [map_add]; module
          rw [e]
          exact add_mem hw hw'
        · intro c w _ hw
          have e : Tℓ (c • w) - b • (c • w) = c • (Tℓ w - b • w) := by
            rw [map_smul]; module
          rw [e]
          exact Submodule.smul_mem _ c hw
      have hy_eq : Tℓ (a • rescaleLin hdR 2 g + z) - b • (a • rescaleLin hdR 2 g + z) =
          Tℓ z - b • z := by
        rw [map_add, map_smul, hDF]; module
      have hDyV : Tℓ (a • rescaleLin hdR 2 g + z) - b • (a • rescaleLin hdR 2 g + z) ∈
          V (r := r) S g₀ :=
        sub_mem (heckeTLin_mem_V S g₀ hyV hℓ (not_dvd_L S hℓM)) (Submodule.smul_mem _ b hyV)
      have hDyW : Tℓ (a • rescaleLin hdR 2 g + z) - b • (a • rescaleLin hdR 2 g + z) ∈
          W hr hrN S g₀ := by
        rw [hy_eq] at hDyV ⊢
        exact ih hT' _ hDz hDyV
      have hTy : Tℓ (a • rescaleLin hdR 2 g + z) = qCoeff g₀ ℓ • (a • rescaleLin hdR 2 g + z) :=
        (mem_V_iff S g₀ _).mp hyV ℓ hℓ hℓM
      rw [hTy, ← sub_smul] at hDyW
      exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne.symm)).mp hDyW

end Old

end OldSpaceSol
p2m_reactivate "P2MW.S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform.OldSpaceSol"

end
p2m_reactivate "P2MW.S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform.OldSpaceSol"

open OldSpaceSol ModularForm ModularFormClass FreyPackage.ModMCarrier in
theorem solution
    (N r : ℕ) [NeZero N] (hr : r.Prime) (hrN : ¬ r ∣ N) (S : Finset ℕ)
    (M₀ : ℕ) (hM₀N : M₀ ∣ N)
    (g₀ : CuspForm (CongruenceSubgroup.Gamma0 M₀) 2) (hg₀ : g₀.IsNewform)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) (hf : f ≠ 0)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNr : ¬ ℓ ∣ N * r), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓNr f = ModularFormClass.qCoeff g₀ ℓ • f)
    (u : ℂ)
    (hu : haveI : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) hr.ne_zero⟩
      CuspForm.heckeULin 2 (dvd_mul_left r N) f = u • f) :
    u ^ 2 - ModularFormClass.qCoeff g₀ r * u + r = 0 := by
  classical
  haveI : NeZero r := ⟨hr.ne_zero⟩

  have hfV : f ∈ V (r := r) S g₀ := by
    rw [mem_V_iff]
    intro ℓ hℓ h
    exact hT ℓ hℓ (not_dvd_L S h) (not_mem_S S hℓ h)

  have hfspan : f ∈ Submodule.span ℂ (S₀ (N := N) (r := r)) := by
    have h := CuspForm.span_rescaleLin_isNewform_eq_top (N * r)
    have hf' : f ∈ (⊤ : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2)) :=
      Submodule.mem_top
    rw [← h] at hf'
    exact hf'
  obtain ⟨T, hT₀, hfT⟩ := Submodule.mem_span_finite_of_mem_span hfspan

  have hfW : f ∈ W hr hrN S g₀ := mem_W_of_mem_span hr hrN S hM₀N g₀ hg₀ T hT₀ f hfT hfV

  have hQ := Q_eq_zero_of_mem_W hr hrN S g₀ hfW
  have hu' : Ur r f = u • f := hu
  have hQ' : Q r (qCoeff g₀ r) f = (u ^ 2 - qCoeff g₀ r * u + r) • f := by
    simp only [Q, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, hu', map_smul]
    module
  rw [hQ'] at hQ
  exact (smul_eq_zero.mp hQ).resolve_right hf

end S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
end P2MW
export P2MW.S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform (solution)
