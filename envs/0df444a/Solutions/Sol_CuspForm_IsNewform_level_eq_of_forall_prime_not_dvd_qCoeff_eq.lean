-- Prove2me | solution 1 for CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2ebdf1d5-92eb-5a16-b627-7f4efdf46382

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_span_heckeTLin_eigen_eq_top
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero
import Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_IsNewform_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd_of_dvd
import Theorems.Thm_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_level_eq_of_forall_prime_not_dvd_qCoeff_eq
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold

namespace NewformLevelRigidity

abbrev S (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma0 N) 2

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

theorem qCoeff_zero' (M n : ℕ) [NeZero M] :
    ModularFormClass.qCoeff (0 : CuspForm (CongruenceSubgroup.Gamma0 M) 2) n = 0 := by
  rw [← qCoeffLin_apply, map_zero]

theorem qCoeff_sub_smul {M : ℕ} [NeZero M] (A B : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (c : ℂ)
    (n : ℕ) : ModularFormClass.qCoeff (⇑(A - c • B)) n
      = ModularFormClass.qCoeff (⇑A) n - c * ModularFormClass.qCoeff (⇑B) n := by
  rw [← qCoeffLin_apply, map_sub, _root_.map_smul, qCoeffLin_apply, qCoeffLin_apply, smul_eq_mul]

theorem rescaleLin_apply' {d R M : ℕ} [NeZero M] [NeZero R] (hdRM : d * R ∣ M) (hd : d ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (τ : ℍ) :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 f τ = (d : ℂ) * f (heckeDiagMatrix d • τ) := by
  rw [show FreyPackage.ModMCarrier.rescaleLin hdRM 2 f τ
      = (⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)) τ from rfl,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, slash_heckeDiagMatrix_apply 2 hd]
  norm_num

theorem qCoeff_rescaleLin {d R M : ℕ} [NeZero M] [NeZero R] (hdRM : d * R ∣ M) (hd : d ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) n
      = if d ∣ n then (d : ℂ) * ModularFormClass.qCoeff f (n / d) else 0 := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hfun : (fun τ : ℍ => f (heckeDiagMatrix d • τ))
      = (d : ℂ)⁻¹ • ⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) := by
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, rescaleLin_apply' hdRM hd, ← mul_assoc, inv_mul_cancel₀ hdC,
      one_mul]
  have h1 := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f (hΓ R) hd n
  rw [hfun] at h1
  have h2 : ModularFormClass.qCoeff ((d : ℂ)⁻¹ • ⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)) n
      = (d : ℂ)⁻¹ * ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) n := by
    unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul, smul_eq_mul]
  rw [h2] at h1
  have h3 := congrArg (fun z : ℂ => (d : ℂ) * z) h1
  rw [← mul_assoc, mul_inv_cancel₀ hdC, one_mul] at h3
  rw [h3]
  split_ifs <;> simp

theorem qCoeff_rescaleLin_one {R M : ℕ} [NeZero M] [NeZero R] (h1 : 1 * R ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin h1 2 f) n = ModularFormClass.qCoeff f n := by
  rw [qCoeff_rescaleLin h1 one_ne_zero, if_pos (one_dvd n), Nat.cast_one, one_mul, Nat.div_one]

theorem not_dvd_of_dvd {N L ℓ : ℕ} (hNL : N ∣ L) (h : ¬ ℓ ∣ L) : ¬ ℓ ∣ N :=
  fun h' => h (h'.trans hNL)

def E (L : ℕ) (lam : ℕ → ℂ) {N : ℕ} (hNL : N ∣ L) : Submodule ℂ (S N) where
  carrier := {v | ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L),
    CuspForm.heckeTLin 2 hℓ (not_dvd_of_dvd hNL hℓL) v = lam ℓ • v}
  add_mem' := by
    intro v w hv hw ℓ hℓ hℓL
    rw [map_add, hv ℓ hℓ hℓL, hw ℓ hℓ hℓL, smul_add]
  zero_mem' := by
    intro ℓ hℓ hℓL
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c v hv ℓ hℓ hℓL
    rw [map_smul, hv ℓ hℓ hℓL, smul_comm]

theorem mem_E {L : ℕ} {lam : ℕ → ℂ} {N : ℕ} (hNL : N ∣ L) (v : S N) :
    v ∈ E L lam hNL ↔ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L),
      CuspForm.heckeTLin 2 hℓ (not_dvd_of_dvd hNL hℓL) v = lam ℓ • v := Iff.rfl

structure Kill (L : ℕ) (lam : ℕ → ℂ) where
  ℓ : ℕ
  hℓ : ℓ.Prime
  hℓL : ¬ ℓ ∣ L
  μ : ℂ
  hμ : μ ≠ lam ℓ

variable {L : ℕ} {lam : ℕ → ℂ}

def factor {N : ℕ} (hNL : N ∣ L) (κ : Kill L lam) : Module.End ℂ (S N) :=
  (lam κ.ℓ - κ.μ)⁻¹ •
    (CuspForm.heckeTLin 2 κ.hℓ (not_dvd_of_dvd hNL κ.hℓL) - κ.μ • (LinearMap.id : Module.End ℂ (S N)))

def proj {N : ℕ} (hNL : N ∣ L) (ks : List (Kill L lam)) : Module.End ℂ (S N) :=
  (ks.map (factor hNL)).prod

theorem proj_nil {N : ℕ} (hNL : N ∣ L) : proj hNL ([] : List (Kill L lam)) = 1 := rfl

theorem proj_cons {N : ℕ} (hNL : N ∣ L) (κ : Kill L lam) (ks : List (Kill L lam)) :
    proj hNL (κ :: ks) = factor hNL κ * proj hNL ks := by
  rw [proj, List.map_cons, List.prod_cons, proj]

def IsEig {N : ℕ} (hNL : N ∣ L) (c : ℕ → ℂ) (v : S N) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L),
    CuspForm.heckeTLin 2 hℓ (not_dvd_of_dvd hNL hℓL) v = c ℓ • v

theorem factor_apply_of_isEig {N : ℕ} (hNL : N ∣ L) (κ : Kill L lam) {c : ℕ → ℂ} {v : S N}
    (hv : IsEig hNL c v) :
    factor hNL κ v = ((lam κ.ℓ - κ.μ)⁻¹ * (c κ.ℓ - κ.μ)) • v := by
  rw [factor, LinearMap.smul_apply, LinearMap.sub_apply, hv κ.ℓ κ.hℓ κ.hℓL, LinearMap.smul_apply,
    LinearMap.id_apply, ← sub_smul, smul_smul]

theorem proj_apply_of_isEig {N : ℕ} (hNL : N ∣ L) (ks : List (Kill L lam)) {c : ℕ → ℂ} {v : S N}
    (hv : IsEig hNL c v) :
    ∃ s : ℂ, proj hNL ks v = s • v := by
  induction ks with
  | nil => exact ⟨1, by rw [proj_nil, Module.End.one_apply, one_smul]⟩
  | cons κ ks ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨(lam κ.ℓ - κ.μ)⁻¹ * (c κ.ℓ - κ.μ) * s, ?_⟩
    rw [proj_cons, Module.End.mul_apply, hs, map_smul, factor_apply_of_isEig hNL κ hv, smul_smul,
      mul_comm s]

theorem proj_apply_of_mem_E {N : ℕ} (hNL : N ∣ L) (ks : List (Kill L lam)) {v : S N}
    (hv : v ∈ E L lam hNL) : proj hNL ks v = v := by
  induction ks with
  | nil => rw [proj_nil, Module.End.one_apply]
  | cons κ ks ih =>
    rw [proj_cons, Module.End.mul_apply, ih, factor_apply_of_isEig hNL κ (c := lam) hv,
      inv_mul_cancel₀ (sub_ne_zero.mpr κ.hμ.symm), one_smul]

theorem factor_apply_eq_zero {N : ℕ} (hNL : N ∣ L) (κ : Kill L lam) {c : ℕ → ℂ} {v : S N}
    (hv : IsEig hNL c v) (hc : c κ.ℓ = κ.μ) : factor hNL κ v = 0 := by
  rw [factor_apply_of_isEig hNL κ hv, hc, sub_self, mul_zero, zero_smul]

theorem proj_apply_eq_zero_of_mem {N : ℕ} (hNL : N ∣ L) {ks : List (Kill L lam)} {κ : Kill L lam}
    (hκ : κ ∈ ks) {c : ℕ → ℂ} {v : S N} (hv : IsEig hNL c v) (hc : c κ.ℓ = κ.μ) :
    proj hNL ks v = 0 := by
  induction ks with
  | nil => exact absurd hκ (by simp)
  | cons κ' ks ih =>
    rw [proj_cons, Module.End.mul_apply]
    rcases List.mem_cons.mp hκ with h | h
    · subst h
      obtain ⟨s, hs⟩ := proj_apply_of_isEig hNL ks hv
      rw [hs, map_smul, factor_apply_eq_zero hNL κ hv hc, smul_zero]
    · rw [ih h, map_zero]

theorem factor_rescaleLin {N N' d : ℕ} [NeZero N'] (hNL : N ∣ L) (hN'L : N' ∣ L) (hdN : d * N ∣ N')
    (κ : Kill L lam) (v : S N) :
    factor hN'L κ (FreyPackage.ModMCarrier.rescaleLin hdN 2 v)
      = FreyPackage.ModMCarrier.rescaleLin hdN 2 (factor hNL κ v) := by
  simp only [factor, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub]
  rw [CuspForm.heckeTLin_rescaleLin hdN κ.hℓ (not_dvd_of_dvd hN'L κ.hℓL) (not_dvd_of_dvd hNL κ.hℓL)]

theorem proj_rescaleLin {N N' d : ℕ} [NeZero N'] (hNL : N ∣ L) (hN'L : N' ∣ L) (hdN : d * N ∣ N')
    (ks : List (Kill L lam)) (v : S N) :
    proj hN'L ks (FreyPackage.ModMCarrier.rescaleLin hdN 2 v)
      = FreyPackage.ModMCarrier.rescaleLin hdN 2 (proj hNL ks v) := by
  induction ks generalizing v with
  | nil => rw [proj_nil, proj_nil, Module.End.one_apply, Module.End.one_apply]
  | cons κ ks ih =>
    rw [proj_cons, proj_cons, Module.End.mul_apply, Module.End.mul_apply, ih, factor_rescaleLin hNL hN'L]

section build

variable {N : ℕ} [NeZero N] (hNL : N ∣ L)

def eigSet (N : ℕ) : Set (S N) :=
  {v | ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN v = c • v}

theorem exists_finset_span : ∃ s : Finset (S N), ↑s ⊆ eigSet N ∧ Submodule.span ℂ (↑s : Set (S N)) = ⊤ := by
  haveI := CuspForm.finiteDimensional_Gamma0 N 2
  have htop : Submodule.span ℂ (eigSet N) = ⊤ := CuspForm.span_heckeTLin_eigen_eq_top N
  have hfg : (Submodule.span ℂ (eigSet N)).FG := by rw [htop]; exact Module.Finite.fg_top
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (eigSet N)).mp hfg
  exact ⟨s, hs, by rw [← hspan, htop]⟩

open Classical in

def sys (v : S N) : ℕ → ℂ := fun ℓ =>
  if h : ∃ (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN v = c • v then
    h.2.2.choose else 0

omit [NeZero N] in
include hNL in
theorem isEig_sys {v : S N} (hv : v ∈ eigSet N) : IsEig hNL (sys v) v := by
  intro ℓ hℓ hℓL
  have hℓN : ¬ ℓ ∣ N := not_dvd_of_dvd hNL hℓL
  have h : ∃ (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN v = c • v :=
    ⟨hℓ, hℓN, hv ℓ hℓ hℓN⟩
  show CuspForm.heckeTLin 2 hℓ hℓN v = sys v ℓ • v
  simp only [sys, dif_pos h]
  exact h.2.2.choose_spec

omit [NeZero N] in

theorem exists_kill (s : Finset (S N)) (hs : ↑s ⊆ eigSet N) :
    ∃ ks : List (Kill L lam), ∀ v ∈ s,
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → sys v ℓ = lam ℓ) ∨ proj hNL ks v = 0 := by
  classical

  let dat : S N → Option (Kill L lam) := fun v =>
    if h : ∃ ℓ : ℕ, ∃ (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L), sys v ℓ ≠ lam ℓ then
      some ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, sys v h.choose, h.choose_spec.2.2⟩
    else none
  refine ⟨s.toList.filterMap dat, fun v hv => ?_⟩
  by_cases h : ∃ ℓ : ℕ, ∃ (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L), sys v ℓ ≠ lam ℓ
  · right
    have hmem : (⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, sys v h.choose, h.choose_spec.2.2⟩ :
        Kill L lam) ∈ s.toList.filterMap dat := by
      rw [List.mem_filterMap]
      exact ⟨v, Finset.mem_toList.mpr hv, by simp only [dat, dif_pos h]⟩
    exact proj_apply_eq_zero_of_mem hNL hmem (isEig_sys hNL (hs hv)) rfl
  · left
    intro ℓ hℓ hℓL
    by_contra hne
    exact h ⟨ℓ, hℓ, hℓL, hne⟩

omit [NeZero N] in

theorem proj_mem_E (s : Finset (S N)) (hs : ↑s ⊆ eigSet N)
    (hspan : Submodule.span ℂ (↑s : Set (S N)) = ⊤) (ks : List (Kill L lam))
    (hks : ∀ v ∈ s, (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → sys v ℓ = lam ℓ) ∨ proj hNL ks v = 0)
    (w : S N) : proj hNL ks w ∈ E L lam hNL := by
  have hw : w ∈ Submodule.span ℂ (↑s : Set (S N)) := by rw [hspan]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ => proj hNL ks x ∈ E L lam hNL) ?_ ?_ ?_ ?_ hw
  · intro v hv
    change proj hNL ks v ∈ E L lam hNL
    rcases hks v hv with h | h
    ·
      have hvE : v ∈ E L lam hNL := by
        intro ℓ hℓ hℓL
        rw [isEig_sys hNL (hs hv) ℓ hℓ hℓL, h ℓ hℓ hℓL]
      rw [proj_apply_of_mem_E hNL ks hvE]
      exact hvE
    · rw [h]; exact Submodule.zero_mem _
  · change proj hNL ks 0 ∈ E L lam hNL
    rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    change proj hNL ks (x + y) ∈ E L lam hNL
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    change proj hNL ks (c • x) ∈ E L lam hNL
    rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem exists_proj_mem_E : ∃ ks : List (Kill L lam), ∀ w : S N, proj hNL ks w ∈ E L lam hNL := by
  obtain ⟨s, hs, hspan⟩ := exists_finset_span (N := N)
  obtain ⟨ks, hks⟩ := exists_kill hNL s hs (lam := lam)
  exact ⟨ks, proj_mem_E hNL s hs hspan ks hks⟩

end build

theorem proj_eig_dichotomy {N : ℕ} (hNL : N ∣ L) (ks : List (Kill L lam))
    (hE : ∀ w : S N, proj hNL ks w ∈ E L lam hNL) {c : ℕ → ℂ} {v : S N} (hv : IsEig hNL c v) :
    proj hNL ks v = 0 ∨ v ∈ E L lam hNL := by
  obtain ⟨s, hs⟩ := proj_apply_of_isEig hNL ks hv
  by_cases hs0 : s = 0
  · left; rw [hs, hs0, zero_smul]
  · right
    have hmem : s • v ∈ E L lam hNL := hs ▸ hE v
    have := Submodule.smul_mem _ s⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this

theorem heckeDiagMatrix_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    heckeDiagMatrix (a * b) = heckeDiagMatrix a * heckeDiagMatrix b := by
  apply Units.ext
  rw [Units.val_mul, val_heckeDiagMatrix (Nat.mul_ne_zero ha hb), val_heckeDiagMatrix ha,
    val_heckeDiagMatrix hb]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rescaleLin_rescaleLin {a b R M₁ M : ℕ} [NeZero R] [NeZero M₁] [NeZero M] (ha : a ≠ 0)
    (hb : b ≠ 0) (hbR : b * R ∣ M₁) (haM : a * M₁ ∣ M) (hab : a * b * R ∣ M)
    (x : S R) :
    FreyPackage.ModMCarrier.rescaleLin haM 2 (FreyPackage.ModMCarrier.rescaleLin hbR 2 x)
      = FreyPackage.ModMCarrier.rescaleLin hab 2 x := by
  refine DFunLike.coe_injective ?_
  show ⇑(FreyPackage.ModMCarrier.rescaleLin haM 2 (FreyPackage.ModMCarrier.rescaleLin hbR 2 x))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin hab 2 x)
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, ← SlashAction.slash_mul, ← heckeDiagMatrix_mul hb ha,
    mul_comm b a]

theorem rescaleLin_congr {d₁ d₂ R M : ℕ} [NeZero M] (hd : d₁ = d₂) (h₁ : d₁ * R ∣ M) (h₂ : d₂ * R ∣ M)
    (x : S R) :
    FreyPackage.ModMCarrier.rescaleLin h₁ 2 x = FreyPackage.ModMCarrier.rescaleLin h₂ 2 x := by
  subst hd; rfl

theorem qCoeff_sub' {M : ℕ} [NeZero M] (A B : S M) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(A - B)) n = ModularFormClass.qCoeff (⇑A) n - ModularFormClass.qCoeff (⇑B) n := by
  rw [← qCoeffLin_apply, map_sub, qCoeffLin_apply, qCoeffLin_apply]

def J (q N : ℕ) [NeZero N] : Submodule ℂ (S N) :=
  Submodule.span ℂ {F | ∃ (p N' : ℕ) (h : p * N' ∣ N) (x : S N'),
    p.Prime ∧ p ≠ q ∧ p * N' = N ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 x}

def Tw (q N : ℕ) [NeZero N] {R' : ℕ} (g' : S R') : Submodule ℂ (S N) :=
  Submodule.span ℂ {F | ∃ (i : ℕ) (h : q ^ i * R' ∣ N),
    1 ≤ i ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 g'}

theorem rescaleLin_mem_J {q N p N' : ℕ} [NeZero N] (h : p * N' ∣ N) (x : S N') (hp : p.Prime)
    (hpq : p ≠ q) (hpN : p * N' = N) : FreyPackage.ModMCarrier.rescaleLin h 2 x ∈ J q N :=
  Submodule.subset_span ⟨p, N', h, x, hp, hpq, hpN, rfl⟩

theorem rescaleLin_mem_Tw {q N R' : ℕ} [NeZero N] (g' : S R') {i : ℕ} (h : q ^ i * R' ∣ N)
    (hi : 1 ≤ i) : FreyPackage.ModMCarrier.rescaleLin h 2 g' ∈ Tw q N g' :=
  Submodule.subset_span ⟨i, h, hi, rfl⟩

variable {L : ℕ} {lam : ℕ → ℂ}

theorem proj_append {N : ℕ} (hNL : N ∣ L) (ks₁ ks₂ : List (Kill L lam)) :
    proj hNL (ks₁ ++ ks₂) = proj hNL ks₁ * proj hNL ks₂ := by
  rw [proj, List.map_append, List.prod_append, proj, proj]

theorem exists_ks_list [NeZero L] (ns : List ℕ) :
    ∃ ks : List (Kill L lam), ∀ N ∈ ns, ∀ (hNL : N ∣ L) (_ : NeZero N) (w : S N),
      proj hNL ks w ∈ E L lam hNL := by
  induction ns with
  | nil => exact ⟨[], fun N hN => absurd hN (by simp)⟩
  | cons n ns ih =>
    obtain ⟨ks', hks'⟩ := ih
    by_cases hn : n ∣ L ∧ n ≠ 0
    · haveI : NeZero n := ⟨hn.2⟩
      obtain ⟨ksn, hksn⟩ := exists_proj_mem_E (L := L) (lam := lam) (N := n) hn.1
      refine ⟨ks' ++ ksn, fun N hN hNL hN0 w => ?_⟩
      rw [proj_append, Module.End.mul_apply]
      rcases List.mem_cons.mp hN with h | h
      · subst h
        rw [proj_apply_of_mem_E hNL ks' (hksn w)]
        exact hksn w
      · exact hks' N h hNL hN0 (proj hNL ksn w)
    · refine ⟨ks', fun N hN hNL hN0 w => ?_⟩
      rcases List.mem_cons.mp hN with h | h
      · subst h
        exact absurd ⟨hNL, hN0.ne⟩ hn
      · exact hks' N h hNL hN0 w

theorem exists_ks [NeZero L] :
    ∃ ks : List (Kill L lam), ∀ (N : ℕ) (hNL : N ∣ L) (_ : NeZero N) (w : S N),
      proj hNL ks w ∈ E L lam hNL := by
  obtain ⟨ks, hks⟩ := exists_ks_list (L := L) (lam := lam) (List.range (L + 1))
  refine ⟨ks, fun N hNL hN0 w => hks N ?_ hNL hN0 w⟩
  rw [List.mem_range]
  have : N ≤ L := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hNL
  omega

theorem isEig_of_isNewform {N : ℕ} [NeZero N] (hNL : N ∣ L) {h : S N} (hh : CuspForm.IsNewform h) :
    IsEig hNL (fun ℓ => ModularFormClass.qCoeff h ℓ) h := by
  intro ℓ hℓ hℓL
  exact (((CuspForm.isNormalizedEigenform_iff_heckeTLin h).mp hh.1).2 ℓ hℓ).1 (not_dvd_of_dvd hNL hℓL)

theorem qCoeff_eq_of_mem_E {N : ℕ} [NeZero N] (hNL : N ∣ L) {h : S N} (hh : CuspForm.IsNewform h)
    (hE : h ∈ E L lam hNL) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) :
    ModularFormClass.qCoeff h ℓ = lam ℓ := by
  have h1 := isEig_of_isNewform hNL hh ℓ hℓ hℓL
  have h2 := hE ℓ hℓ hℓL
  rw [h1] at h2
  exact smul_left_injective ℂ hh.ne_zero h2

theorem decomp [NeZero L] {q R R' : ℕ} (hq : q.Prime) {g : S R} {g' : S R'}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g') (hR : R ∣ L) (hR' : R' ∣ L) (hqL : q ∣ L)
    (hagree : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ)
    (huniq : ∀ (R₁ : ℕ) (h' : S R₁), CuspForm.IsNewform h' → q * R₁ ∣ L →
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → ModularFormClass.qCoeff h' ℓ = ModularFormClass.qCoeff g' ℓ) →
      R₁ = R')
    (h1 : 1 * R ∣ L) (h1' : 1 * R' ∣ L) :
    FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g'
      ∈ Tw q L g' ⊔ J q L := by
  haveI : NeZero R := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) hR⟩
  haveI : NeZero R' := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) hR'⟩
  have hLL : L ∣ L := dvd_rfl
  set lam : ℕ → ℂ := fun ℓ => ModularFormClass.qCoeff g' ℓ with hlam
  set d : S L := FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g'
    with hd

  have hdE : d ∈ E L lam hLL := by
    intro ℓ hℓ hℓL
    have hℓR : ¬ ℓ ∣ R := not_dvd_of_dvd hR hℓL
    have hℓR' : ¬ ℓ ∣ R' := not_dvd_of_dvd hR' hℓL
    have eg := (((CuspForm.isNormalizedEigenform_iff_heckeTLin g).mp hg.1).2 ℓ hℓ).1 hℓR
    have eg' := (((CuspForm.isNormalizedEigenform_iff_heckeTLin g').mp hg'.1).2 ℓ hℓ).1 hℓR'
    rw [hd, map_sub, CuspForm.heckeTLin_rescaleLin h1 hℓ (not_dvd_of_dvd hLL hℓL) hℓR,
      CuspForm.heckeTLin_rescaleLin h1' hℓ (not_dvd_of_dvd hLL hℓL) hℓR', eg, eg', map_smul, map_smul,
      hagree ℓ hℓ hℓL, smul_sub]

  have hL1 : 1 < L := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hqL
    have := hq.one_lt
    omega
  have hcop : ∀ n : ℕ, Nat.Coprime n L → ModularFormClass.qCoeff d n = 0 := by
    intro n hn
    rw [hd, qCoeff_sub', qCoeff_rescaleLin_one, qCoeff_rescaleLin_one,
      hg.1.qCoeff_eq_of_coprime_of_forall_prime_not_dvd hg'.1 hR hR' hagree hn, sub_self]
  have hX3 := CuspForm.mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero (m := L) hL1 hcop

  obtain ⟨ks, hks⟩ := exists_ks (L := L) (lam := lam)

  have hdproj : proj hLL ks d = d := proj_apply_of_mem_E hLL ks hdE
  rw [← hdproj]
  have himg := Submodule.mem_map_of_mem (f := proj hLL ks) hX3
  rw [Submodule.map_span] at himg
  refine (Submodule.span_le.mpr ?_) himg
  rintro _ ⟨F, ⟨p, R'', hpR'', fq, hp, hpRL, rfl⟩, rfl⟩
  rw [SetLike.mem_coe]
  have hR''L : R'' ∣ L := ⟨p, by rw [← hpRL, mul_comm]⟩
  haveI : NeZero R'' := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) hR''L⟩
  show proj hLL ks (FreyPackage.ModMCarrier.rescaleLin hpR'' 2 fq) ∈ Tw q L g' ⊔ J q L
  rw [proj_rescaleLin hR''L hLL hpR'' ks fq]
  by_cases hpq : p = q
  · subst hpq

    set e := proj hR''L ks fq with he
    have heE : e ∈ E L lam hR''L := hks R'' hR''L inferInstance fq

    let Φ : S R'' →ₗ[ℂ] S L := (FreyPackage.ModMCarrier.rescaleLin hpR'' 2).comp (proj hR''L ks)
    have hgen : Submodule.span ℂ {F : S R'' | ∃ (R₁ dd : ℕ) (hdd : dd * R₁ ∣ R'') (h' : S R₁),
        CuspForm.IsNewform h' ∧ F = FreyPackage.ModMCarrier.rescaleLin hdd 2 h'}
          ≤ (Tw p L g' ⊔ J p L).comap Φ := by
      refine Submodule.span_le.mpr ?_
      rintro F ⟨R₁, dd, hdd, h', hh', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show FreyPackage.ModMCarrier.rescaleLin hpR'' 2
          (proj hR''L ks (FreyPackage.ModMCarrier.rescaleLin hdd 2 h')) ∈ Tw p L g' ⊔ J p L
      have hR₁R'' : R₁ ∣ R'' := (Dvd.intro_left dd rfl).trans hdd
      have hR₁L : R₁ ∣ L := hR₁R''.trans hR''L
      haveI : NeZero R₁ := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne L) hR₁L⟩
      rw [proj_rescaleLin hR₁L hR''L hdd ks h']
      rcases proj_eig_dichotomy hR₁L ks (fun w => hks R₁ hR₁L inferInstance w) (isEig_of_isNewform hR₁L hh')
        with h0 | hE
      · rw [h0, map_zero, map_zero]; exact Submodule.zero_mem _
      ·
        rw [proj_apply_of_mem_E hR₁L ks hE]
        have hagree' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L →
            ModularFormClass.qCoeff h' ℓ = ModularFormClass.qCoeff g' ℓ := fun ℓ hℓ hℓL =>
          qCoeff_eq_of_mem_E hR₁L hh' hE hℓ hℓL
        have hR₁eq : R₁ = R' := huniq R₁ h' hh' ((mul_dvd_mul_left p hR₁R'').trans ⟨1, by rw [hpRL, mul_one]⟩)
          hagree'
        subst hR₁eq
        have hh'g' : h' = g' := hh'.eq_of_forall_qCoeff_eq hg' hR' hagree'
        subst hh'g'

        have hdd0 : dd ≠ 0 := fun h0 => by
          rw [h0, zero_mul] at hdd; exact NeZero.ne R'' (Nat.eq_zero_of_zero_dvd hdd)
        obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hdd0 p hp.one_lt.ne'
        have hu0 : u ≠ 0 := fun h0 => hdd0 (by rw [h0, mul_zero])
        have htot : p * (p ^ a * u) * R₁ ∣ L := by
          rw [← hpRL, mul_assoc]; exact mul_dvd_mul_left p hdd
        rw [rescaleLin_rescaleLin hp.ne_zero hdd0 hdd hpR'' htot h']
        by_cases hu1 : u = 1
        ·
          subst hu1
          have hpow : p ^ (a + 1) * R₁ ∣ L := by
            have : p * (p ^ a * 1) = p ^ (a + 1) := by rw [mul_one, pow_succ, mul_comm]
            rw [← this]; exact htot
          rw [rescaleLin_congr (by rw [mul_one, pow_succ, mul_comm]) htot hpow h']
          exact Submodule.mem_sup_left (rescaleLin_mem_Tw h' hpow (Nat.succ_le_succ (Nat.zero_le a)))
        ·
          obtain ⟨p', hp', hp'u⟩ := Nat.exists_prime_and_dvd hu1
          have hp'p : p' ≠ p := fun h0 => hu (h0 ▸ hp'u)
          obtain ⟨u', rfl⟩ := hp'u
          have hp'L : p' ∣ L := by
            refine Dvd.dvd.trans ?_ htot
            exact Dvd.intro (p * p ^ a * u' * R₁) (by ring)
          obtain ⟨N', hN'⟩ := hp'L
          haveI : NeZero N' := ⟨fun h0 => NeZero.ne L (by rw [hN', h0, mul_zero])⟩
          have hp'N' : p' * N' ∣ L := ⟨1, by rw [hN', mul_one]⟩
          have hrest : p ^ (a + 1) * u' * R₁ ∣ N' := by
            refine Nat.dvd_of_mul_dvd_mul_left hp'.pos ?_
            rw [← hN']
            have : p' * (p ^ (a + 1) * u' * R₁) = p * (p ^ a * (p' * u')) * R₁ := by ring
            rw [this]; exact htot
          have htot' : p' * (p ^ (a + 1) * u') * R₁ ∣ L := by
            have : p' * (p ^ (a + 1) * u') * R₁ = p * (p ^ a * (p' * u')) * R₁ := by ring
            rw [this]; exact htot
          rw [rescaleLin_congr (by ring) htot htot' h',
            ← rescaleLin_rescaleLin hp'.ne_zero (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero)
              (fun h0 => hu0 (by rw [h0, mul_zero]))) hrest hp'N' htot' h']
          exact Submodule.mem_sup_right (rescaleLin_mem_J hp'N' _ hp' hp'p hN'.symm)

    have hetop : e ∈ Submodule.span ℂ {F : S R'' | ∃ (R₁ dd : ℕ) (hdd : dd * R₁ ∣ R'') (h' : S R₁),
        CuspForm.IsNewform h' ∧ F = FreyPackage.ModMCarrier.rescaleLin hdd 2 h'} := by
      rw [CuspForm.span_rescaleLin_isNewform_eq_top R'']; exact Submodule.mem_top
    have hmem := hgen hetop
    rw [Submodule.mem_comap] at hmem
    have hpe : proj hR''L ks e = e := proj_apply_of_mem_E hR''L ks heE
    show FreyPackage.ModMCarrier.rescaleLin hpR'' 2 e ∈ Tw p L g' ⊔ J p L
    rw [← hpe]
    exact hmem
  · exact Submodule.mem_sup_right (rescaleLin_mem_J hpR'' _ hp hpq hpRL)

def P (L' : ℕ) : Prop :=
  L' ≠ 0 → ∀ (A B : ℕ) (h : S A) (h' : S B), CuspForm.IsNewform h → CuspForm.IsNewform h' →
    A ∣ L' → B ∣ L' →
    (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L' → ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff h' ℓ) →
    A = B

theorem agree_of_dvd {L L' A B : ℕ} (hL0 : L ≠ 0) (hL'L : L' ∣ L) {h : S A} {h' : S B}
    (hh : CuspForm.IsNewform h) (hh' : CuspForm.IsNewform h') (hA : A ∣ L') (hB : B ∣ L')
    (hagree : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff h' ℓ) :
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L' → ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff h' ℓ := by
  intro ℓ hℓ hℓL'
  haveI : NeZero L := ⟨hL0⟩
  exact hh.1.qCoeff_eq_of_coprime_of_forall_prime_not_dvd_of_dvd hL'L hh'.1 hA hB hagree
    ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL')

theorem key {L A B : ℕ} (hL0 : L ≠ 0) (ih : ∀ L' < L, P L') {h : S A} {h' : S B}
    (hh : CuspForm.IsNewform h) (hh' : CuspForm.IsNewform h') (hA : A ∣ L) (hB : B ∣ L)
    (hlcm : Nat.lcm A B = L) (hAB : ¬ A ∣ B)
    (hagree : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff h' ℓ) :
    False := by
  haveI : NeZero L := ⟨hL0⟩
  have hA0 : A ≠ 0 := ne_zero_of_dvd_ne_zero hL0 hA
  have hB0 : B ≠ 0 := ne_zero_of_dvd_ne_zero hL0 hB

  obtain ⟨q, hqlt⟩ : ∃ q : ℕ, B.factorization q < A.factorization q := by
    have hno : ¬ A.factorization ≤ B.factorization := fun hle =>
      hAB ((Nat.factorization_le_iff_dvd hA0 hB0).mp hle)
    rw [Finsupp.le_def] at hno
    obtain ⟨q, hq⟩ := not_forall.mp hno
    exact ⟨q, not_le.mp hq⟩
  set m := A.factorization q with hm
  set e := B.factorization q with he
  have hm0 : m ≠ 0 := by omega
  have hq : q.Prime := by
    have : q ∈ A.factorization.support := Finsupp.mem_support_iff.mpr hm0
    rw [Nat.support_factorization] at this
    exact Nat.prime_of_mem_primeFactors this

  have hLfac : L.factorization q = m := by
    rw [← hlcm, Nat.factorization_lcm hA0 hB0, Finsupp.sup_apply, ← hm, ← he]
    exact max_eq_left hqlt.le

  have hAdec : q ^ m * (A / q ^ m) = A := hm ▸ Nat.ordProj_mul_ordCompl_eq_self A q
  have hBdec : q ^ e * (B / q ^ e) = B := he ▸ Nat.ordProj_mul_ordCompl_eq_self B q
  have hLdec : q ^ m * (L / q ^ m) = L := by
    have := Nat.ordProj_mul_ordCompl_eq_self L q
    rwa [hLfac] at this
  have hqA : ¬ q ∣ A / q ^ m := hm ▸ Nat.not_dvd_ordCompl hq hA0
  have hqB : ¬ q ∣ B / q ^ e := he ▸ Nat.not_dvd_ordCompl hq hB0
  have hqL : ¬ q ∣ L / q ^ m := by
    have := Nat.not_dvd_ordCompl hq hL0
    rwa [hLfac] at this
  have hqL' : q ∣ L := (dvd_pow_self q hm0).trans ⟨L / q ^ m, hLdec.symm⟩

  have huniq : ∀ (R₁ : ℕ) (h'' : S R₁), CuspForm.IsNewform h'' → q * R₁ ∣ L →
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L → ModularFormClass.qCoeff h'' ℓ = ModularFormClass.qCoeff h' ℓ) →
      R₁ = B := by
    intro R₁ h'' hh'' hqR₁ hag
    have hR₁L : R₁ ∣ L := (Dvd.intro_left q rfl).trans hqR₁
    have hR₁0 : R₁ ≠ 0 := ne_zero_of_dvd_ne_zero hL0 hR₁L
    set L' := Nat.lcm R₁ B with hL'
    have hL'L : L' ∣ L := Nat.lcm_dvd hR₁L hB
    have hL'0 : L' ≠ 0 := Nat.lcm_ne_zero hR₁0 hB0

    have hR₁fac : R₁.factorization q < m := by
      have h1 : (q * R₁).factorization q ≤ L.factorization q :=
        (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hq.ne_zero hR₁0) hL0).mpr hqR₁)) q
      rw [Nat.factorization_mul hq.ne_zero hR₁0, Finsupp.add_apply, hq.factorization_self, hLfac] at h1
      omega
    have hL'fac : L'.factorization q < m := by
      rw [hL', Nat.factorization_lcm hR₁0 hB0, Finsupp.sup_apply]
      exact max_lt hR₁fac hqlt
    have hL'lt : L' < L := by
      rcases (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hL'L).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (heq ▸ hLfac) hL'fac.ne
    exact ih L' hL'lt hL'0 R₁ B h'' h' hh'' hh' (Nat.dvd_lcm_left R₁ B) (Nat.dvd_lcm_right R₁ B)
      (agree_of_dvd hL0 hL'L hh'' hh' (Nat.dvd_lcm_left R₁ B) (Nat.dvd_lcm_right R₁ B) hag)

  have h1A : 1 * A ∣ L := by rwa [one_mul]
  have h1B : 1 * B ∣ L := by rwa [one_mul]
  have hmem := decomp hq hh hh' hA hB hqL' hagree huniq h1A h1B
  exact hh.rescaleLin_sub_rescaleLin_notMem_span_sup_span hq hLdec hqL hAdec hqA hBdec hqB hqlt
    hh' h1A h1B hmem

theorem main_ind : ∀ L : ℕ, P L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro hL0 A B h h' hh hh' hA hB hagree
  have hA0 : A ≠ 0 := ne_zero_of_dvd_ne_zero hL0 hA
  have hB0 : B ≠ 0 := ne_zero_of_dvd_ne_zero hL0 hB

  set L₂ := Nat.lcm A B with hL₂
  have hL₂L : L₂ ∣ L := Nat.lcm_dvd hA hB
  have hL₂0 : L₂ ≠ 0 := Nat.lcm_ne_zero hA0 hB0
  rcases (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hL₂L).lt_or_eq with hlt | heq
  · exact ih L₂ hlt hL₂0 A B h h' hh hh' (Nat.dvd_lcm_left A B) (Nat.dvd_lcm_right A B)
      (agree_of_dvd hL0 hL₂L hh hh' (Nat.dvd_lcm_left A B) (Nat.dvd_lcm_right A B) hagree)
  ·
    by_cases hAB : A ∣ B
    · by_cases hBA : B ∣ A
      · exact Nat.dvd_antisymm hAB hBA
      · exact (key hL0 ih hh' hh hB hA ((Nat.lcm_comm B A).trans heq) hBA
          (fun ℓ hℓ hℓL => (hagree ℓ hℓ hℓL).symm)).elim
    · exact (key hL0 ih hh hh' hA hB heq hAB hagree).elim

end NewformLevelRigidity

theorem solution
    {M R R' : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    R = R' :=
  NewformLevelRigidity.main_ind M (NeZero.ne M) R R' g g' hg hg' hR hR' h

end

end S_CuspForm_IsNewform_level_eq_of_forall_prime_not_dvd_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsNewform_level_eq_of_forall_prime_not_dvd_qCoeff_eq (solution)
