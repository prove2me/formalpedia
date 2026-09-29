-- Prove2me | solution 1 for CuspForm.exists_qCoeff_eq_sum_divisors_of_isNewform_matching
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c9739f94-16c8-5c40-8b75-ac4adb9d5573

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open CongruenceSubgroup
open scoped ModularForm MatrixGroups

private lemma wsmo_one_mem_strictPeriods (R : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

private lemma wsmo_analyticAt_cusp {M : ℕ} {k : ℤ} (f : CuspForm (Gamma0 M) k) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (wsmo_one_mem_strictPeriods M)

private lemma wsmo_qCoeff_smul {M : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff (⇑f) n := by
  unfold ModularFormClass.qCoeff
  rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • (⇑f) from by ext z; rfl,
    UpperHalfPlane.qExpansion_smul (wsmo_analyticAt_cusp f), map_smul, smul_eq_mul]

private lemma wsmo_qCoeff_add {M : ℕ} {k : ℤ} (f g : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n
      = ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add,
    UpperHalfPlane.qExpansion_add (wsmo_analyticAt_cusp f) (wsmo_analyticAt_cusp g), map_add]

private lemma wsmo_qCoeff_zero {M : ℕ} {k : ℤ} (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma0 M) k)) n = 0 := by
  have h := wsmo_qCoeff_smul (M := M) (k := k) 0 0 n
  rw [zero_smul] at h
  simpa using h

private lemma wsmo_qCoeff_finsetSum {M : ℕ} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, F i)) n
      = ∑ i ∈ s, ModularFormClass.qCoeff (⇑(F i)) n := by
  induction s using Finset.cons_induction with
  | empty => simpa using wsmo_qCoeff_zero (M := M) (k := k) n
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, wsmo_qCoeff_add, ih]

private lemma wsmo_qCoeff_rescaleLin {R d N : ℕ} [NeZero N] (hdRN : d * R ∣ N)
    (f : CuspForm (Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(FreyPackage.ModMCarrier.rescaleLin hdRN 2 f)) n
      = (d : ℂ) * (if d ∣ n then ModularFormClass.qCoeff (⇑f) (n / d) else 0) := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using hdRN))
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  set G := FreyPackage.ModMCarrier.rescaleLin hdRN 2 f with hG
  have hcoe : ⇑G = fun τ => (d : ℂ) * f (ModularForm.heckeDiagMatrix d • τ) := by
    funext τ
    show (⇑f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix d) τ = _
    rw [ModularForm.slash_heckeDiagMatrix_apply 2 hd]
    norm_num
  have hcoe2 : ⇑((d : ℂ)⁻¹ • G) = fun τ => f (ModularForm.heckeDiagMatrix d • τ) := by
    funext τ
    rw [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, hcoe, smul_eq_mul,
      inv_mul_cancel_left₀ hdC]
  calc ModularFormClass.qCoeff (⇑G) n
      = ModularFormClass.qCoeff (⇑((d : ℂ) • ((d : ℂ)⁻¹ • G))) n := by
        rw [smul_smul, mul_inv_cancel₀ hdC, one_smul]
    _ = (d : ℂ) * ModularFormClass.qCoeff (⇑((d : ℂ)⁻¹ • G)) n := wsmo_qCoeff_smul _ _ n
    _ = (d : ℂ) * (if d ∣ n then ModularFormClass.qCoeff (⇑f) (n / d) else 0) := by
        rw [hcoe2]
        congr 1
        exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f
          (wsmo_one_mem_strictPeriods R) hd n

private lemma wsmo_separation {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι)
    (v : CuspForm (Gamma0 N) 2) (w : ι → CuspForm (Gamma0 N) 2)
    (χ₀ : ℕ → ℂ) (χ : ι → ℕ → ℂ)
    (hv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN v = χ₀ ℓ • v)
    (hw : ∀ i ∈ S, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN (w i) = χ i ℓ • w i)
    (hsep : ∀ i ∈ S, ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ N ∧ χ i ℓ ≠ χ₀ ℓ)
    (hsum : v = ∑ i ∈ S, w i) : v = 0 := by
  classical
  subst hsum
  induction S using Finset.induction_on generalizing w with
  | empty => exact Finset.sum_empty
  | insert j S hj ih =>
    obtain ⟨ℓ, hℓ, hℓN, hne⟩ := hsep j (Finset.mem_insert_self j S)

    have key : (χ₀ ℓ - χ j ℓ) • (∑ i ∈ insert j S, w i)
        = ∑ i ∈ S, (χ i ℓ - χ j ℓ) • w i := by
      have h1 : CuspForm.heckeTLin 2 hℓ hℓN (∑ i ∈ insert j S, w i)
          = ∑ i ∈ insert j S, χ i ℓ • w i := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i hi => hw i hi ℓ hℓ hℓN
      rw [sub_smul, ← hv ℓ hℓ hℓN, h1, Finset.smul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_insert hj]
      simp only [← sub_smul, sub_self, zero_add]

    have hw' : ∀ i ∈ S, ∀ (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓ'N : ¬ ℓ' ∣ N),
        CuspForm.heckeTLin 2 hℓ' hℓ'N ((χ i ℓ - χ j ℓ) • w i)
          = χ i ℓ' • ((χ i ℓ - χ j ℓ) • w i) := by
      intro i hi ℓ' hℓ' hℓ'N
      rw [map_smul, hw i (Finset.mem_insert_of_mem hi) ℓ' hℓ' hℓ'N, smul_comm]
    have hsep' : ∀ i ∈ S, ∃ ℓ' : ℕ, ℓ'.Prime ∧ ¬ ℓ' ∣ N ∧ χ i ℓ' ≠ χ₀ ℓ' :=
      fun i hi => hsep i (Finset.mem_insert_of_mem hi)
    have hv' : ∀ (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓ'N : ¬ ℓ' ∣ N),
        CuspForm.heckeTLin 2 hℓ' hℓ'N (∑ i ∈ S, (χ i ℓ - χ j ℓ) • w i)
          = χ₀ ℓ' • ∑ i ∈ S, (χ i ℓ - χ j ℓ) • w i := by
      intro ℓ' hℓ' hℓ'N
      rw [← key, map_smul, hv ℓ' hℓ' hℓ'N, smul_comm]
    have hzero : ∑ i ∈ S, (χ i ℓ - χ j ℓ) • w i = 0 :=
      ih (fun i => (χ i ℓ - χ j ℓ) • w i) hw' hsep' hv'
    have hc : χ₀ ℓ - χ j ℓ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [hzero] at key
    calc ∑ i ∈ insert j S, w i
        = (χ₀ ℓ - χ j ℓ)⁻¹ • ((χ₀ ℓ - χ j ℓ) • ∑ i ∈ insert j S, w i) :=
          (inv_smul_smul₀ hc _).symm
      _ = 0 := by rw [key, smul_zero]

private lemma wsmo_regroup {ι : Type*} (s : Finset ι) (dd : ι → ℕ) (coef : ι → ℂ)
    (D : Finset ℕ) (hmaps : ∀ i ∈ s, dd i ∈ D) (X : ℕ → ℂ)
    [DecidableEq ℕ] :
    ∑ i ∈ s, coef i * X (dd i)
      = ∑ d ∈ D, (∑ i ∈ s.filter (fun i => dd i = d), coef i) * X d :=
  calc ∑ i ∈ s, coef i * X (dd i)
      = ∑ d ∈ D, ∑ i ∈ s.filter (fun i => dd i = d), coef i * X (dd i) :=
        (Finset.sum_fiberwise_of_maps_to hmaps (fun i => coef i * X (dd i))).symm
    _ = ∑ d ∈ D, (∑ i ∈ s.filter (fun i => dd i = d), coef i) * X d := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

theorem solution
    (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (f₀ : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf₀ : f₀.IsNewform)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hg : g.IsNormalizedEigenform)
    (hmatch : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N →
      ModularFormClass.qCoeff f₀ ℓ = ModularFormClass.qCoeff g ℓ) :
    ∃ c : ℕ → ℂ, ∀ n : ℕ, ModularFormClass.qCoeff g n =
      ∑ d ∈ (N / M).divisors, c d * (if d ∣ n then ModularFormClass.qCoeff f₀ (n / d) else 0) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hM : M ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hMN)
  have hNM : N / M ≠ 0 := by
    intro h0
    exact hN (by simpa [h0] using (Nat.div_mul_cancel hMN).symm)

  have hmem : g ∈ Submodule.span ℂ
      {F : CuspForm (Gamma0 N) 2 |
        ∃ (R d : ℕ) (hdRM : d * R ∣ N) (g' : CuspForm (Gamma0 R) 2),
          CuspForm.IsNewform g' ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g'} := by
    rw [CuspForm.span_rescaleLin_isNewform_eq_top N]
    trivial
  obtain ⟨l, hsupp, hsum⟩ := Submodule.mem_span_set.mp hmem

  have hwit : ∀ F : {x // x ∈ l.support},
      ∃ (R d : ℕ) (h : d * R ∣ N) (g' : CuspForm (Gamma0 R) 2),
        CuspForm.IsNewform g' ∧
        (F : CuspForm (Gamma0 N) 2) = FreyPackage.ModMCarrier.rescaleLin h 2 g' :=
    fun F => hsupp F.2
  choose Rf df hdvd gf hnew hFeq using hwit
  set S : Finset {x // x ∈ l.support} := l.support.attach with hS
  set w : {x // x ∈ l.support} → CuspForm (Gamma0 N) 2 :=
    fun F => l F.1 • F.1 with hw_def
  have hsum' : g = ∑ F ∈ S, w F := by
    rw [hS, hw_def]
    rw [← hsum, Finsupp.sum]
    exact (Finset.sum_attach l.support fun F => l F • F).symm

  set χ₀ : ℕ → ℂ := fun ℓ => ModularFormClass.qCoeff f₀ ℓ with hχ₀
  set χ : {x // x ∈ l.support} → ℕ → ℂ :=
    fun F ℓ => ModularFormClass.qCoeff (⇑(gf F)) ℓ with hχ
  have hgeig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN g = χ₀ ℓ • g := by
    intro ℓ hℓ hℓN
    have h1 := (((CuspForm.isNormalizedEigenform_iff_heckeTLin g).mp hg).2 ℓ hℓ).1 hℓN
    rw [h1, show ModularFormClass.qCoeff (⇑g) ℓ = χ₀ ℓ from (hmatch ℓ hℓ hℓN).symm]
  have hweig : ∀ F ∈ S, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN (w F) = χ F ℓ • w F := by
    intro F _ ℓ hℓ hℓN
    have hRdvd : Rf F ∣ N := dvd_of_mul_left_dvd (hdvd F)
    have hℓR : ¬ ℓ ∣ Rf F := fun hdR => hℓN (hdR.trans hRdvd)
    haveI : NeZero (Rf F) :=
      ⟨fun h0 => hN (Nat.eq_zero_of_zero_dvd (by simpa [h0] using hdvd F))⟩
    have heig := (((CuspForm.isNormalizedEigenform_iff_heckeTLin (gf F)).mp
      ((hnew F).isNormalizedEigenform)).2 ℓ hℓ).1 hℓR
    have hTF : CuspForm.heckeTLin 2 hℓ hℓN (F : CuspForm (Gamma0 N) 2)
        = χ F ℓ • (F : CuspForm (Gamma0 N) 2) := by
      rw [hFeq F, CuspForm.heckeTLin_rescaleLin (hdvd F) hℓ hℓN hℓR (gf F), heig, map_smul]
    simp only [hw_def]
    rw [map_smul, hTF, smul_comm]

  set GOOD : Finset {x // x ∈ l.support} :=
    S.filter (fun F => ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → χ F ℓ = χ₀ ℓ) with hGOOD
  set BAD : Finset {x // x ∈ l.support} :=
    S.filter (fun F => ¬ ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → χ F ℓ = χ₀ ℓ) with hBAD
  have hsplit : ∑ F ∈ GOOD, w F + ∑ F ∈ BAD, w F = ∑ F ∈ S, w F :=
    Finset.sum_filter_add_sum_filter_not S _ w
  set v : CuspForm (Gamma0 N) 2 := g - ∑ F ∈ GOOD, w F with hv_def
  have hvsum : v = ∑ F ∈ BAD, w F := by
    rw [hv_def, hsum', ← hsplit]
    abel
  have hveig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN v = χ₀ ℓ • v := by
    intro ℓ hℓ hℓN
    rw [hv_def, map_sub, hgeig ℓ hℓ hℓN, map_sum, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun F hF => ?_
    have hFS : F ∈ S := Finset.mem_filter.mp hF |>.1
    have hFmatch := Finset.mem_filter.mp hF |>.2
    rw [hweig F hFS ℓ hℓ hℓN, hFmatch ℓ hℓ hℓN]
  have hbadsep : ∀ F ∈ BAD, ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ N ∧ χ F ℓ ≠ χ₀ ℓ := by
    intro F hF
    have h := Finset.mem_filter.mp hF |>.2
    rcases Classical.not_forall.mp h with ⟨ℓ, hℓcon⟩
    rcases Classical.not_imp.mp hℓcon with ⟨hℓ, hrest⟩
    rcases Classical.not_imp.mp hrest with ⟨hℓN, hne⟩
    exact ⟨ℓ, hℓ, hℓN, hne⟩
  have hbadw : ∀ F ∈ BAD, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN (w F) = χ F ℓ • w F :=
    fun F hF => hweig F (Finset.mem_filter.mp hF |>.1)
  have hv0 : v = 0 := wsmo_separation BAD v w χ₀ χ hveig hbadw hbadsep hvsum
  have hgood : g = ∑ F ∈ GOOD, w F := by
    have := hv_def ▸ hv0
    exact sub_eq_zero.mp this

  have hengine : ∀ F ∈ GOOD,
      Rf F = M ∧ ∀ m : ℕ, ModularFormClass.qCoeff (⇑(gf F)) m = ModularFormClass.qCoeff f₀ m := by
    intro F hF
    have hpred := Finset.mem_filter.mp hF |>.2
    exact CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
      (hnew F) hf₀ (dvd_of_mul_left_dvd (hdvd F)) hMN hpred
  have hdM : ∀ F ∈ GOOD, df F ∈ (N / M).divisors := by
    intro F hF
    have hlev := (hengine F hF).1
    have : df F * M ∣ N := by rw [← hlev]; exact hdvd F
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at this), hNM⟩

  refine ⟨fun d => ∑ F ∈ GOOD.filter (fun F => df F = d), l F.1 * (df F : ℂ), fun n => ?_⟩
  have h1 : ModularFormClass.qCoeff g n
      = ∑ F ∈ GOOD, ModularFormClass.qCoeff (⇑(w F)) n := by
    conv_lhs => rw [hgood]
    exact wsmo_qCoeff_finsetSum GOOD w n
  have h2 : ∀ F ∈ GOOD, ModularFormClass.qCoeff (⇑(w F)) n
      = (l F.1 * (df F : ℂ)) * (if df F ∣ n then ModularFormClass.qCoeff f₀ (n / df F) else 0) := by
    intro F hF
    have hqF : ModularFormClass.qCoeff (⇑(F : CuspForm (Gamma0 N) 2)) n
        = (df F : ℂ) * (if df F ∣ n then ModularFormClass.qCoeff (⇑(gf F)) (n / df F) else 0) := by
      rw [hFeq F, wsmo_qCoeff_rescaleLin (hdvd F) (gf F) n]
    simp only [hw_def]
    rw [wsmo_qCoeff_smul (l F.1), hqF]
    have hco := (hengine F hF).2 (n / df F)
    rw [mul_assoc]
    congr 1
    congr 1
    split_ifs with h
    · rw [hco]
    · rfl
  calc ModularFormClass.qCoeff g n
      = ∑ F ∈ GOOD, ModularFormClass.qCoeff (⇑(w F)) n := h1
    _ = ∑ F ∈ GOOD, (l F.1 * (df F : ℂ))
          * (if df F ∣ n then ModularFormClass.qCoeff f₀ (n / df F) else 0) :=
        Finset.sum_congr rfl h2
    _ = ∑ d ∈ (N / M).divisors,
          (∑ F ∈ GOOD.filter (fun F => df F = d), l F.1 * (df F : ℂ))
          * (if d ∣ n then ModularFormClass.qCoeff f₀ (n / d) else 0) :=
        wsmo_regroup GOOD df (fun F => l F.1 * (df F : ℂ)) ((N / M).divisors) hdM
          (fun d => if d ∣ n then ModularFormClass.qCoeff f₀ (n / d) else 0)

end

end S_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching
end P2MW
export P2MW.S_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching (solution)
