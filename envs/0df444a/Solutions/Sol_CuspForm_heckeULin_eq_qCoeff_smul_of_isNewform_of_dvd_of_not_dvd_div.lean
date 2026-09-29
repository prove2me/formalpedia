-- Prove2me | solution 1 for CuspForm.heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8a61310d-fe9d-5562-b007-c5e40cc2831c

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_qCoeff_rescaleLin
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option Elab.async false

noncomputable section

open CongruenceSubgroup ModularFormClass
open scoped ModularForm MatrixGroups

namespace ALMain

theorem one_mem_strictPeriods (R : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

theorem analyticAt_cusp {M : ℕ} {k : ℤ} (f : CuspForm (Gamma0 M) k) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods M)

theorem qCoeff_smul {M : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff (⇑f) n := by
  unfold ModularFormClass.qCoeff
  rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • (⇑f) from by ext z; rfl,
    UpperHalfPlane.qExpansion_smul (analyticAt_cusp f), map_smul, smul_eq_mul]

theorem qCoeff_add {M : ℕ} {k : ℤ} (f g : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n
      = ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add,
    UpperHalfPlane.qExpansion_add (analyticAt_cusp f) (analyticAt_cusp g), map_add]

theorem qCoeff_sub {M : ℕ} {k : ℤ} (f g : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f - g)) n
      = ModularFormClass.qCoeff (⇑f) n - ModularFormClass.qCoeff (⇑g) n := by
  rw [sub_eq_add_neg, qCoeff_add, ← neg_one_smul ℂ g, qCoeff_smul]
  ring

theorem qCoeff_zero {M : ℕ} {k : ℤ} (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma0 M) k)) n = 0 := by
  have h := qCoeff_smul (M := M) (k := k) 0 0 n
  rw [zero_smul] at h
  simpa using h

theorem qCoeff_finsetSum {M : ℕ} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, F i)) n
      = ∑ i ∈ s, ModularFormClass.qCoeff (⇑(F i)) n := by
  induction s using Finset.cons_induction with
  | empty => simpa using qCoeff_zero (M := M) (k := k) n
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, qCoeff_add, ih]

theorem qCoeff_mul_of_prime_dvd {M : ℕ} {g : CuspForm (Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (m : ℕ) (hm : m ≠ 0) :
    ModularFormClass.qCoeff (⇑g) (q * m) = ModularFormClass.qCoeff (⇑g) q * ModularFormClass.qCoeff (⇑g) m := by

  have hpow : ∀ j : ℕ, ModularFormClass.qCoeff (⇑g) (q ^ (j + 1)) =
      ModularFormClass.qCoeff (⇑g) q * ModularFormClass.qCoeff (⇑g) (q ^ j) := by
    intro j
    cases j with
    | zero => rw [zero_add, pow_one, pow_zero, hg.qCoeff_one, mul_one]
    | succ r => exact hg.qCoeff_prime_pow_of_dvd q r hq hqM
  obtain ⟨j, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm q hq.ne_one
  have hcop : ∀ i : ℕ, Nat.Coprime (q ^ i) m' := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hq).2 hm')
  rw [show q * (q ^ j * m') = q ^ (j + 1) * m' by ring,
    hg.qCoeff_mul_of_coprime _ _ (hcop (j + 1)), hg.qCoeff_mul_of_coprime _ _ (hcop j), hpow j]
  ring

theorem separation {N : ℕ} [NeZero N] (S : Finset ℕ) {ι : Type*} (I : Finset ι)
    (v : CuspForm (Gamma0 N) 2) (w : ι → CuspForm (Gamma0 N) 2)
    (χ₀ : ℕ → ℂ) (χ : ι → ℕ → ℂ)
    (hv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN v = χ₀ ℓ • v)
    (hw : ∀ i ∈ I, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN (w i) = χ i ℓ • w i)
    (hsep : ∀ i ∈ I, ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S ∧ χ i ℓ ≠ χ₀ ℓ)
    (hsum : v = ∑ i ∈ I, w i) : v = 0 := by
  classical
  subst hsum
  induction I using Finset.induction_on generalizing w with
  | empty => exact Finset.sum_empty
  | insert j I hj ih =>
    obtain ⟨ℓ, hℓ, hℓN, hℓS, hne⟩ := hsep j (Finset.mem_insert_self j I)

    have key : (χ₀ ℓ - χ j ℓ) • (∑ i ∈ insert j I, w i)
        = ∑ i ∈ I, (χ i ℓ - χ j ℓ) • w i := by
      have h1 : CuspForm.heckeTLin 2 hℓ hℓN (∑ i ∈ insert j I, w i)
          = ∑ i ∈ insert j I, χ i ℓ • w i := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i hi => hw i hi ℓ hℓ hℓN
      rw [sub_smul, ← hv ℓ hℓ hℓN hℓS, h1, Finset.smul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_insert hj]
      simp only [← sub_smul, sub_self, zero_add]
    have hw' : ∀ i ∈ I, ∀ (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓ'N : ¬ ℓ' ∣ N),
        CuspForm.heckeTLin 2 hℓ' hℓ'N ((χ i ℓ - χ j ℓ) • w i)
          = χ i ℓ' • ((χ i ℓ - χ j ℓ) • w i) := by
      intro i hi ℓ' hℓ' hℓ'N
      rw [map_smul, hw i (Finset.mem_insert_of_mem hi) ℓ' hℓ' hℓ'N, smul_comm]
    have hsep' : ∀ i ∈ I, ∃ ℓ' : ℕ, ℓ'.Prime ∧ ¬ ℓ' ∣ N ∧ ℓ' ∉ S ∧ χ i ℓ' ≠ χ₀ ℓ' :=
      fun i hi => hsep i (Finset.mem_insert_of_mem hi)
    have hv' : ∀ (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓ'N : ¬ ℓ' ∣ N), ℓ' ∉ S →
        CuspForm.heckeTLin 2 hℓ' hℓ'N (∑ i ∈ I, (χ i ℓ - χ j ℓ) • w i)
          = χ₀ ℓ' • ∑ i ∈ I, (χ i ℓ - χ j ℓ) • w i := by
      intro ℓ' hℓ' hℓ'N hℓ'S
      rw [← key, map_smul, hv ℓ' hℓ' hℓ'N hℓ'S, smul_comm]
    have hzero : ∑ i ∈ I, (χ i ℓ - χ j ℓ) • w i = 0 :=
      ih (fun i => (χ i ℓ - χ j ℓ) • w i) hw' hsep' hv'
    have hc : χ₀ ℓ - χ j ℓ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [hzero] at key
    calc ∑ i ∈ insert j I, w i
        = (χ₀ ℓ - χ j ℓ)⁻¹ • ((χ₀ ℓ - χ j ℓ) • ∑ i ∈ insert j I, w i) :=
          (inv_smul_smul₀ hc _).symm
      _ = 0 := by rw [key, smul_zero]

end ALMain

open ALMain in
theorem solution
    (N M : ℕ) [NeZero N] [NeZero M] (hMN : M ∣ N) (S : Finset ℕ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hg : g.IsNewform)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqNM : ¬ q ∣ N / M)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN f = qCoeff g ℓ • f) :
    CuspForm.heckeULin 2 (hqM.trans hMN) f = qCoeff g q • f := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hM : M ≠ 0 := NeZero.ne M

  obtain ⟨Namb, hNamb⟩ : ∃ Namb : ℕ, Namb = N * ∏ s ∈ S.filter (fun s => s ≠ 0), s := ⟨_, rfl⟩
  have hNamb0 : Namb ≠ 0 := by
    rw [hNamb]
    exact mul_ne_zero hN (Finset.prod_ne_zero_iff.2 fun s hs => (Finset.mem_filter.1 hs).2)
  haveI : NeZero Namb := ⟨hNamb0⟩
  have hNNamb : N ∣ Namb := by rw [hNamb]; exact dvd_mul_right N _
  have hgoodℓ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Namb → ¬ ℓ ∣ N ∧ ℓ ∉ S := by
    intro ℓ hℓ hℓA
    refine ⟨fun h => hℓA (h.trans hNNamb), fun hS => hℓA ?_⟩
    rw [hNamb]
    exact (Finset.dvd_prod_of_mem (fun s : ℕ => s) (Finset.mem_filter.2 ⟨hS, hℓ.ne_zero⟩)).trans
      (dvd_mul_left _ _)

  have hmem : f ∈ Submodule.span ℂ
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
  set I : Finset {x // x ∈ l.support} := l.support.attach with hI
  set w : {x // x ∈ l.support} → CuspForm (Gamma0 N) 2 :=
    fun F => l F.1 • F.1 with hw_def
  have hsum' : f = ∑ F ∈ I, w F := by
    rw [hI, hw_def]
    rw [← hsum, Finsupp.sum]
    exact (Finset.sum_attach l.support fun F => l F • F).symm

  have hweig : ∀ F ∈ I, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN (w F) = (fun F ℓ => ModularFormClass.qCoeff (⇑(gf F)) ℓ) F ℓ • w F := by
    intro F _ ℓ hℓ hℓN
    have hRdvd : Rf F ∣ N := dvd_of_mul_left_dvd (hdvd F)
    have hℓR : ¬ ℓ ∣ Rf F := fun hdR => hℓN (hdR.trans hRdvd)
    haveI : NeZero (Rf F) :=
      ⟨fun h0 => hN (Nat.eq_zero_of_zero_dvd (by simpa [h0] using hdvd F))⟩
    have heig := (((CuspForm.isNormalizedEigenform_iff_heckeTLin (gf F)).mp
      ((hnew F).isNormalizedEigenform)).2 ℓ hℓ).1 hℓR
    have hTF : CuspForm.heckeTLin 2 hℓ hℓN (F : CuspForm (Gamma0 N) 2)
        = ModularFormClass.qCoeff (⇑(gf F)) ℓ • (F : CuspForm (Gamma0 N) 2) := by
      rw [hFeq F, CuspForm.heckeTLin_rescaleLin (hdvd F) hℓ hℓN hℓR (gf F), heig, map_smul]
    simp only [hw_def]
    rw [map_smul, hTF, smul_comm]

  set GOOD : Finset {x // x ∈ l.support} :=
    I.filter (fun F => ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S →
      ModularFormClass.qCoeff (⇑(gf F)) ℓ = ModularFormClass.qCoeff (⇑g) ℓ) with hGOOD
  set BAD : Finset {x // x ∈ l.support} :=
    I.filter (fun F => ¬ ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S →
      ModularFormClass.qCoeff (⇑(gf F)) ℓ = ModularFormClass.qCoeff (⇑g) ℓ) with hBAD
  have hsplit : ∑ F ∈ GOOD, w F + ∑ F ∈ BAD, w F = ∑ F ∈ I, w F :=
    Finset.sum_filter_add_sum_filter_not I _ w
  set v : CuspForm (Gamma0 N) 2 := f - ∑ F ∈ GOOD, w F with hv_def
  have hvsum : v = ∑ F ∈ BAD, w F := by
    rw [hv_def, hsum', ← hsplit]
    abel
  have hveig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN v = (fun ℓ => ModularFormClass.qCoeff (⇑g) ℓ) ℓ • v := by
    intro ℓ hℓ hℓN hℓS
    show CuspForm.heckeTLin 2 hℓ hℓN v = ModularFormClass.qCoeff (⇑g) ℓ • v
    rw [hv_def, map_sub, hf ℓ hℓ hℓN hℓS, map_sum, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun F hF => ?_
    have hFI : F ∈ I := Finset.mem_filter.mp hF |>.1
    have hFmatch := Finset.mem_filter.mp hF |>.2
    rw [hweig F hFI ℓ hℓ hℓN]
    show ModularFormClass.qCoeff (⇑(gf F)) ℓ • w F = _
    rw [hFmatch ℓ hℓ hℓN hℓS]
  have hbadsep : ∀ F ∈ BAD, ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S ∧
      (fun F ℓ => ModularFormClass.qCoeff (⇑(gf F)) ℓ) F ℓ ≠ (fun ℓ => ModularFormClass.qCoeff (⇑g) ℓ) ℓ := by
    intro F hF
    have h := Finset.mem_filter.mp hF |>.2
    rcases Classical.not_forall.mp h with ⟨ℓ, hℓcon⟩
    rcases Classical.not_imp.mp hℓcon with ⟨hℓ, hrest⟩
    rcases Classical.not_imp.mp hrest with ⟨hℓN, hrest'⟩
    rcases Classical.not_imp.mp hrest' with ⟨hℓS, hne⟩
    exact ⟨ℓ, hℓ, hℓN, hℓS, hne⟩
  have hbadw : ∀ F ∈ BAD, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      CuspForm.heckeTLin 2 hℓ hℓN (w F) = (fun F ℓ => ModularFormClass.qCoeff (⇑(gf F)) ℓ) F ℓ • w F :=
    fun F hF => hweig F (Finset.mem_filter.mp hF |>.1)
  have hv0 : v = 0 := separation S BAD v w _ _ hveig hbadw hbadsep hvsum
  have hgood : f = ∑ F ∈ GOOD, w F := by
    have := hv_def ▸ hv0
    exact sub_eq_zero.mp this

  have hengine : ∀ F ∈ GOOD,
      Rf F = M ∧ ∀ m : ℕ, ModularFormClass.qCoeff (⇑(gf F)) m = ModularFormClass.qCoeff (⇑g) m := by
    intro F hF
    have hpred := Finset.mem_filter.mp hF |>.2
    exact CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq (M := Namb)
      (hnew F) hg ((dvd_of_mul_left_dvd (hdvd F)).trans hNNamb) (hMN.trans hNNamb)
      (fun ℓ hℓ hℓA => hpred ℓ hℓ (hgoodℓ ℓ hℓ hℓA).1 (hgoodℓ ℓ hℓ hℓA).2)
  have hd0 : ∀ F ∈ GOOD, df F ≠ 0 := by
    intro F _ h0
    exact hN (Nat.eq_zero_of_zero_dvd (by simpa [h0] using hdvd F))
  have hqd : ∀ F ∈ GOOD, ¬ q ∣ df F := by
    intro F hF hqdF
    apply hqNM
    have hlev := (hengine F hF).1
    have h1 : df F * M ∣ N := by rw [← hlev]; exact hdvd F
    exact hqdF.trans (Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at h1))

  have hcoef : ∀ n : ℕ, n ≠ 0 →
      ModularFormClass.qCoeff (⇑(CuspForm.heckeULin 2 (hqM.trans hMN) f)) n =
        ModularFormClass.qCoeff (⇑(qCoeff g q • f)) n := by
    intro n hn
    rw [CuspForm.coe_heckeULin_apply, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods N) hq.ne_zero n,
      ModularForm.coeffHeckeU_apply, qCoeff_smul]

    conv_lhs => rw [hgood]
    conv_rhs => rw [hgood]
    rw [qCoeff_finsetSum, qCoeff_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF => ?_
    have heng := (hengine F hF).2
    have hdpos : 0 < df F := Nat.pos_of_ne_zero (hd0 F hF)
    have hcop : Nat.Coprime (df F) q :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 (hqd F hF)))
    have hwF : ∀ idx : ℕ, ModularFormClass.qCoeff (⇑(w F)) idx =
        l F.1 * (if df F ∣ idx then ((df F : ℂ) ^ ((2 : ℤ) - 1)) * ModularFormClass.qCoeff (⇑(gf F)) (idx / df F)
          else 0) := by
      intro idx
      simp only [hw_def]
      rw [qCoeff_smul (l F.1), hFeq F, CuspForm.qCoeff_rescaleLin (hdvd F) 2 (gf F) idx]
    rw [hwF (n * q), hwF n]
    by_cases hdn : df F ∣ n
    · obtain ⟨e, rfl⟩ := hdn
      have he : e ≠ 0 := fun h => hn (by rw [h, mul_zero])
      rw [if_pos (dvd_mul_of_dvd_left (dvd_mul_right (df F) e) q), if_pos (dvd_mul_right (df F) e),
        show df F * e * q = df F * (e * q) by ring, Nat.mul_div_cancel_left (e * q) hdpos,
        Nat.mul_div_cancel_left e hdpos, heng (e * q), heng e, mul_comm e q,
        qCoeff_mul_of_prime_dvd hg.isNormalizedEigenform hq hqM e he]
      ring
    · rw [if_neg (fun h => hdn (hcop.dvd_mul_right.1 h)), if_neg hdn]
      ring

  obtain ⟨p, hpN1, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hpN : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
    omega
  have hD : CuspForm.heckeULin 2 (hqM.trans hMN) f - qCoeff g q • f = 0 := by
    refine CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero hp hpN _ fun n hpn => ?_
    have hn : n ≠ 0 := fun h => hpn (h ▸ dvd_zero p)
    rw [qCoeff_sub, hcoef n hn, sub_self]
  exact sub_eq_zero.mp hD

end

end S_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
end P2MW
export P2MW.S_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div (solution)
