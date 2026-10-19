-- Prove2me | solution 2 for BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:42:38.110347+00:00
-- url     : https://prove2.me/submissions/0307a37d-3323-4728-bf8a-ae2a0225799a

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_rel
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_symmetricOn
import Theorems.Thm_BookProof_QgOuterFock_sqSumOp_symmetricOn
import Theorems.Thm_BookProof_QgOuterFockFL_polyGaussCore_le_harmFriedDom
import Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_fib
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_commForm_le
import Theorems.Thm_BookProof_SqSumFarisLavine_commForm_sqSumOp_le
-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.QgOuterFockFullFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open Filter Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open Finset

theorem h42_wcs {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, |a i|) * (∑ i ∈ s, |a i| * b i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt |a i|)
    (fun i => Real.sqrt |a i| * (SignType.sign (a i) : ℝ) * b i)
  have e1 : ∀ i, Real.sqrt |a i| * (Real.sqrt |a i| * (SignType.sign (a i) : ℝ) * b i) = a i * b i := by
    intro i
    rw [← mul_assoc, ← mul_assoc, Real.mul_self_sqrt (abs_nonneg _), abs_mul_sign]
  have e2 : ∀ i, Real.sqrt |a i| ^ 2 = |a i| := fun i => Real.sq_sqrt (abs_nonneg _)
  have e3 : ∀ i, (Real.sqrt |a i| * (SignType.sign (a i) : ℝ) * b i) ^ 2 = |a i| * b i ^ 2 := by
    intro i
    rw [mul_pow, mul_pow, e2]
    rcases lt_trichotomy (a i) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  simp only [e1, e2, e3] at h
  exact h

theorem h42_grad {R : Type*} [Fintype R] {D : ℕ} (v : R → Fin D → ℝ) (x : Fin D → ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : ∀ k, ∑ r, |v r k| ≤ A) (h2 : ∀ r, ∑ k, |v r k| ≤ B) :
    ∑ k, (∑ r, v r k * ∑ i, v r i * x i) ^ 2 ≤ (A * B) ^ 2 * ∑ k, x k ^ 2 := by
  set L : R → ℝ := fun r => ∑ i, v r i * x i with hL
  have hL2 : ∀ r, L r ^ 2 ≤ B * ∑ k, |v r k| * x k ^ 2 := by
    intro r
    refine (h42_wcs _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (h2 r) (sum_nonneg fun _ _ => by positivity)
  have hk : ∀ k, (∑ r, v r k * L r) ^ 2 ≤ A * ∑ r, |v r k| * L r ^ 2 := by
    intro k
    refine (h42_wcs _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (h1 k) (sum_nonneg fun _ _ => by positivity)
  calc ∑ k, (∑ r, v r k * L r) ^ 2 ≤ ∑ k, A * ∑ r, |v r k| * L r ^ 2 := sum_le_sum fun k _ => hk k
    _ = A * ∑ r, L r ^ 2 * ∑ k, |v r k| := by
        rw [← mul_sum, sum_comm]; congr 1; refine sum_congr rfl fun r _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ A * ∑ r, L r ^ 2 * B := by
        gcongr with r; exact h2 r
    _ ≤ A * ∑ r, (B * ∑ k, |v r k| * x k ^ 2) * B := by
        gcongr with r; exact hL2 r
    _ = A * B ^ 2 * ∑ k, x k ^ 2 * ∑ r, |v r k| := by
        simp only [mul_sum, sum_mul]; rw [sum_comm]
        refine sum_congr rfl fun k _ => sum_congr rfl fun r _ => by ring
    _ ≤ A * B ^ 2 * ∑ k, x k ^ 2 * A := by
        gcongr with k; exact h1 k
    _ = (A * B) ^ 2 * ∑ k, x k ^ 2 := by rw [← sum_mul]; ring

theorem h42_tv_le_one (m : Fin 64) (i : Fin 84) : |torsionVec m i| ≤ 1 := by
  unfold torsionVec; split_ifs <;> norm_num

theorem h42_tv_sum (m : Fin 64) : ∑ i, |torsionVec m i| ≤ 2 := by
  have : ∀ i, |torsionVec m i| ≤ (if i = torsionIdx1 m then 1 else 0) + (if i = torsionIdx2 m then 1 else 0) := by
    intro i; unfold torsionVec; split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun i _ => this i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp; norm_num
theorem h42_gradFun_le (n : ℕ) (x : Vd (n * 84)) :
    ∑ k : Fin (n * 84), (gradFun (qgTorsionVecN n) k x) ^ 2 ≤ (128 : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  have h1 : ∀ k, ∑ r, |qgTorsionVecN n r k| ≤ 64 := by
    intro k
    simp only [qgTorsionVecN, Fintype.sum_prod_type, apply_ite abs, abs_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    calc ∑ m : Fin 64, |torsionVec m (modeOf k)| ≤ ∑ _m : Fin 64, (1:ℝ) :=
          Finset.sum_le_sum fun m _ => h42_tv_le_one m _
      _ = 64 := by simp
  have h2 : ∀ r, ∑ k, |qgTorsionVecN n r k| ≤ 2 := by
    intro r
    rw [← finProdFinEquiv.sum_comp]
    simp only [qgTorsionVecN, partOf, modeOf, Equiv.symm_apply_apply, Fintype.sum_prod_type,
      apply_ite abs, abs_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact h42_tv_sum r.2
  have key := h42_grad (qgTorsionVecN n) (fun i => x i) 64 2 (by norm_num) (by norm_num) h1 h2
  have hx : ‖x‖ ^ 2 = ∑ k, x k ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hx]
  have e : ((64:ℝ) * 2) ^ 2 = 128 ^ 2 := by norm_num
  rw [e] at key
  simpa only [gradFun, linFun] using key
theorem h42_ham_comm (n : ℕ) (u : polyGaussCore (d := n * 84)) :
    |commForm (qgSectorHam n) BookProof.QgOuterFockFL.harmCore u| ≤ qgFLc * quadForm BookProof.QgOuterFockFL.harmCore u := by
  have h := BookProof.SqSumFarisLavine.commForm_sqSumOp_le (km := 1 / 16) (M := 128) (by norm_num)
    (qgKappaN_abs_le n) (by norm_num) (h42_gradFun_le n) u
  rw [qgFLc]
  exact h
theorem h42_data_comm (n : ℕ) (p : (qgSectorData n).C₀) :
    |commForm (qgSectorData n).H₀ (qgSectorData n).coreN p|
      ≤ qgFLc * quadForm (qgSectorData n).coreN p := by
  have hc : (qgSectorData n).coreN = BookProof.QgOuterFockFL.harmCore :=
    LinearMap.ext fun q => BookProof.QgOuterFockFL.harmFried_op_core _ q _
  rw [hc]
  exact h42_ham_comm n p
theorem h42_core_dense {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) : DenseRange (d.coreRange.subtypeL) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨x, hx⟩ := d.C.surj f
  obtain ⟨y, hy0, hy1, hy2⟩ := d.gc.approx x (ε / 2) (by positivity)
  refine ⟨⟨d.coreShift ⟨(y : F), hy0⟩, ⟨_, rfl⟩⟩, ?_⟩
  simp only [Submodule.subtypeL_apply, CoreData.coreShift_apply]
  have hyy : (⟨(y : F), d.gc.le hy0⟩ : d.C.dom) = y := rfl
  rw [hyy, dist_eq_norm]
  calc ‖f - (d.C.op y + (y : F))‖ = ‖(d.C.op x - d.C.op y) + ((x : F) - (y : F))‖ := by
        rw [← hx]; congr 1; abel
    _ ≤ ‖d.C.op x - d.C.op y‖ + ‖(x : F) - (y : F)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [norm_sub_rev (d.C.op x), norm_sub_rev (x : F)]; exact add_lt_add hy2 hy1
    _ = ε := by ring

theorem h42_ext_core {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) (p : d.C₀) (h : (p : F) ∈ d.C.dom) : d.ext ⟨(p : F), h⟩ = d.H₀ p := by
  have hs : shiftOp d.C ⟨(p : F), h⟩ = d.coreRange.subtypeL (d.coreEquiv p) := rfl
  simp only [CoreData.ext, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hs, CoreData.extCLM, ContinuousLinearMap.extend_eq _ (h42_core_dense d)
    (isUniformEmbedding_subtype_val.isUniformInducing)]
  simp [CoreData.resolvedCLM, CoreData.resolvedMap]
theorem h42_core_le : qgOuterCore ≤ qgOuterFriedDom := by
  intro x hx
  refine ⟨fun n => BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom _ (hx.2 n),
    BookProof.DirectSumEsa.memLp_of_finite_support (hx.1.subset ?_)⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  apply hn
  rw [h0, opTot_of_mem _ (Submodule.zero_mem _)]
  exact map_zero _
theorem h42_esa
    (H : ∀ n : ℕ, (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84))
    (hsym : ∀ n : ℕ, SymmetricOn (harmFried (n * 84)).dom (H n))
    (hext : ∀ (n : ℕ) (p : polyGaussCore (d := n * 84))
      (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom),
      H n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p)
    (K c : ℝ) (hc : 0 ≤ c)
    (hrel : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
      ‖H n u‖ ≤ K * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖)
    (hcomm : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
      |commForm (H n) (harmFried (n * 84)).op u| ≤ c * quadForm (harmFried (n * 84)).op u) :
    EssentiallySelfAdjointOn qgOuterFriedDom
        (dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel) ∧
      ∀ x : qgOuterCore, ∃ h : (x : BookProof.QgOuterFockFL.qgOuterFock) ∈ qgOuterFriedDom,
        dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel ⟨(x : BookProof.QgOuterFockFL.qgOuterFock), h⟩
          = qgOuterHam x := by
  refine ⟨BookProof.QgOuterFockFL.dsFibOp_essentiallySelfAdjointOn hc hrel hsym hcomm,
    fun x => ⟨h42_core_le x.2, ?_⟩⟩
  apply lp.ext
  funext n
  rw [BookProof.QgOuterFockFL.dsFibOp_fib]
  exact hext n ⟨((x : BookProof.QgOuterFockFL.qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n, x.2.2 n⟩ _

theorem solution :
    EssentiallySelfAdjointOn qgOuterFriedDom
        (dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel) ∧
      ∀ x : qgOuterCore, ∃ h : (x : BookProof.QgOuterFockFL.qgOuterFock) ∈ qgOuterFriedDom,
        dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel
            ⟨(x : BookProof.QgOuterFockFL.qgOuterFock), h⟩ = qgOuterHam x := by
  exact h42_esa qgSectorExt
    (fun n => BookProof.QgOuterFockCoreFL.CoreData.ext_symmetricOn (qgSectorData n)
      (BookProof.QgOuterFock.sqSumOp_symmetricOn (qgKappaN n) (qgTorsionVecN n)))
    (fun n p h => h42_ext_core (qgSectorData n) p h) qgFLK qgFLc (by norm_num [qgFLc]) qgSectorExt_rel
    (fun n u => BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le (qgSectorData n) (h42_data_comm n) u)

