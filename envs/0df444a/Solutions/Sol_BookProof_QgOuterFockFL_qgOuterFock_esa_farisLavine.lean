-- Prove2me | solution 1 for BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:41:24.280423+00:00
-- url     : https://prove2.me/submissions/f4fc5704-774b-464f-97e0-9e0e5cee15db

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Theorems.Thm_BookProof_QgOuterFockFL_polyGaussCore_le_harmFriedDom
import Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_fib
-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL


open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}
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

theorem solution
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
  exact h42_esa H hsym hext K c hc hrel hcomm

