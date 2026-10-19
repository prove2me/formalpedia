-- Prove2me | solution 1 for BookProof.HermiteBandHigher.IsBandR.add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:29:26.172057+00:00
-- url     : https://prove2.me/submissions/e8ebdd41-3893-4801-8c74-57a7dfa93ddb

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterSirkFinitePrecision
-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.add
open BookProof.HermiteBand
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}
theorem h44hb_add {d r m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : BookProof.HermiteBandHigher.IsBandR r m T) (hS : BookProof.HermiteBandHigher.IsBandR r m S) :
    BookProof.HermiteBandHigher.IsBandR r m (T + S) := by
  obtain ⟨M1, C1, hC1, h1⟩ := hT
  obtain ⟨M2, C2, hC2, h2⟩ := hS
  refine ⟨M1 + M2, C1 + C2, add_nonneg hC1 hC2, fun α => ?_⟩
  obtain ⟨f, hf, hfc, hfr, hfn⟩ := h1 α
  obtain ⟨g, hg, hgc, hgr, hgn⟩ := h2 α
  refine ⟨f + g, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.add_apply, hf, hg]; exact (map_add (Finsupp.linearCombination ℂ (BookProof.HermiteBand.hpsi (d := d))) f g).symm
  · exact (Finset.card_le_card Finsupp.support_add).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hfc hgc))
  · intro β hβ
    rcases Finset.mem_union.mp (Finsupp.support_add hβ) with h | h
    · exact hfr β h
    · exact hgr β h
  · intro β
    rw [Finsupp.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hfn β) (hgn β))

theorem h44hb_smul {d r m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (c : ℂ) (hT : BookProof.HermiteBandHigher.IsBandR r m T) :
    BookProof.HermiteBandHigher.IsBandR r m (c • T) := by
  obtain ⟨M1, C1, hC1, h1⟩ := hT
  refine ⟨M1, ‖c‖ * C1, mul_nonneg (norm_nonneg _) hC1, fun α => ?_⟩
  obtain ⟨f, hf, hfc, hfr, hfn⟩ := h1 α
  refine ⟨c • f, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.smul_apply, hf]; exact (map_smul (Finsupp.linearCombination ℂ (BookProof.HermiteBand.hpsi (d := d))) c f).symm
  · exact (Finset.card_le_card Finsupp.support_smul).trans hfc
  · intro β hβ
    exact hfr β (Finsupp.support_smul hβ)
  · intro β
    rw [Finsupp.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hfn β) (norm_nonneg _)

theorem h44hb_zero {d r m : ℕ} :
    BookProof.HermiteBandHigher.IsBandR r m (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by
  refine ⟨0, 0, le_refl _, fun α => ⟨0, ?_, ?_, ?_, ?_⟩⟩
  · simp
  · simp
  · simp
  · intro β; simp

theorem h44hb_sum {d r m : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, BookProof.HermiteBandHigher.IsBandR r m (F i)) :
    BookProof.HermiteBandHigher.IsBandR r m (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (h44hb_zero (d := d) (r := r) (m := m))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact h44hb_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem h44hb_monoR {d r r' m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hr : r ≤ r') (hT : BookProof.HermiteBandHigher.IsBandR r m T) :
    BookProof.HermiteBandHigher.IsBandR r' m T := by
  obtain ⟨M1, C1, hC1, h1⟩ := hT
  refine ⟨M1, C1, hC1, fun α => ?_⟩
  obtain ⟨f, hf, hfc, hfr, hfn⟩ := h1 α
  exact ⟨f, hf, hfc, fun β hβ => (hfr β hβ).trans hr, hfn⟩

theorem h44hb_deg_add {d m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : BookProof.HermiteBandHigher.IsBandDeg m T) (hS : BookProof.HermiteBandHigher.IsBandDeg m S) :
    BookProof.HermiteBandHigher.IsBandDeg m (T + S) := by
  obtain ⟨r1, h1⟩ := hT
  obtain ⟨r2, h2⟩ := hS
  exact ⟨max r1 r2, h44hb_add (h44hb_monoR (le_max_left _ _) h1) (h44hb_monoR (le_max_right _ _) h2)⟩

theorem h44hb_deg_smul {d m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (c : ℂ) (hT : BookProof.HermiteBandHigher.IsBandDeg m T) :
    BookProof.HermiteBandHigher.IsBandDeg m (c • T) := by
  obtain ⟨r1, h1⟩ := hT
  exact ⟨r1, h44hb_smul c h1⟩

theorem h44hb_deg_sum {d m : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, BookProof.HermiteBandHigher.IsBandDeg m (F i)) :
    BookProof.HermiteBandHigher.IsBandDeg m (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨0, h44hb_zero⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact h44hb_deg_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem solution {r m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBandR r m T) (hS : IsBandR r m S) : IsBandR r m (T + S) := by
  exact h44hb_add hT hS

