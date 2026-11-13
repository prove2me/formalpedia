-- Prove2me | solution 1 for BosonicLearn.isDensity_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T05:33:08.012365+00:00
-- url     : https://prove2.me/submissions/21f2f674-c100-41ac-84b1-ae677c7e27e2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal

noncomputable section

/-- Transport of a vector of `ℓ²(A)` along a bijection `A ≃ B`. -/
private def reVec {A B : Type} (e : A ≃ B) (f : Hilbert A) : Hilbert B :=
  ⟨fun b => f (e.symm b), memℓp_gen (by
    have h := (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact h.comp_injective e.symm.injective)⟩

private lemma reVec_apply {A B : Type} (e : A ≃ B) (f : Hilbert A) (b : B) :
    reVec e f b = f (e.symm b) := rfl

private lemma norm_reVec {A B : Type} (e : A ≃ B) (f : Hilbert A) : ‖reVec e f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num) (reVec e f), lp.norm_eq_tsum_rpow (by norm_num) f]
  congr 1
  exact Equiv.tsum_eq e.symm (fun a => ‖f a‖ ^ (2 : ℝ≥0∞).toReal)

theorem solution {A B : Type} (e : A ≃ B) {X : Matrix A A ℂ} (hX : IsDensity X) :
    IsDensity (fun i j : B => X (e.symm i) (e.symm j)) := by
  obtain ⟨⟨ex⟩, hpos, hsum, htr⟩ := hX
  refine ⟨⟨{
    left := fun n => reVec e (ex.left n)
    right := fun n => reVec e (ex.right n)
    summable := by simpa [norm_reVec] using ex.summable
    coefficients := fun i j => by
      simpa [reVec_apply] using ex.coefficients (e.symm i) (e.symm j) }⟩, ?_, ?_, ?_⟩
  · intro s z
    have h := hpos (s.map e.symm.toEmbedding) (fun a => z (e a))
    simpa [Finset.sum_map] using h
  · exact hsum.comp_injective e.symm.injective
  · rw [← htr]
    exact Equiv.tsum_eq e.symm (fun a => (X a a).re)
