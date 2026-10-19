-- Prove2me | solution 1 for DSGE.bounded_orbits_zero_iff_eigenvalues_outside
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:45:35.101593+00:00
-- url     : https://prove2.me/submissions/8f0237ae-cb92-48e8-9664-d7454be38787

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

open Module.End

private def boundedVectors {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∃ C : ℝ, ∀ t : ℕ, ‖(f ^ t) v‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C+D, fun t => by simpa only [map_add] using
      (norm_add_le ((f^t) v) ((f^t) w)).trans (add_le_add (hC t) (hD t))⟩
  smul_mem' := by
    rintro c v ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun t => ?_⟩
    simpa only [map_smul, norm_smul] using
      (mul_le_mul_of_nonneg_left (hC t) (norm_nonneg c))

private lemma boundedVectors_invariant {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    ∀ v ∈ boundedVectors f, f v ∈ boundedVectors f := by
  rintro v ⟨C, hC⟩
  refine ⟨C, fun t => ?_⟩
  simpa only [pow_succ, Module.End.mul_apply, Module.End.one_apply] using hC (t+1)

private lemma eigenvalue_le_one_of_bounded {n : ℕ} (f : Module.End ℂ (Fin n → ℂ))
    {μ : ℂ} {v : Fin n → ℂ} (hv : f.HasEigenvector μ v)
    (hb : v ∈ boundedVectors f) : ‖μ‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hb
  by_contra h
  have hμ : 1 < ‖μ‖ := lt_of_not_ge h
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (C / ‖v‖) hμ
  have hbound := hC t
  rw [hv.pow_apply, norm_smul, norm_pow] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hvpos).mp ht)

private lemma eigenvalue_iff_root {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue A.toLin' μ ↔ A.charpoly.IsRoot μ := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    Matrix.mem_spectrum_iff_isRoot_charpoly]

private lemma no_bounded_vector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ μ : ℂ, A.charpoly.IsRoot μ → 1 < ‖μ‖) :
    ∀ v ∈ boundedVectors A.toLin', v = 0 := by
  intro v hv
  by_contra hne
  let W := boundedVectors A.toLin'
  have : Nontrivial W := nontrivial_of_ne (⟨v, hv⟩ : W) 0
    (fun h => hne (congrArg Subtype.val h))
  let g : Module.End ℂ W := A.toLin'.restrict (boundedVectors_invariant A.toLin')
  obtain ⟨μ, hμ⟩ := g.exists_eigenvalue
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have heq : A.toLin' (w : Fin n → ℂ) = μ • (w : Fin n → ℂ) :=
    congrArg Subtype.val hw.apply_eq_smul
  have hwne : (w : Fin n → ℂ) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw' : Module.End.HasEigenvector A.toLin' μ (w : Fin n → ℂ) :=
    ⟨Module.End.mem_eigenspace_iff.mpr heq, hwne⟩
  have hroot := (eigenvalue_iff_root A μ).mp (hasEigenvalue_of_hasEigenvector hw')
  exact (not_lt_of_ge (eigenvalue_le_one_of_bounded A.toLin' hw' w.property)) (hA μ hroot)

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : ℕ → Fin n → ℝ, (∀ t : ℕ, x (t + 1) = M.mulVec (x t)) →
        (∃ C : ℝ, ∀ t : ℕ, ∀ j : Fin n, |x t j| ≤ C) → ∀ t : ℕ, x t = 0) ↔
      ∀ μ : ℂ, (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot μ → 1 < ‖μ‖ := by
  let A := M.map (algebraMap ℝ ℂ)
  let f := A.toLin'
  constructor
  · intro h μ hroot
    by_contra hμ
    have hle : ‖μ‖ ≤ 1 := le_of_not_gt hμ
    obtain ⟨v, hv⟩ := ((eigenvalue_iff_root A μ).mpr hroot).exists_hasEigenvector
    let z : ℕ → Fin n → ℂ := fun t => (f^t) v
    have hz (t : ℕ) : z (t+1) = A.mulVec (z t) := by
      change (f^(t+1)) v = f ((f^t) v)
      rw [pow_succ', Module.End.mul_apply]
    have hnorm (t : ℕ) (j : Fin n) : ‖z t j‖ ≤ ‖v‖ := by
      apply (norm_le_pi_norm (z t) j).trans
      change ‖(f^t) v‖ ≤ ‖v‖
      rw [hv.pow_apply, norm_smul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg v) (pow_le_one₀ (norm_nonneg μ) hle)
    have hre : ∀ t, (fun j => (z (t+1) j).re) = M.mulVec (fun j => (z t j).re) := by
      intro t
      ext j
      rw [hz]
      simp [A, Matrix.mulVec, dotProduct, Complex.mul_re]
    have him : ∀ t, (fun j => (z (t+1) j).im) = M.mulVec (fun j => (z t j).im) := by
      intro t
      ext j
      rw [hz]
      simp [A, Matrix.mulVec, dotProduct, Complex.mul_im]
    have hzr := h (fun t j => (z t j).re) hre
      ⟨‖v‖, fun t j => (Complex.abs_re_le_norm (z t j)).trans (hnorm t j)⟩
    have hzi := h (fun t j => (z t j).im) him
      ⟨‖v‖, fun t j => (Complex.abs_im_le_norm (z t j)).trans (hnorm t j)⟩
    apply hv.2
    ext j
    apply Complex.ext
    · simpa [z, f] using congrFun (hzr 0) j
    · simpa [z, f] using congrFun (hzi 0) j
  · intro hA x hx ⟨C, hC⟩ t
    let z : ℕ → Fin n → ℂ := fun t j => (x t j : ℂ)
    have hz (k : ℕ) : z (k+1) = f (z k) := by
      ext j
      change (x (k+1) j : ℂ) = _
      rw [hx k]
      simp [z, f, A, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    have hpow (k : ℕ) : (f^k) (z t) = z (t+k) := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, ← hz]; rfl
    have hCt : 0 ≤ max C 0 := le_max_right _ _
    have hb : z t ∈ boundedVectors f := by
      refine ⟨max C 0, fun k => ?_⟩
      rw [hpow]
      apply (pi_norm_le_iff_of_nonneg hCt).mpr
      intro j
      simpa only [z, Complex.norm_real, Real.norm_eq_abs] using
        (hC (t+k) j).trans (le_max_left C 0)
    have hzero := no_bounded_vector A hA (z t) hb
    ext j
    have hj : (x t j : ℂ) = 0 := congrFun hzero j
    exact Complex.ofReal_injective hj
