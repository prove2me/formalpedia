-- Prove2me | solution 1 for DimensionalCollapse.linear_weight_flow
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T13:47:35.858278+00:00
-- url     : https://prove2.me/submissions/d9bfe71d-b917-43d4-8748-263438359d7c

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic
set_option autoImplicit false
open Matrix
namespace DimensionalCollapse

lemma lw_partition_pos {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) : 0 < partitionZ z z' i := by
  unfold partitionZ; positivity

lemma lw_diff (N d : ℕ) :
    Differentiable ℝ (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) => infoNCE p.1 p.2) := by
  intro p
  unfold infoNCE
  apply DifferentiableAt.neg
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.log
  · unfold partitionZ sqNorm
    fun_prop (disch := positivity)
  · exact (div_pos (Real.exp_pos _) (lw_partition_pos _ _ i)).ne'

lemma lw_dir (N d : ℕ) (p v : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ)) :
    deriv (fun s : ℝ => infoNCE (p + s • v).1 (p + s • v).2) 0 =
      fderiv ℝ (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) => infoNCE p.1 p.2) p v := by
  have hg : HasDerivAt (fun s : ℝ => p + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have h := ((lw_diff N d) (p + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  simp only [zero_smul, add_zero, one_smul] at h
  exact h.deriv

lemma lw_upd {N d : ℕ} (z : Fin N → Fin d → ℝ) (i : Fin N) (c : Fin d) (s : ℝ) :
    Function.update z i (z i + s • Pi.single c 1) =
      z + s • (Pi.single i (Pi.single c (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ) := by
  funext j; by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, h]

lemma lw_gradZ {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) (c : Fin d) :
    gradZ z z' i c = fderiv ℝ (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) => infoNCE p.1 p.2)
      (z, z') ((Pi.single i (Pi.single c (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ), 0) := by
  rw [← lw_dir]; unfold gradZ; simp_rw [lw_upd]; simp

lemma lw_gradZ' {N d : ℕ} (z z' : Fin N → Fin d → ℝ) (i : Fin N) (c : Fin d) :
    gradZ' z z' i c = fderiv ℝ (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) => infoNCE p.1 p.2)
      (z, z') (0, (Pi.single i (Pi.single c (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ)) := by
  rw [← lw_dir]; unfold gradZ'; simp_rw [lw_upd]; simp

lemma lw_embed {N n d : ℕ} (W : Matrix (Fin d) (Fin n) ℝ) (x : Fin N → Fin n → ℝ) (a : Fin d) (b : Fin n)
    (s : ℝ) : embed (W + s • Matrix.single a b 1) x =
      embed W x + s • ∑ i, x i b • (Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ) := by
  funext i c
  simp [embed, Finset.sum_apply, Pi.single_apply, Matrix.mulVec, dotProduct,
    Matrix.single_apply]
  simp_rw [add_mul, Finset.sum_add_distrib, add_right_inj]
  by_cases h : c = a
  · subst h; simp [Finset.sum_ite_eq', ite_mul]
  · have : a ≠ c := Ne.symm h
    simp [this, h]

theorem linear_weight_flow {N n d : ℕ} (x x' : Fin N → Fin n → ℝ)
    (W : ℝ → Matrix (Fin d) (Fin n) ℝ) (t : ℝ)
    (hW : ∀ a b, HasDerivAt (fun s => W s a b) (-(matGrad (linLoss x x') (W t)) a b) t) :
    ∀ a b, HasDerivAt (fun s => W s a b) (-(Gmat x x' (W t)) a b) t := by
  intro a b
  convert hW a b using 3
  unfold matGrad linLoss
  simp only [Matrix.of_apply, Gmat]
  simp_rw [lw_embed]
  have := lw_dir N d (embed (W t) x, embed (W t) x')
    (∑ i, x i b • (Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ), ∑ i, x' i b • (Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ))
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at this
  rw [this]
  have hv : (∑ i, x i b • (Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ), ∑ i, x' i b • (Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ)) =
      ∑ i, (x i b • ((Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ), (0 : Fin N → Fin d → ℝ)) + x' i b • ((0 : Fin N → Fin d → ℝ), (Pi.single i (Pi.single a (1:ℝ) : Fin d → ℝ) : Fin N → Fin d → ℝ))) := by
    refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [hv, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul, map_smul, lw_gradZ, lw_gradZ', smul_eq_mul, smul_eq_mul]
  ring

end DimensionalCollapse
open DimensionalCollapse in
theorem solution {N n d : ℕ} (x x' : Fin N → Fin n → ℝ)
    (W : ℝ → Matrix (Fin d) (Fin n) ℝ) (t : ℝ)
    (hW : ∀ a b, HasDerivAt (fun s => W s a b) (-(matGrad (linLoss x x') (W t)) a b) t) :
    ∀ a b, HasDerivAt (fun s => W s a b) (-(Gmat x x' (W t)) a b) t :=
  linear_weight_flow x x' W t hW
