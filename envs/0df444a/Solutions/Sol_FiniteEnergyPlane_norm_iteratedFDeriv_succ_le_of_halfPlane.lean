-- Prove2me | solution 1 for FiniteEnergyPlane.norm_iteratedFDeriv_succ_le_of_halfPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T20:49:52.899765+00:00
-- url     : https://prove2.me/submissions/14b60ae5-8556-4888-9918-66d13c0b7654

import Mathlib



namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- On a half-plane `{s > s₀}`, the norm of the `(j+1)`-st derivative of a smooth map at `p` is
bounded by `2 (2A/h + Bh)` for every `h > 0`, where `A` and `B` bound the `j`-th and `(j+2)`-nd
derivatives on `{s ≥ p.1}`. -/
theorem norm_iteratedFDeriv_succ_le_of_halfPlane_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s₀ : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) (j : ℕ) (p : ℝ × ℝ) (hp : s₀ < p.1)
    (A B h : ℝ) (hh : 0 < h)
    (hA : ∀ q : ℝ × ℝ, p.1 ≤ q.1 → ‖iteratedFDeriv ℝ j f q‖ ≤ A)
    (hB : ∀ q : ℝ × ℝ, p.1 ≤ q.1 → ‖iteratedFDeriv ℝ (j + 2) f q‖ ≤ B) :
    ‖iteratedFDeriv ℝ (j + 1) f p‖ ≤ 2 * (2 * A / h + B * h) := by
  set K : Set (ℝ × ℝ) := closedBall p h ∩ (Set.Ici p.1 ×ˢ Set.univ) with hKdef
  have hKc : Convex ℝ K := (convex_closedBall p h).inter ((convex_Ici p.1).prod convex_univ)
  have memK : ∀ z : ℝ × ℝ, z ∈ K ↔ dist z p ≤ h ∧ p.1 ≤ z.1 := by
    intro z; simp [hKdef, Set.mem_prod]
  have pK : p ∈ K := (memK p).2 ⟨by simp [hh.le], le_rfl⟩
  have hdiff : ∀ k : ℕ, ∀ z ∈ K, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z := by
    intro k z hz
    have hz1 : s₀ < z.1 := lt_of_lt_of_le hp ((memK z).1 hz).2
    have hU : Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ∈ nhds z :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz1, trivial⟩
    exact (hf.contDiffAt hU).differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.coe_lt_top k)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB p le_rfl)
  have hLip : ∀ z ∈ K, ‖iteratedFDeriv ℝ (j + 1) f z - iteratedFDeriv ℝ (j + 1) f p‖ ≤
      B * ‖z - p‖ := by
    intro z hz
    refine hKc.norm_image_sub_le_of_norm_fderiv_le (hdiff (j + 1)) (fun x hx => ?_) pK hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hB x ((memK x).1 hx).2
  set G := iteratedFDeriv ℝ j f with hG
  set L := fderiv ℝ G p with hL
  have hfd : ∀ z ∈ K, ‖fderiv ℝ G z - L‖ ≤ B * h := by
    intro z hz
    rw [hL, hG, fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply,
      ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
    refine (hLip z hz).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [← dist_eq_norm]; exact ((memK z).1 hz).1
  have hdir : ∀ e : ℝ × ℝ, ‖e‖ = 1 → 0 ≤ e.1 → ‖L e‖ ≤ 2 * A / h + B * h := by
    intro e he he1
    have hq : p + h • e ∈ K := by
      refine (memK _).2 ⟨?_, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_pos hh,
          mul_one]
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        nlinarith
    have hmv := hKc.norm_image_sub_le_of_norm_fderiv_le' (f := G) (φ := L) (hdiff j) hfd pK hq
    rw [add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_pos hh, mul_one] at hmv
    have key : L (h • e) = (G (p + h • e) - G p) - (G (p + h • e) - G p - L (h • e)) := by abel
    have hnorm : h * ‖L e‖ ≤ 2 * A + B * h * h := by
      have h1 : ‖L (h • e)‖ ≤ ‖G (p + h • e)‖ + ‖G p‖ + B * h * h := by
        rw [key]
        refine (norm_sub_le _ _).trans ?_
        have := norm_sub_le (G (p + h • e)) (G p)
        linarith
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at h1
      have := hA _ ((memK _).1 hq).2
      have := hA p le_rfl
      linarith
    have hrw : 2 * A / h + B * h = (2 * A + B * h * h) / h := by field_simp
    rw [hrw, le_div_iff₀ hh]
    linarith
  have h1 := hdir (1, 0) (by simp [Prod.norm_def]) (by norm_num)
  have h2 := hdir (0, 1) (by simp [Prod.norm_def]) (by norm_num)
  rw [← norm_fderiv_iteratedFDeriv]
  have hbound : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound L (by positivity) (fun v => ?_)
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have a1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
    have a2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
    have hv' : ‖v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))‖ = ‖v‖ := by rw [← hv]
    rw [hv']
    nlinarith [norm_nonneg (L (1, 0)), norm_nonneg (L (0, 1))]
  exact hbound.trans (by linarith)

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s₀ : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) (j : ℕ) (p : ℝ × ℝ) (hp : s₀ < p.1)
    (A B h : ℝ) (hh : 0 < h)
    (hA : ∀ q : ℝ × ℝ, p.1 ≤ q.1 → ‖iteratedFDeriv ℝ j f q‖ ≤ A)
    (hB : ∀ q : ℝ × ℝ, p.1 ≤ q.1 → ‖iteratedFDeriv ℝ (j + 2) f q‖ ≤ B) :
    ‖iteratedFDeriv ℝ (j + 1) f p‖ ≤ 2 * (2 * A / h + B * h) :=
  norm_iteratedFDeriv_succ_le_of_halfPlane_aux f s₀ hf j p hp A B h hh hA hB
