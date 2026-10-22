-- Prove2me | solution 1 for CompOT.Barycenter.g_block_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:06:17.299869+00:00
-- url     : https://prove2.me/submissions/54f910de-5b25-4640-a395-55d6d19b5947

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs
set_option autoImplicit false
open CompOT.Barycenter

lemma ss_gb_rewrite {n m : ℕ} (ε : ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    gBlockObjective ε C b f g =
      ∑ j, (g j * b j - ε * ((∑ i, gibbs ε C i j * Real.exp (f i / ε)) * Real.exp (g j / ε))) := by
  unfold gBlockObjective
  rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun i j => Real.exp (f i / ε) * gibbs ε C i j * Real.exp (g j / ε)),
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (hbSimplex : b ∈ stdSimplex ℝ (Fin m))
    (hb : ∀ j, 0 < b j) (f : Fin n → ℝ) :
    (∀ g : Fin m → ℝ,
      gBlockObjective ε C b f g ≤
        gBlockObjective ε C b f (gBlockUpdate ε C b f)) ∧
    (∀ j, Real.exp (gBlockUpdate ε C b f j / ε) =
      b j / (∑ i, gibbs ε C i j * Real.exp (f i / ε))) := by
  have hcpos : ∀ j, 0 < ∑ i, gibbs ε C i j * Real.exp (f i / ε) := by
    intro j
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  have hexp : ∀ j, Real.exp (gBlockUpdate ε C b f j / ε) =
      b j / (∑ i, gibbs ε C i j * Real.exp (f i / ε)) := by
    intro j
    unfold gBlockUpdate
    rw [mul_div_cancel_left₀ _ hε.ne', Real.exp_log (div_pos (hb j) (hcpos j))]
  refine ⟨fun g => ?_, hexp⟩
  rw [ss_gb_rewrite, ss_gb_rewrite]
  refine Finset.sum_le_sum fun j _ => ?_
  set c := ∑ i, gibbs ε C i j * Real.exp (f i / ε) with hc
  have hcp : 0 < c := hcpos j
  have hcne : c ≠ 0 := hcp.ne'
  have hbj := hb j
  have hg : Real.exp (gBlockUpdate ε C b f j / ε) = b j / c := hexp j
  set x := g j / ε with hx
  set y := gBlockUpdate ε C b f j / ε with hy
  have hgx : g j = ε * x := by rw [hx]; field_simp
  have hgy : gBlockUpdate ε C b f j = ε * y := by rw [hy]; field_simp
  rw [hgx, hgy, hg]
  have hy' : y = Real.log (b j / c) := by
    rw [← Real.log_exp y, hg]
  have hex : Real.exp x = Real.exp (x - y) * (b j / c) := by
    rw [← hg, ← Real.exp_add]; ring_nf
  have hle := Real.add_one_le_exp (x - y)
  have hcb : c * (b j / c) = b j := by field_simp
  have h1 : c * Real.exp x = Real.exp (x - y) * b j := by
    rw [hex]; field_simp
  have h2 : y = Real.log (b j / c) := hy'
  -- goal: ε x b - ε (c e^x) ≤ ε y b - ε (c (b/c))
  have : x * b j - c * Real.exp x ≤ y * b j - b j := by
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_right hle hbj.le]
  nlinarith [mul_le_mul_of_nonneg_left this hε.le]
