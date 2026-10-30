-- Prove2me | solution 1 for ExactPenGNEP.NonShared.theorem_11_descent_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:45:45.557904+00:00
-- url     : https://prove2.me/submissions/18874fb0-bd63-4b39-bc41-a82a40b5f234

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting
import Theorems.Thm_ExactPenGNEP_NonShared_eq_5_gradient

open LeiBR.Sync ExactPenGNEP.NonShared

lemma epg_affine_update_diff {N : ℕ} {n : Fin N → ℕ} (f : Profile n →ᵃ[ℝ] ℝ) (x : Profile n)
    (ν : Fin N) : Differentiable ℝ (fun y : Strat n ν => f (Function.update x ν y)) := by
  let F : Profile n →ᴬ[ℝ] ℝ := ⟨f, f.continuous_of_finiteDimensional⟩
  have hF : Differentiable ℝ (fun z : Profile n => f z) := F.differentiable
  intro y
  exact (hF _).comp y (hasFDerivAt_update x y).differentiableAt

theorem solution {N : ℕ} {n m p : Fin N → ℕ}
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ)
    (q α c : ℝ) (x : Profile n) (νh : Fin N) (xh : Strat n νh)
    (hq : 1 < q) (hα : 0 < α)
    (hg_diff : ∀ i, Differentiable ℝ (fun y => g νh i (Function.update x νh y)))
    (hx : x νh ∉ frSet g h νh x)
    (hg_bullet : ∀ i, 0 < g νh i x →
      fderiv ℝ (fun y => g νh i (Function.update x νh y)) (x νh) (xh - x νh) ≤ -α)
    (hh_bullet : ∀ j, h νh j x ≠ 0 →
      Real.sign (h νh j x) *
        fderiv ℝ (fun y => h νh j (Function.update x νh y)) (x νh) (xh - x νh) ≤ -α)
    (hc : 0 < c)
    (hcq : ∀ (k : ℕ) (v : Fin k → ℝ),
      c * (∑ i, |v i| ^ q) ^ (1 / q) ≤ (∑ i, |v i| ^ (q - 1)) ^ (1 / (q - 1))) :
    fderiv ℝ (fun y => lqRes (g νh) (fun j z => h νh j z) q (Function.update x νh y)) (x νh)
        (xh - x νh)
      ≤ -α * (lqRes (g νh) (fun j z => h νh j z) (q - 1) x /
          lqRes (g νh) (fun j z => h νh j z) q x) ^ (q - 1) ∧
    -α * (lqRes (g νh) (fun j z => h νh j z) (q - 1) x /
          lqRes (g νh) (fun j z => h νh j z) q x) ^ (q - 1) ≤ -α * c ^ (q - 1) := by
  classical
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  -- block functions
  let G : Fin (m νh) → Strat n νh → ℝ := fun i y => g νh i (Function.update x νh y)
  let H : Fin (p νh) → Strat n νh → ℝ := fun j y => h νh j (Function.update x νh y)
  have hGd : ∀ i, Differentiable ℝ (G i) := hg_diff
  have hHd : ∀ j, Differentiable ℝ (H j) := fun j => epg_affine_update_diff (h νh j) x νh
  have hGx : ∀ i, G i (x νh) = g νh i x := fun i => by simp [G]
  have hHx : ∀ j, H j (x νh) = h νh j x := fun j => by simp [H]
  have hxS : x νh ∉ {y | (∀ i, G i y ≤ 0) ∧ ∀ j, H j y = 0} := by
    intro hmem
    apply hx
    exact hmem
  have hD := eq_5_gradient G H q (x νh) hGd hHd hq hxS
  have hfun : (fun y => lqRes (g νh) (fun j z => h νh j z) q (Function.update x νh y)) =
      lqRes G H q := rfl
  rw [hfun, hD.fderiv]
  -- notation
  set R := lqRes (g νh) (fun j z => h νh j z) q x with hR
  set R1 := lqRes (g νh) (fun j z => h νh j z) (q - 1) x with hR1
  have hRG : lqRes G H q (x νh) = R := by simp [lqRes, hR, hGx, hHx]
  set T := ∑ i, (max (g νh i x) 0) ^ (q - 1) + ∑ j, |h νh j x| ^ (q - 1) with hT
  have hT0 : 0 ≤ T := add_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_max_right _ _) _)
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hR1T : R1 ^ (q - 1) = T := by
    rw [hR1, lqRes, ← Real.rpow_mul hT0, one_div, inv_mul_cancel₀ hq1.ne', Real.rpow_one]
  -- positivity of R
  set S := ∑ i, (max (g νh i x) 0) ^ q + ∑ j, |h νh j x| ^ q with hS
  have hSpos : 0 < S := by
    simp only [frSet, Set.mem_ofPred_eq, not_and, not_forall] at hx
    by_cases hgi : ∃ i, 0 < g νh i x
    · obtain ⟨i, hi⟩ := hgi
      have hterm : 0 < (max (g νh i x) 0) ^ q := by
        rw [max_eq_left hi.le]; exact Real.rpow_pos_of_pos hi _
      have hle : (max (g νh i x) 0) ^ q ≤ ∑ i, (max (g νh i x) 0) ^ q :=
        Finset.single_le_sum (f := fun i => (max (g νh i x) 0) ^ q)
          (fun i _ => Real.rpow_nonneg (le_max_right _ _) _) (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ j, |h νh j x| ^ q :=
        Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      linarith
    · push Not at hgi
      have hgi' : ∀ i, g νh i (Function.update x νh (x νh)) ≤ 0 := by
        intro i; simpa using hgi i
      obtain ⟨j, hj⟩ := hx hgi'
      simp only [Function.update_eq_self] at hj
      have hterm : 0 < |h νh j x| ^ q := Real.rpow_pos_of_pos (abs_pos.mpr hj) _
      have hle : |h νh j x| ^ q ≤ ∑ j, |h νh j x| ^ q :=
        Finset.single_le_sum (f := fun j => |h νh j x| ^ q)
          (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ j)
      have h1 : 0 ≤ ∑ i, (max (g νh i x) 0) ^ q :=
        Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (le_max_right _ _) _)
      linarith
  have hRpos : 0 < R := by
    rw [hR, lqRes]; exact Real.rpow_pos_of_pos hSpos _
  have hR1nn : 0 ≤ R1 := by
    rw [hR1, lqRes]; exact Real.rpow_nonneg hT0 _
  -- the bracket bound
  set d := xh - x νh with hd
  have hbr : (∑ i, (max (G i (x νh)) 0) ^ (q - 1) • fderiv ℝ (G i) (x νh) +
        ∑ j, (|H j (x νh)| ^ (q - 1) * Real.sign (H j (x νh))) • fderiv ℝ (H j) (x νh)) d
      ≤ -α * T := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hGx, hHx]
    rw [hT, mul_add, Finset.mul_sum, Finset.mul_sum]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro i _
      by_cases hi : 0 < g νh i x
      · have := hg_bullet i hi
        have hpos : 0 ≤ (max (g νh i x) 0) ^ (q - 1) := Real.rpow_nonneg (le_max_right _ _) _
        change (max (g νh i x) 0) ^ (q - 1) * (fderiv ℝ (fun y => g νh i
          (Function.update x νh y)) (x νh) d) ≤ _
        nlinarith
      · push Not at hi
        rw [max_eq_right hi, Real.zero_rpow hq1.ne']
        simp
    · apply Finset.sum_le_sum
      intro j _
      by_cases hj : h νh j x = 0
      · rw [hj]; simp [Real.zero_rpow hq1.ne']
      · have := hh_bullet j hj
        have hpos : 0 ≤ |h νh j x| ^ (q - 1) := Real.rpow_nonneg (abs_nonneg _) _
        change |h νh j x| ^ (q - 1) * Real.sign (h νh j x) * (fderiv ℝ (fun y => h νh j
          (Function.update x νh y)) (x νh) d) ≤ _
        nlinarith
  have hRq : 0 < R ^ (q - 1) := Real.rpow_pos_of_pos hRpos _
  constructor
  · rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hRG, Real.div_rpow hR1nn hRpos.le, hR1T]
    calc 1 / R ^ (q - 1) * _ ≤ 1 / R ^ (q - 1) * (-α * T) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
      _ = -α * (T / R ^ (q - 1)) := by ring
  · -- c ≤ R1 / R
    have hv := hcq (m νh + p νh) (Fin.append (fun i => max (g νh i x) 0) (fun j => h νh j x))
    rw [Fin.sum_univ_add, Fin.sum_univ_add] at hv
    simp only [Fin.append_left, Fin.append_right] at hv
    have habs : ∀ i, |max (g νh i x) 0| = max (g νh i x) 0 :=
      fun i => abs_of_nonneg (le_max_right _ _)
    simp only [habs] at hv
    have hcR : c ≤ R1 / R := by
      rw [le_div_iff₀ hRpos]
      have : c * R ≤ R1 := by rw [hR, hR1]; exact hv
      linarith
    have : c ^ (q - 1) ≤ (R1 / R) ^ (q - 1) := Real.rpow_le_rpow hc.le hcR hq1.le
    nlinarith
