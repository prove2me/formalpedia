-- Prove2me | solution 1 for CompOT.Sinkhorn.thm_4_2_proof_invariance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:38:02.102485+00:00
-- url     : https://prove2.me/submissions/6ef0de96-90b6-46ea-9bed-843f7ae8a217

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

set_option autoImplicit false
open CompOT.Sinkhorn

theorem hil_eq {n : ℕ} (hn : 0 < n) (u u' : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i) :
    hilbertMetric u u' = varNorm (fun i => Real.log (u i) - Real.log (u' i)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f : Fin n → ℝ := fun i => Real.log (u i) - Real.log (u' i) with hf
  obtain ⟨i0, hi0⟩ := Finite.exists_max f
  obtain ⟨j0, hj0⟩ := Finite.exists_min f
  set r : Fin n → ℝ := fun i => u i / u' i with hr
  have hrpos : ∀ i, 0 < r i := fun i => div_pos (hu i) (hu' i)
  have hlogr : ∀ i, Real.log (r i) = f i := fun i => by
    simp only [hr, hf]; rw [Real.log_div (hu i).ne' (hu' i).ne']
  have hrle : ∀ i j, f i ≤ f j → r i ≤ r j := by
    intro i j h
    rw [← hlogr, ← hlogr] at h
    exact (Real.log_le_log_iff (hrpos i) (hrpos j)).1 h
  set g : Fin n → Fin n → ℝ := fun i j => u i * u' j / (u j * u' i) with hg
  have hgr : ∀ i j, g i j = r i / r j := by
    intro i j
    simp only [hg, hr]
    have := (hu i).ne'; have := (hu' i).ne'; have := (hu j).ne'; have := (hu' j).ne'
    field_simp
  have hsup : (⨆ i, ⨆ j, g i j) = g i0 j0 := by
    apply le_antisymm
    · refine ciSup_le (fun i => ciSup_le (fun j => ?_))
      rw [hgr, hgr]
      have h1 := hrle _ _ (hi0 i)
      have h2 := hrle _ _ (hj0 j)
      have := hrpos i; have := hrpos j; have := hrpos i0; have := hrpos j0
      rw [div_le_div_iff₀ (hrpos j) (hrpos j0)]
      nlinarith [mul_le_mul h1 h2 (hrpos j0).le (hrpos i0).le]
    · exact le_trans (le_ciSup (f := fun j => g i0 j) (Set.finite_range _).bddAbove j0)
        (le_ciSup (f := fun i => ⨆ j, g i j) (Set.finite_range _).bddAbove i0)
  have hmax : (⨆ i, f i) = f i0 :=
    le_antisymm (ciSup_le hi0) (le_ciSup (Set.finite_range f).bddAbove i0)
  have hmin : (⨅ i, f i) = f j0 :=
    le_antisymm (ciInf_le (Set.finite_range f).bddBelow j0) (le_ciInf hj0)
  unfold hilbertMetric varNorm
  rw [hsup, hmax, hmin]
  simp only [hg]
  rw [Real.log_div (mul_pos (hu i0) (hu' j0)).ne' (mul_pos (hu j0) (hu' i0)).ne',
    Real.log_mul (hu i0).ne' (hu' j0).ne', Real.log_mul (hu j0).ne' (hu' i0).ne']
  simp only [hf]
  ring

lemma varNorm_eq {n : ℕ} (f : Fin n → ℝ) (i0 j0 : Fin n) (hi : ∀ i, f i ≤ f i0)
    (hj : ∀ j, f j0 ≤ f j) : varNorm f = f i0 - f j0 := by
  have : Nonempty (Fin n) := ⟨i0⟩
  unfold varNorm
  rw [le_antisymm (ciSup_le hi) (le_ciSup (Set.finite_range f).bddAbove i0),
    le_antisymm (ciInf_le (Set.finite_range f).bddBelow j0) (le_ciInf hj)]

lemma sub_le_varNorm {n : ℕ} (f : Fin n → ℝ) (i j : Fin n) : f i - f j ≤ varNorm f := by
  have : Nonempty (Fin n) := ⟨i⟩
  unfold varNorm
  have h1 := le_ciSup (Set.finite_range f).bddAbove i
  have h2 := ciInf_le (Set.finite_range f).bddBelow j
  linarith

lemma varNorm_exists {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ i0 j0, varNorm f = f i0 - f j0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max f
  obtain ⟨j0, hj0⟩ := Finite.exists_min f
  exact ⟨i0, j0, varNorm_eq f i0 j0 hi0 hj0⟩

lemma varNorm_neg {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : varNorm (fun i => - f i) = varNorm f := by
  obtain ⟨i0, j0, h⟩ := varNorm_exists hn (fun i => - f i)
  obtain ⟨i1, j1, h1⟩ := varNorm_exists hn f
  apply le_antisymm
  · rw [h]; have := sub_le_varNorm f j0 i0; linarith
  · rw [h1]
    have := sub_le_varNorm (fun i => - f i) j1 i1; linarith

lemma varNorm_nonneg {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : 0 ≤ varNorm f := by
  have := sub_le_varNorm f ⟨0, hn⟩ ⟨0, hn⟩; linarith

theorem solution {m : ℕ} (hm : 0 < m) (v v' : Fin m → ℝ)
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) :
    hilbertMetric v v' = hilbertMetric (v / v') 1 ∧
    hilbertMetric v v' = hilbertMetric (1 / v) (1 / v') ∧
    ∀ c : Fin m → ℝ, (∀ j, 0 < c j) → hilbertMetric (c * v) (c * v') = hilbertMetric v v' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hil_eq hm v v' hv hv', hil_eq hm (v / v') 1 (fun i => div_pos (hv i) (hv' i))
      (fun _ => one_pos)]
    congr 1
    funext i
    simp [Real.log_div (hv i).ne' (hv' i).ne']
  · rw [hil_eq hm v v' hv hv', hil_eq hm (1 / v) (1 / v') (fun i => one_div_pos.2 (hv i))
      (fun i => one_div_pos.2 (hv' i)), ← varNorm_neg hm]
    congr 1
    funext i
    simp [Real.log_inv]
    ring
  · intro c hc
    rw [hil_eq hm v v' hv hv', hil_eq hm (c * v) (c * v') (fun i => mul_pos (hc i) (hv i))
      (fun i => mul_pos (hc i) (hv' i))]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    rw [Real.log_mul (hc i).ne' (hv i).ne', Real.log_mul (hc i).ne' (hv' i).ne']
    ring
