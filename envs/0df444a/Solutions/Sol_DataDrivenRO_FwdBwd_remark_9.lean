-- Prove2me | solution 1 for DataDrivenRO.FwdBwd.remark_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:50:16.803338+00:00
-- url     : https://prove2.me/submissions/b3b9db43-229e-424f-a09a-58654591f2b7

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

set_option autoImplicit false
open DataDrivenRO.FwdBwd

theorem solution {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) (hv : v ≠ 0) (t : ℝ) (ht : t < fbValue mb mf sf sb ε v) :
    let lam : ℝ := Real.sqrt ((∑ i, if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) /
      (2 * Real.log (1 / ε)))
    let u : Fin d → ℝ := fun i =>
      if 0 < v i then mf i + v i * sf i ^ 2 / lam else mb i + v i * sb i ^ 2 / lam
    u ∈ UFB mb mf sf sb ε ∧ t < u ⬝ᵥ v := by
  intro lam u
  have hL : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε0]; linarith
  have hSpos : 0 < ∑ i, (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hnn : ∀ i, 0 ≤ (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) := by
      intro i; split_ifs <;> positivity
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j))
    have hv2 : 0 < v j ^ 2 := by positivity
    split_ifs
    · exact mul_pos hv2 (pow_pos (hsf j) 2)
    · exact mul_pos hv2 (pow_pos (hsb j) 2)
  set S : ℝ := ∑ i, (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) with hS
  have hlam2 : lam ^ 2 = S / (2 * Real.log (1 / ε)) := Real.sq_sqrt (by positivity)
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hconstr : ∑ i, ((if 0 < v i then v i * sf i ^ 2 / lam else 0) ^ 2 / (2 * sf i ^ 2) +
      (if 0 < v i then 0 else -(v i * sb i ^ 2 / lam)) ^ 2 / (2 * sb i ^ 2)) = Real.log (1 / ε) := by
    have h1 : ∀ i, ((if 0 < v i then v i * sf i ^ 2 / lam else 0) ^ 2 / (2 * sf i ^ 2) +
      (if 0 < v i then 0 else -(v i * sb i ^ 2 / lam)) ^ 2 / (2 * sb i ^ 2))
        = (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) / (2 * lam ^ 2) := by
      intro i
      have := (hsf i).ne'
      have := (hsb i).ne'
      split_ifs <;> field_simp <;> ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_div, ← hS, hlam2]
    field_simp
  have hval : u ⬝ᵥ v = fbValue mb mf sf sb ε v := by
    unfold fbValue
    have e1 : ∀ i, u i * v i = (if 0 ≤ v i then mf i * v i else mb i * v i) +
        (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) / lam := by
      intro i
      simp only [u]
      rcases lt_trichotomy (v i) 0 with h | h | h
      · rw [if_neg (not_lt.mpr h.le), if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le)]
        field_simp
      · simp [h]
      · rw [if_pos h, if_pos h.le, if_pos h]
        field_simp
    have e2 : ∀ i, (if 0 ≤ v i then sf i ^ 2 * v i ^ 2 else sb i ^ 2 * v i ^ 2) =
        (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) := by
      intro i
      rcases lt_trichotomy (v i) 0 with h | h | h
      · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le)]; ring
      · simp [h]
      · rw [if_pos h.le, if_pos h]; ring
    have e3 : Real.sqrt (2 * Real.log (1 / ε) * S) = S / lam := by
      have : (S / lam) ^ 2 = 2 * Real.log (1 / ε) * S := by
        rw [div_pow, hlam2]; field_simp
      rw [← this, Real.sqrt_sq (by positivity)]
    rw [dotProduct, Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_congr rfl (fun i _ => e2 i), ← hS, e3]
  refine ⟨⟨fun i => if 0 < v i then mf i else mb i, fun i => if 0 < v i then v i * sf i ^ 2 / lam else 0,
    fun i => if 0 < v i then 0 else -(v i * sb i ^ 2 / lam), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    show 0 ≤ if 0 < v i then v i * sf i ^ 2 / lam else 0
    split_ifs with h
    · have := hsf i; positivity
    · exact le_refl _
  · intro i
    show 0 ≤ if 0 < v i then (0 : ℝ) else -(v i * sb i ^ 2 / lam)
    split_ifs with h
    · exact le_refl _
    · have h1 : v i ≤ 0 := not_lt.mp h
      have h2 : 0 ≤ -v i := by linarith
      have h3 : 0 ≤ (-v i) * sb i ^ 2 / lam := by have := hsb i; positivity
      calc (0 : ℝ) ≤ (-v i) * sb i ^ 2 / lam := h3
        _ = -(v i * sb i ^ 2 / lam) := by ring
  · intro i
    by_cases h : 0 < v i
    · simp only [if_pos h]; exact ⟨hm i, le_refl _⟩
    · simp only [if_neg h]; exact ⟨le_refl _, hm i⟩
  · exact hconstr.le
  · funext i
    simp only [u, Pi.add_apply, Pi.sub_apply]
    by_cases h : 0 < v i
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  · rw [hval]; exact ht
