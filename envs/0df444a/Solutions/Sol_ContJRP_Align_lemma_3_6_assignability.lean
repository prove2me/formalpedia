-- Prove2me | solution 1 for ContJRP.Align.lemma_3_6_assignability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:03:12.039868+00:00
-- url     : https://prove2.me/submissions/34e753e5-3b63-40fd-9713-aba8794fa1c9

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active

open ContJRP.Align
open Classical

/-- `C` is nondecreasing on `[√(K/H), ∞)`. -/
theorem jrp36_mono (K H x y : ℝ) (hK : 0 < K) (hH : 0 < H)
    (hx : Real.sqrt (K / H) ≤ x) (hxy : x ≤ y) : eoqCost K H x ≤ eoqCost K H y := by
  have hs : 0 < Real.sqrt (K / H) := Real.sqrt_pos.mpr (div_pos hK hH)
  have hx0 : 0 < x := lt_of_lt_of_le hs hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hss : Real.sqrt (K / H) * Real.sqrt (K / H) = K / H :=
    Real.mul_self_sqrt (div_nonneg hK.le hH.le)
  have hxy2 : K / H ≤ x * y := by
    rw [← hss]
    exact mul_le_mul hx (le_trans hx hxy) hs.le hx0.le
  have hK' : K ≤ H * (x * y) := by
    rw [div_le_iff₀ hH] at hxy2; linarith
  unfold eoqCost
  rw [div_add' _ _ _ hx0.ne', div_add' _ _ _ hy0.ne', div_le_div_iff₀ hx0 hy0]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hK')]

/-- `C(√(K/H)) ≤ C(T)` for `T > 0` (AM-GM). -/
theorem jrp36_min (K H T : ℝ) (hK : 0 < K) (hH : 0 < H) (hT : 0 < T) :
    eoqCost K H (Real.sqrt (K / H)) ≤ eoqCost K H T := by
  set s := Real.sqrt (K / H) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hK hH)
  have hss : s * s = K / H := Real.mul_self_sqrt (div_nonneg hK.le hH.le)
  have hKs : K = H * (s * s) := by rw [hss]; field_simp
  unfold eoqCost
  rw [hKs]
  have e1 : H * (s * s) / s = H * s := by field_simp
  rw [e1, div_add' _ _ _ hT.ne', le_div_iff₀ hT]
  nlinarith [mul_nonneg hH.le (sq_nonneg (T - s))]

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (K H : Fin n → ℝ) (hK : ∀ i, 0 < K i) (hH : ∀ i, 0 < H i)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (That : Fin n → ℝ) (hThat : IsFinalPolicy K H ε Tt Tstar R That) :
    ∀ i, eoqCost (K i) (H i) (That i) ≤ (1 + 2 * ε) * eoqCost (K i) (H i) (Tstar i) := by
  intro i
  have htmin_pos : 0 < tmin Tstar := by
    unfold tmin
    rw [Finset.lt_inf'_iff]
    intro i _; exact hTstar i
  have hTt_pos : 0 < Tt := by
    have : 0 < (1 - ε / 2) * tmin Tstar := mul_pos (by linarith) htmin_pos
    linarith
  have hTi_ge : Tt ≤ Tstar i := by
    refine le_trans hTt2 ?_
    unfold tmin
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have h1ε : 0 < 1 + ε := by linarith
  have hKi := hK i
  have hHi := hH i
  have hTi := hTstar i
  have hCpos : 0 < eoqCost (K i) (H i) (Tstar i) := by unfold eoqCost; positivity
  have hmin : ∀ o ∈ options K H ε Tt Tstar R i, eoqCost (K i) (H i) (That i) ≤
      eoqCost (K i) (H i) o := (hThat i).2
  by_cases hsmall : ∃ ℓ < numSegments ε, Tstar i ∈ seg ε Tt ℓ
  · -- Regime 1: `T*_i` lies in an (active) segment
    obtain ⟨ℓ, hℓL, hℓ⟩ := hsmall
    have hact : ℓ ∈ active ε Tt Tstar := by
      unfold active
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hℓL, i, hℓ⟩
    have hRl := hfeas.1 ℓ hact
    have hopt : R ℓ ∈ options K H ε Tt Tstar R i := by
      unfold options
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem R hact)
    refine le_trans (hmin _ hopt) ?_
    unfold seg at hℓ
    unfold segClosed at hRl
    obtain ⟨ha1, ha2⟩ := hℓ
    obtain ⟨hb1, hb2⟩ := hRl
    set a := (1 + ε) ^ ℓ * Tt with ha
    have hapos : 0 < a := by positivity
    have hpow : (1 + ε) ^ (ℓ + 1) * Tt = (1 + ε) * a := by rw [ha]; ring
    rw [hpow] at ha2 hb2
    have hRpos : 0 < R ℓ := lt_of_lt_of_le hapos hb1
    have hb : eoqCost (K i) (H i) (R ℓ) ≤ (1 + ε) * eoqCost (K i) (H i) (Tstar i) := by
      unfold eoqCost
      have t1 : K i / R ℓ ≤ (1 + ε) * (K i / Tstar i) := by
        rw [mul_div_assoc', div_le_div_iff₀ hRpos hTi]
        have h' : Tstar i ≤ (1 + ε) * R ℓ := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h' hKi.le]
      have t2 : H i * R ℓ ≤ (1 + ε) * (H i * Tstar i) := by
        have h' : R ℓ ≤ (1 + ε) * Tstar i := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h' hHi.le]
      linarith
    have : (1 + ε) * eoqCost (K i) (H i) (Tstar i) ≤ (1 + 2 * ε) * eoqCost (K i) (H i) (Tstar i) :=
      mul_le_mul_of_nonneg_right (by linarith) hCpos.le
    linarith
  · -- Regimes 2 and 3: `T*_i` is large
    push Not at hsmall
    have hL : 1 / ε < (1 + ε) ^ numSegments ε := by
      have hne : {L : ℕ | 1 / ε < (1 + ε) ^ L}.Nonempty := by
        obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (1 / ε) (by linarith : (1 : ℝ) < 1 + ε)
        exact ⟨L, hL⟩
      exact Nat.sInf_mem hne
    have hind : ∀ ℓ ≤ numSegments ε, (1 + ε) ^ ℓ * Tt ≤ Tstar i := by
      intro ℓ
      induction ℓ with
      | zero => intro _; simpa using hTi_ge
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hsmall k (by omega)
        unfold seg at h2
        rw [Set.mem_Ico, not_and_or, not_le, not_lt] at h2
        rcases h2 with h2 | h2
        · exact absurd h2 (not_lt.mpr h1)
        · exact h2
    have hbig : Tt / ε < Tstar i := by
      have := hind _ le_rfl
      have h3 : Tt / ε < (1 + ε) ^ numSegments ε * Tt := by
        rw [div_lt_iff₀ hε0]
        rw [div_lt_iff₀ hε0] at hL
        nlinarith
      linarith
    -- the large option
    have h0act : 0 ∈ active ε Tt Tstar :=
      observation_2_3_first_segment_active ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2
    have hR0 := hfeas.1 0 h0act
    unfold segClosed at hR0
    simp only [pow_zero, one_mul, zero_add, pow_one] at hR0
    obtain ⟨hr1, hr2⟩ := hR0
    have hr : 0 < R 0 := lt_of_lt_of_le hTt_pos hr1
    set s := Real.sqrt (K i / H i) with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hKi hHi)
    set tm := tMax K H ε Tt i with htm
    have htm_def : tm = max (Tt / ε) s := rfl
    have htm_ge : s ≤ tm := by rw [htm_def]; exact le_max_right _ _
    have htm_ge' : Tt / ε ≤ tm := by rw [htm_def]; exact le_max_left _ _
    have htm_pos : 0 < tm := lt_of_lt_of_le hs htm_ge
    set x := roundUpMult tm (R 0) with hx
    have hopt : x ∈ options K H ε Tt Tstar R i := by
      unfold options; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hx_ge : tm ≤ x := by
      rw [hx]; unfold roundUpMult
      have := Nat.le_ceil (tm / R 0)
      rw [div_le_iff₀ hr] at this
      exact this
    have hx_le : x ≤ (1 + 2 * ε) * tm := by
      rw [hx]; unfold roundUpMult
      have := Nat.ceil_lt_add_one (div_nonneg htm_pos.le hr.le)
      have h4 : (⌈tm / R 0⌉₊ : ℝ) * R 0 < (tm / R 0 + 1) * R 0 :=
        mul_lt_mul_of_pos_right this hr
      have h5 : (tm / R 0 + 1) * R 0 = tm + R 0 := by field_simp
      have h6 : Tt ≤ ε * tm := by
        rw [div_le_iff₀ hε0] at htm_ge'; linarith
      have h7 : R 0 ≤ 2 * ε * tm := by nlinarith
      linarith
    refine le_trans (hmin _ hopt) ?_
    have hxs : s ≤ x := le_trans htm_ge hx_ge
    by_cases hreg : Tstar i ≤ s
    · -- Regime 2
      have htm_eq : tm = s := by
        rw [htm_def]; exact max_eq_right (by linarith)
      rw [htm_eq] at hx_le
      have hmono := jrp36_mono (K i) (H i) x ((1 + 2 * ε) * s) hKi hHi hxs hx_le
      refine le_trans hmono ?_
      have hm := jrp36_min (K i) (H i) (Tstar i) hKi hHi hTi
      rw [← hsdef] at hm
      -- C((1+2ε)s) = ½(θ + 1/θ) C(s) ≤ (1 + ε) C(s)
      have hss : s * s = K i / H i := Real.mul_self_sqrt (div_nonneg hKi.le hHi.le)
      have hKs : K i = H i * (s * s) := by rw [hss]; field_simp
      have hθ : 0 < 1 + 2 * ε := by linarith
      have hCs : eoqCost (K i) (H i) s = 2 * H i * s := by
        unfold eoqCost; rw [hKs]; field_simp; ring
      have hCθ : eoqCost (K i) (H i) ((1 + 2 * ε) * s) ≤ (1 + ε) * eoqCost (K i) (H i) s := by
        rw [hCs]
        unfold eoqCost
        rw [hKs]
        have e : H i * (s * s) / ((1 + 2 * ε) * s) = H i * s / (1 + 2 * ε) := by
          field_simp
        rw [e, div_add' _ _ _ hθ.ne', div_le_iff₀ hθ]
        have : 0 < H i * s := mul_pos hHi hs
        nlinarith
      have hCs_pos : 0 ≤ eoqCost (K i) (H i) s := by rw [hCs]; positivity
      calc eoqCost (K i) (H i) ((1 + 2 * ε) * s) ≤ (1 + ε) * eoqCost (K i) (H i) s := hCθ
        _ ≤ (1 + ε) * eoqCost (K i) (H i) (Tstar i) :=
            mul_le_mul_of_nonneg_left hm h1ε.le
        _ ≤ (1 + 2 * ε) * eoqCost (K i) (H i) (Tstar i) :=
            mul_le_mul_of_nonneg_right (by linarith) hCpos.le
    · -- Regime 3
      push Not at hreg
      have htm_le : tm ≤ Tstar i := by
        rw [htm_def]; exact max_le hbig.le hreg.le
      have hx_le' : x ≤ (1 + 2 * ε) * Tstar i :=
        le_trans hx_le (mul_le_mul_of_nonneg_left htm_le (by linarith))
      have hmono := jrp36_mono (K i) (H i) x ((1 + 2 * ε) * Tstar i) hKi hHi hxs hx_le'
      refine le_trans hmono ?_
      have hθ : 1 ≤ 1 + 2 * ε := by linarith
      have hθ0 : 0 < 1 + 2 * ε := by linarith
      unfold eoqCost
      have t1 : K i / ((1 + 2 * ε) * Tstar i) ≤ (1 + 2 * ε) * (K i / Tstar i) := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hTi]
        have h1 : 1 ≤ (1 + 2 * ε) * (1 + 2 * ε) := by nlinarith
        have h2 := mul_pos hKi hTi
        nlinarith
      have t2 : H i * ((1 + 2 * ε) * Tstar i) = (1 + 2 * ε) * (H i * Tstar i) := by ring
      rw [t2, mul_add]
      linarith
