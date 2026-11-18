-- Prove2me | solution 1 for DistancePreserver934.Exact.claim_22
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:07:50.045333+00:00
-- url     : https://prove2.me/submissions/4519c37a-c1f5-41ee-82b3-61ac0bf2b613

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
set_option autoImplicit false
open Classical DistancePreserver934.Exact

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (p : ℕ) (C C_CE : ℝ)
    (hp₁ : (Fintype.card V : ℝ) ^ ((7 : ℝ) / 10) < (p : ℝ))
    (hp₂ : (p : ℝ) ≤ (Fintype.card V : ℝ))
    (hCE : ∀ (G' J : SimpleGraph V) (T : Finset (Sym2 V)),
      IsDemandSet G' T → IsMinimalPreserver G' J T →
      (numEdges J : ℝ) ≤ C_CE * ((Fintype.card V : ℝ) +
        (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2) * (T.card : ℝ)))
    (hC : (2 : ℝ) ^ ((13 : ℝ) / 9) * C_CE ≤ C)
    (IH : ∀ (G' J : SimpleGraph V) (T : Finset (Sym2 V)),
      IsDemandSet G' T → (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ (T.card : ℝ) → T.card < p →
      IsMinimalPreserver G' J T →
      (numEdges J : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (T.card : ℝ) ^ ((4 : ℝ) / 9))
    (R : Finset (Sym2 V)) (J : SimpleGraph V)
    (hR : IsDemandSet G R) (hRp : (R.card : ℝ) ≤ (p : ℝ) / 2) (hJ : IsMinimalPreserver G J R) :
    (numEdges J : ℝ) ≤
      C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * ((p : ℝ) / 2) ^ ((4 : ℝ) / 9) := by
  classical

  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hp : 0 < (p : ℝ) := (Real.rpow_nonneg hn0 _).trans_lt hp₁
  have hn : 0 < n := hp.trans_le hp₂
  have hn1 : 1 ≤ n := by
    have hv : 0 < Fintype.card V := by exact_mod_cast (show 0 < (Fintype.card V : ℝ) from hn)
    change 1 ≤ (Fintype.card V : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv))
  have hCE0 : 0 ≤ C_CE := by
    have hb : IsMinimalPreserver (⊥ : SimpleGraph V) ⊥ ∅ := by
      refine ⟨⟨le_rfl, by simp⟩, ?_⟩
      simp
    have h := hCE ⊥ ⊥ ∅ (by simp [IsDemandSet]) hb
    simp [numEdges, edgesF] at h
    exact nonneg_of_mul_nonneg_left h hn
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  have hpquarter : n ^ ((1:ℝ)/4) ≤ (p : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1:ℝ)/4 ≤ 7/10)).trans hp₁.le
  by_cases hbig : n ^ ((1:ℝ)/4) ≤ (R.card : ℝ)
  · have hlt : R.card < p := by
      have : (R.card : ℝ) < p := by linarith
      exact_mod_cast this
    have h := IH G J R hR hbig hlt hJ
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hRp (by norm_num : (0:ℝ) ≤ 4/9))
      (mul_nonneg hC0 (Real.rpow_nonneg hn0 _)))
  have hsmall : (R.card : ℝ) ≤ n ^ ((1:ℝ)/4) := (lt_of_not_ge hbig).le
  have hbase : (numEdges J : ℝ) ≤ 2*C_CE*n := by
    have h := hCE G J R hR hJ
    have hmul : n ^ ((1:ℝ)/2) * (R.card : ℝ) ≤ n := by
      calc
        _ ≤ n ^ ((1:ℝ)/2) * n ^ ((1:ℝ)/4) :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hn0 _)
        _ = n ^ ((3:ℝ)/4) := by rw [← Real.rpow_add hn]; norm_num
        _ ≤ n ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = n := Real.rpow_one _
    dsimp [n] at *
    nlinarith
  have hid : (2:ℝ)^((13:ℝ)/9) * n^((8:ℝ)/9) * (n^((1:ℝ)/4)/2)^((4:ℝ)/9) = 2*n := by
    rw [Real.div_rpow (Real.rpow_nonneg hn0 _) (by norm_num), ← Real.rpow_mul hn0]
    have hpow : n ^ ((8:ℝ)/9) * n ^ (((1:ℝ)/4)*((4:ℝ)/9)) = n := by
      rw [← Real.rpow_add hn]; norm_num
    have htwo : (2:ℝ)^((13:ℝ)/9) = 2*(2:ℝ)^((4:ℝ)/9) := by
      rw [show (13:ℝ)/9 = 1 + 4/9 by norm_num, Real.rpow_add (by norm_num)]
      norm_num
    rw [htwo]
    have h2 : (2:ℝ)^((4:ℝ)/9) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    field_simp
    nlinarith [hpow]
  calc
    (numEdges J : ℝ) ≤ 2*C_CE*n := hbase
    _ = ((2:ℝ)^((13:ℝ)/9)*C_CE)*n^((8:ℝ)/9)*(n^((1:ℝ)/4)/2)^((4:ℝ)/9) := by
      nlinarith [congrArg (fun z : ℝ => C_CE*z) hid]
    _ ≤ C*n^((8:ℝ)/9)*(n^((1:ℝ)/4)/2)^((4:ℝ)/9) := by
      gcongr
    _ ≤ C*n^((8:ℝ)/9)*((p:ℝ)/2)^((4:ℝ)/9) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 (Real.rpow_nonneg hn0 _))
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      linarith
