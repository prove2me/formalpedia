-- Prove2me | solution 1 for DetANN.Thm11.outer_composition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-23T21:58:47.175953+00:00
-- url     : https://prove2.me/submissions/f76e4cdc-9739-41f9-a6ba-e20a36fc0252
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Definitions.Def_DetANN_Thm11_OuterProg
import Definitions.Def_DetANN_Thm11_Stored
import Theorems.Thm_PNormRegLib_exists_usesBelow
import Theorems.Thm_PNormRegLib_exists_litBound
import Theorems.Thm_DetANN_Thm11_outer_det
import Theorems.Thm_DetANN_Thm11_outer_small
import Theorems.Thm_DetANN_Thm11_outer_pre_spec
import Theorems.Thm_DetANN_Thm11_outer_qry_spec

namespace DetANN

namespace Thm11

namespace ARed

open PNormReg PNormRegLib

lemma usesBelow_mono {P : Program} {a b : ℕ} (h : UsesBelow P a a) (hab : a ≤ b) : UsesBelow P b b := by
  intro ins hins
  have h1 := h ins hins
  cases ins with
  | core c => cases c <;> simp only [InstrOK] at h1 ⊢ <;> omega
  | _ => simp only [InstrOK] at h1 ⊢ <;> omega

lemma litBound_mono {P : Program} {a b : ℤ} (h : LitBound P a) (hab : a ≤ b) : LitBound P b :=
  fun q c hc => (h q c hc).trans hab

/-- With one point, the answer `0` is a local answer (padding `k = 0`). -/
lemma local_one {d : ℕ} (C₀ : ℝ) (P : Fin 1 → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (hε : 0 < ε)
    (q : EuclideanSpace ℝ (Fin d)) : LocalAnswer C₀ 0 P ε q 0 := by
  refine ⟨fun _ => 0, ?_, fun _ => le_rfl⟩
  intro v y hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
  rw [Subsingleton.elim i 0]
  have h0 : 0 ≤ superNormSq (annBlocks C₀ 0 P ε) (annTuples 0 ε) v
      (padVec (2 ^ 0) q - padVec (2 ^ 0) (P 0)) := Finset.sum_nonneg (fun _ _ => by positivity)
  have h1 : 1 ≤ (1 + ε / 100) ^ 2 := by nlinarith
  nlinarith

lemma pre_mono {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {C₁ K₁ C₂ K₂ : ℕ}
    (hC : C₁ ≤ C₂) (hK : K₁ ≤ K₂) :
    (C₁ : ℝ) * (n : ℝ) ^ ((K₁ : ℝ) * ε⁻¹ ^ K₁) ≤ (C₂ : ℝ) * (n : ℝ) ^ ((K₂ : ℝ) * ε⁻¹ ^ K₂) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1.le
  have he : (K₁ : ℝ) * ε⁻¹ ^ K₁ ≤ (K₂ : ℝ) * ε⁻¹ ^ K₂ :=
    mul_le_mul (by exact_mod_cast hK) (pow_le_pow_right₀ hi hK) (by positivity) (by positivity)
  have hp : (n : ℝ) ^ ((K₁ : ℝ) * ε⁻¹ ^ K₁) ≤ (n : ℝ) ^ ((K₂ : ℝ) * ε⁻¹ ^ K₂) :=
    Real.rpow_le_rpow_of_exponent_le hn1 he
  exact mul_le_mul (by exact_mod_cast hC) hp (by positivity) (by positivity)

lemma qry_mono {d n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {C₁ K₁ C₂ K₂ : ℕ}
    (hC : C₁ ≤ C₂) (hK : K₁ ≤ K₂) :
    (C₁ : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ K₁ * (1 + Real.log n) ^ K₁) ≤
      (C₂ : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ K₂ * (1 + Real.log n) ^ K₂) := by
  have hi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1.le
  have hl : 1 ≤ 1 + Real.log n := by
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    linarith
  have h1 : ε⁻¹ ^ K₁ * (1 + Real.log n) ^ K₁ ≤ ε⁻¹ ^ K₂ * (1 + Real.log n) ^ K₂ :=
    mul_le_mul (pow_le_pow_right₀ hi hK) (pow_le_pow_right₀ hl hK) (by positivity) (by positivity)
  have h2 : (d : ℝ) ^ 2 + d * ε⁻¹ ^ K₁ * (1 + Real.log n) ^ K₁ ≤
      (d : ℝ) ^ 2 + d * ε⁻¹ ^ K₂ * (1 + Real.log n) ^ K₂ := by
    have : (d : ℝ) * (ε⁻¹ ^ K₁ * (1 + Real.log n) ^ K₁) ≤ d * (ε⁻¹ ^ K₂ * (1 + Real.log n) ^ K₂) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have h3 : 0 ≤ (d : ℝ) ^ 2 + d * ε⁻¹ ^ K₁ * (1 + Real.log n) ^ K₁ := by
    have : 0 ≤ (1 + Real.log n) := by linarith
    positivity
  exact mul_le_mul (by exact_mod_cast hC) h2 h3 (by positivity)

end ARed

end Thm11

open PNormReg PNormRegLib Thm11 Thm11.ARed in
theorem _root_.solution :
    ∀ (Pre₃ Qry₃ : PNormReg.Program), DetProgram Pre₃ → DetProgram Qry₃ →
      ∀ (C : ℝ) (K C' : ℕ), 1 < C →
        (∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
            ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
              IsDetANNStructure Pre₃ Qry₃ Y δ (1 + δ)
                ((C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
                ((C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
                ((C' : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2)) →
        ∀ C₀s : ℝ, 0 < C₀s →
          ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
            ∃ Cm Km : ℕ, ∀ d n : ℕ, 1 ≤ d → d ≤ n →
              ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
                ∀ ε : ℝ, 0 < ε → ε < 1 →
                  ∃ (k : ℕ) (C₀ : ℝ), d ≤ 2 ^ k ∧ C₀s ≤ C₀ ∧
                    IsDetStructure Pre Qry P ε (LocalAnswer C₀ k P ε)
                      ((Cm : ℝ) * (n : ℝ) ^ ((Km : ℝ) * ε⁻¹ ^ Km))
                      ((Cm : ℝ) * (n : ℝ) ^ ((Km : ℝ) * ε⁻¹ ^ Km))
                      ((Cm : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ Km * (1 + Real.log n) ^ Km)) := by
  intro Pre₃ Qry₃ hD1 hD2 C K C' hC hIn C₀s hC₀s
  obtain ⟨u1, hu1⟩ := exists_usesBelow Pre₃
  obtain ⟨u2, hu2⟩ := exists_usesBelow Qry₃
  obtain ⟨l1, hl1, hL1⟩ := exists_litBound Pre₃
  obtain ⟨l2, hl2, hL2⟩ := exists_litBound Qry₃
  set n3 := max u1 u2 with hn3
  set X3 : ℕ := (max l1 l2).toNat with hX3
  have eX : ((X3 : ℕ) : ℤ) = max l1 l2 := Int.toNat_of_nonneg (by omega)
  have hX1 : 1 ≤ X3 := by omega
  have hLP : LitBound Pre₃ (X3 : ℤ) := litBound_mono hL1 (by omega)
  have hLQ : LitBound Qry₃ (X3 : ℤ) := litBound_mono hL2 (by omega)
  have hUP : UsesBelow Pre₃ n3 n3 := usesBelow_mono hu1 (by omega)
  have hUQ : UsesBelow Qry₃ n3 n3 := usesBelow_mono hu2 (by omega)
  have hCb : C ≤ (⌈C⌉₊ : ℕ) := Nat.le_ceil C
  obtain ⟨c1, hP⟩ := outer_pre_spec Pre₃ Qry₃ hD1 hD2 n3 X3 hUP hLP hX1 C K C' ⌈C⌉₊ hC hCb hIn
  obtain ⟨c2, hQ⟩ := outer_qry_spec Pre₃ Qry₃ hD1 hD2 n3 X3 hUQ hLQ hX1 C K C' ⌈C⌉₊ hC hCb hIn
  set c0 := max (max c1 c2) ⌈C₀s⌉₊ with hc0
  obtain ⟨Cm, Km, hPm⟩ := hP c0 (by omega)
  obtain ⟨Cq, Kq, hQm⟩ := hQ c0 (by omega)
  obtain ⟨hDP, hDQ⟩ := outer_det Pre₃ Qry₃ n3 c0 ⌈C⌉₊ K C' X3 hD1 hD2
  have hs0 : C₀s ≤ (c0 : ℝ) :=
    (Nat.le_ceil C₀s).trans (by exact_mod_cast (le_max_right _ _ : ⌈C₀s⌉₊ ≤ c0))
  refine ⟨_, _, hDP, hDQ, max (max Cm Cq) 8, max Km Kq, ?_⟩
  intro d n hd hdn P hP ε hε hε1
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl : n = 1 := by omega
    obtain ⟨t, ht, h1, h2, h3, hq⟩ := outer_small Pre₃ Qry₃ n3 c0 ⌈C⌉₊ K C' X3 d P ε
    have h8 : (8 : ℝ) ≤ ((max (max Cm Cq) 8 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    refine ⟨0, C₀s, by simpa using hdn, le_rfl, ?_⟩
    unfold IsDetStructure
    refine ⟨t, h1, ?_, ?_, fun q => ?_⟩
    · rw [h2]; simp only [Nat.cast_one, Real.one_rpow, mul_one]
      exact le_trans (by exact_mod_cast ht) h8
    · rw [h3]; simp only [Finset.card_empty, Nat.cast_zero, Nat.cast_one, Real.one_rpow, mul_one]
      positivity
    · obtain ⟨t', ht', g1, g2, g3⟩ := hq q
      refine ⟨t', g1, ?_, 0, by rw [g3]; simp, local_one C₀s P ε hε q⟩
      rw [g2]
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have : (0 : ℝ) ≤ d * ε⁻¹ ^ max Km Kq * (1 + Real.log ((1 : ℕ) : ℝ)) ^ max Km Kq := by
        simp only [Nat.cast_one, Real.log_one, add_zero, one_pow, mul_one]; positivity
      have hdd : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd1
      have ht5 : (t' : ℝ) ≤ 8 := by exact_mod_cast (show t' ≤ 8 by omega)
      nlinarith
  · obtain ⟨t, k, C₀, hC₀, h1, h2, h3, hS⟩ := hPm d n hd hdn hn P hP ε hε hε1
    refine ⟨k, C₀, hS.1, hs0.trans hC₀, ?_⟩
    unfold IsDetStructure
    have hn1 : 1 ≤ n := by omega
    refine ⟨t, h1, h2.trans (pre_mono hn1 hε hε1 (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)), h3.trans (pre_mono hn1 hε hε1 (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)), fun q => ?_⟩
    obtain ⟨t', g1, g2, a, g3, g4⟩ := hQm d n hd hdn hn P hP ε hε hε1 k C₀ _ hC₀ hS q
    exact ⟨t', g1, g2.trans (qry_mono hn1 hε hε1 (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_right _ _)), a, g3, g4⟩

end DetANN
