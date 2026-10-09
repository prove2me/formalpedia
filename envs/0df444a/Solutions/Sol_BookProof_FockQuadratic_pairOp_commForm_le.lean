-- Prove2me | solution 1 for BookProof.FockQuadratic.pairOp_commForm_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:26:27.083488+00:00
-- url     : https://prove2.me/submissions/466f7eec-68ac-462d-adb9-db882628f399
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.pairOp_commForm_le
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_abs_sig_sub_sig_tgt_le
import Theorems.Thm_BookProof_FockQuadratic_norm_hopT
import Theorems.Thm_BookProof_FockQuadratic_amp_mul_le
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_hasSum_quadForm
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg
import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) (x : maxDom (sig ω)) :
    |commForm (pairOp hω g P Q hPQ) (diagMax (sig ω)) x|
      ≤ (4 * ‖g‖ * (wsum ω P + wsum ω Q + 2)) * quadForm (diagMax (sig ω)) x := by

  classical
  have hQP : deg Q + deg P ≤ 2 := by omega
  have hc0 : ∀ b : Idx ι, 0 ≤ sig ω b := fun b => sig_nonneg hω b
  set xb : Idx ι → ℂ := ((x : L2I (Idx ι)) : Idx ι → ℂ) with hxb
  set q : ℝ := quadForm (diagMax (sig ω)) x with hqdef
  have hq0 : 0 ≤ q := diagMax_quadForm_nonneg (sig ω) hc0 x
  set W : ℝ := wsum ω P + wsum ω Q + 2 with hWdef
  have hW0 : 0 ≤ W := by
    have h1 : (0 : ℝ) ≤ wsum ω P := wsum_nonneg hω _
    have h2 : (0 : ℝ) ≤ wsum ω Q := wsum_nonneg hω _
    simp only [hWdef]; linarith
  set t : Idx ι → ℂ := hopT P Q xb with htdef
  set A : ℂ := inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι)) with hAdef
  set B : ℂ := inner ℂ (hopOp hω Q P hQP x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι)) with hBdef
  -- the two matrix elements as sums over the configurations above `P`
  have hA : HasSum (fun b : {b : Idx ι // P ≤ b} => (sig ω (b : Idx ι) : ℂ) * t (b : Idx ι)) A := by
    have h := lp.hasSum_inner (𝕜 := ℂ) (hopOp hω P Q hPQ x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι))
    have hvan : ∀ b : Idx ι, b ∉ Set.range (Subtype.val : {b : Idx ι // P ≤ b} → Idx ι) →
        (inner ℂ (((hopOp hω P Q hPQ x : L2I (Idx ι)) : Idx ι → ℂ) b)
          (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ) = 0 := by
      intro b hb
      have hnp : ¬ P ≤ b := fun hle => hb ⟨⟨b, hle⟩, rfl⟩
      simp [RCLike.inner_apply, amp_eq_zero_of_not_le hnp]
    have h2 := ((Subtype.coe_injective (p := fun b : Idx ι => P ≤ b)).hasSum_iff hvan).mpr h
    refine h2.congr_fun ?_
    intro b
    simp only [Function.comp_apply, RCLike.inner_apply, hopOp_coe, diagMax_coe, htdef, hopT,
      map_mul, Complex.conj_ofReal, hxb]
    ring
  have hB : HasSum (fun b : {b : Idx ι // P ≤ b} =>
      (sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι))) B := by
    have h := lp.hasSum_inner (𝕜 := ℂ) (hopOp hω Q P hQP x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι))
    have hvan : ∀ a : Idx ι,
        a ∉ Set.range (fun b : {b : Idx ι // P ≤ b} => tgt P Q (b : Idx ι)) →
        (inner ℂ (((hopOp hω Q P hQP x : L2I (Idx ι)) : Idx ι → ℂ) a)
          (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) a) : ℂ) = 0 := by
      intro a ha
      have hnq : ¬ Q ≤ a := fun hle => ha ⟨⟨tgt Q P a, le_tgt Q P a⟩, tgt_tgt hle⟩
      simp [RCLike.inner_apply, amp_eq_zero_of_not_le hnq]
    have h2 := ((hop_injective P Q).hasSum_iff hvan).mpr h
    refine h2.congr_fun ?_
    intro b
    simp only [Function.comp_apply, RCLike.inner_apply, hopOp_coe, diagMax_coe]
    rw [amp_symm b.2, tgt_tgt b.2]
    simp only [htdef, hopT, map_mul, Complex.conj_ofReal, Complex.conj_conj, hxb]
    ring
  -- the imaginary part of the matrix element of the Hermitian combination
  have hcomb : HasSum (fun b : {b : Idx ι // P ≤ b} =>
      (starRingEnd ℂ) g * ((sig ω (b : Idx ι) : ℂ) * t (b : Idx ι))
        + g * ((sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι))))
      ((starRingEnd ℂ) g * A + g * B) := (hA.mul_left _).add (hB.mul_left _)
  set R : {b : Idx ι // P ≤ b} → ℝ := fun b =>
    (sig ω (b : Idx ι) - sig ω (tgt P Q (b : Idx ι))) * ((starRingEnd ℂ) g * t (b : Idx ι)).im
    with hRdef
  have him : HasSum R ((starRingEnd ℂ) g * A + g * B).im := by
    refine (Complex.hasSum_im hcomb).congr_fun ?_
    intro b
    set z : ℂ := (starRingEnd ℂ) g * t (b : Idx ι) with hz
    have hrw : (starRingEnd ℂ) g * ((sig ω (b : Idx ι) : ℂ) * t (b : Idx ι))
        + g * ((sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι)))
        = (sig ω (b : Idx ι) : ℂ) * z + (sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) z := by
      simp only [hz, map_mul, Complex.conj_conj]
      ring
    rw [hrw, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.conj_im, hRdef]
    ring
  -- the two halves of the comparison quadratic form
  have hquad : HasSum (fun b : Idx ι => sig ω b * ‖xb b‖ ^ 2) q :=
    diagMax_hasSum_quadForm (sig ω) x
  have hquad0 : ∀ b : Idx ι, 0 ≤ sig ω b * ‖xb b‖ ^ 2 := fun b =>
    mul_nonneg (hc0 b) (sq_nonneg _)
  have huS : Summable (fun b : {b : Idx ι // P ≤ b} =>
      sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2) :=
    hquad.summable.subtype _
  have hvS : Summable (fun b : {b : Idx ι // P ≤ b} =>
      sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) :=
    hquad.summable.comp_injective (hop_injective P Q)
  have huSle : (∑' b : {b : Idx ι // P ≤ b}, sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2) ≤ q := by
    rw [← hquad.tsum_eq]
    exact Summable.tsum_le_tsum_of_inj (Subtype.val : {b : Idx ι // P ≤ b} → Idx ι)
      Subtype.coe_injective (fun c _ => hquad0 c) (fun b => le_refl _) huS hquad.summable
  have hvSle : (∑' b : {b : Idx ι // P ≤ b},
      sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) ≤ q := by
    rw [← hquad.tsum_eq]
    exact Summable.tsum_le_tsum_of_inj (fun b : {b : Idx ι // P ≤ b} => tgt P Q (b : Idx ι))
      (hop_injective P Q) (fun c _ => hquad0 c) (fun b => le_refl _) hvS hquad.summable
  -- the pointwise bound
  have hRle : ∀ b : {b : Idx ι // P ≤ b}, |R b| ≤ (‖g‖ * W) *
      (sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2
        + sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) := by
    intro b
    have him1 : |((starRingEnd ℂ) g * t (b : Idx ι)).im| ≤ ‖g‖ * ‖t (b : Idx ι)‖ := by
      calc |((starRingEnd ℂ) g * t (b : Idx ι)).im|
          ≤ ‖(starRingEnd ℂ) g * t (b : Idx ι)‖ := Complex.abs_im_le_norm _
        _ = ‖g‖ * ‖t (b : Idx ι)‖ := by rw [norm_mul, RCLike.norm_conj]
    have hsig := abs_sig_sub_sig_tgt_le hω (P := P) (Q := Q) hPQ b.2
    have hnt : ‖t (b : Idx ι)‖
        = amp P Q (b : Idx ι) * ‖xb (tgt P Q (b : Idx ι))‖ * ‖xb (b : Idx ι)‖ := by
      rw [htdef]; exact norm_hopT P Q xb (b : Idx ι)
    have hamp := amp_mul_le hω (P := P) (Q := Q) hPQ (b : Idx ι)
      ‖xb (b : Idx ι)‖ ‖xb (tgt P Q (b : Idx ι))‖
    have hg0 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
    have hnt0 : (0 : ℝ) ≤ ‖t (b : Idx ι)‖ := norm_nonneg _
    have habs : |R b| ≤ |sig ω (b : Idx ι) - sig ω (tgt P Q (b : Idx ι))|
        * |((starRingEnd ℂ) g * t (b : Idx ι)).im| := by
      rw [hRdef, abs_mul]
    have hstep : |sig ω (b : Idx ι) - sig ω (tgt P Q (b : Idx ι))|
        * |((starRingEnd ℂ) g * t (b : Idx ι)).im| ≤ W * (‖g‖ * ‖t (b : Idx ι)‖) := by
      refine mul_le_mul hsig him1 (abs_nonneg _) hW0
    have hfin : W * (‖g‖ * ‖t (b : Idx ι)‖) ≤ (‖g‖ * W) *
        (sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2
          + sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) := by
      rw [hnt]
      have := mul_le_mul_of_nonneg_left hamp (mul_nonneg hg0 hW0)
      nlinarith [this]
    linarith [habs, hstep, hfin]
  have habsS : Summable (fun b : {b : Idx ι // P ≤ b} => |R b|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hRle ?_
    exact (huS.add hvS).mul_left _
  have hRsum : Summable R := by
    have := habsS
    exact Summable.of_norm (by simpa [Real.norm_eq_abs] using this)
  have hbound : |((starRingEnd ℂ) g * A + g * B).im| ≤ (‖g‖ * W) * (2 * q) := by
    calc |((starRingEnd ℂ) g * A + g * B).im| = |∑' b : {b : Idx ι // P ≤ b}, R b| := by
          rw [him.tsum_eq]
      _ ≤ ∑' b : {b : Idx ι // P ≤ b}, |R b| := by
          have h := norm_tsum_le_tsum_norm (f := R) (by simpa [Real.norm_eq_abs] using habsS)
          simpa [Real.norm_eq_abs] using h
      _ ≤ ∑' b : {b : Idx ι // P ≤ b}, (‖g‖ * W) *
            (sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2
              + sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) :=
          Summable.tsum_le_tsum hRle habsS ((huS.add hvS).mul_left _)
      _ = (‖g‖ * W) * ((∑' b : {b : Idx ι // P ≤ b}, sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2)
            + ∑' b : {b : Idx ι // P ≤ b},
              sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) := by
          rw [(huS.add hvS).tsum_mul_left, huS.tsum_add hvS]
      _ ≤ (‖g‖ * W) * (2 * q) := by
          have hg0 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
          have : (0 : ℝ) ≤ ‖g‖ * W := mul_nonneg hg0 hW0
          nlinarith [huSle, hvSle]
  -- assemble
  have hinner : (inner ℂ (pairOp hω g P Q hPQ x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι)) : ℂ) = (starRingEnd ℂ) g * A + g * B := by
    simp only [pairOp, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
      hAdef, hBdef, Complex.conj_conj]
  rw [commForm_eq_neg_two_im, hinner, abs_mul]
  simp only [abs_neg, abs_two]
  nlinarith [hbound, hq0, norm_nonneg g, hW0]
