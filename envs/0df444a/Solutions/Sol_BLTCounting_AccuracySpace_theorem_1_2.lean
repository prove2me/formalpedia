-- Prove2me | solution 1 for BLTCounting.AccuracySpace.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:46:42.707801+00:00
-- url     : https://prove2.me/submissions/bc17b0fc-ed9c-46f7-ae0b-1a2032dce2ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Sequences
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks
import Theorems.Thm_BLTCounting_AccuracySpace_corollary_4_3
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_4_6
import Theorems.Thm_BLTCounting_AccuracySpace_proposition_4_7
import Theorems.Thm_BLTCounting_AccuracySpace_claim_3_8
import Theorems.Thm_BLTCounting_AccuracySpace_corollary_3_9
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_7
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_2_7
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_13
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_16
import Theorems.Thm_BLTCounting_AccuracySpace_theorem_2_1

open Matrix Complex MeasureTheory BLTCounting.AccuracySpace
open scoped ComplexOrder

namespace AuxThm12

lemma c0_even (x : ℝ) : c0 (-x) = c0 x := by
  unfold c0
  have h : (-x) / 2 = -(x / 2) := by ring
  rw [h, Real.cosh_neg]

lemma c0_nonneg (x : ℝ) : 0 ≤ c0 x := by
  unfold c0
  positivity

lemma blockPoint_eq {R : ℕ} (hR : 1 ≤ R) (h : ℝ) (i : ℕ) :
    blockPoint R h i = (R : ℝ) * Real.exp ((i : ℝ) * h) := by
  unfold blockPoint
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Real.exp_add, Real.exp_log hR_pos]

lemma blockPoint_pos {R : ℕ} (hR : 1 ≤ R) (h : ℝ) (i : ℕ) :
    0 < blockPoint R h i := by
  rw [blockPoint_eq hR]
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
  positivity

lemma blockPoint_mono {R : ℕ} (_hR : 1 ≤ R) {h : ℝ} (hh : 0 < h) {i j : ℕ} (hij : i ≤ j) :
    blockPoint R h i ≤ blockPoint R h j := by
  unfold blockPoint
  refine Real.exp_le_exp.mpr ?_
  have hij' : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  linarith [mul_le_mul_of_nonneg_right hij' hh.le]

lemma block_nonempty {R : ℕ} (hR : 1 ≤ R) {h : ℝ} (hh : 0 < h)
    (hRh : 1 < (R : ℝ) * h) (i : ℕ) :
    (block R h i).Nonempty := by
  unfold block
  rw [Finset.nonempty_Ico]
  have hexp_h : 1 + h < Real.exp h := by linarith [Real.add_one_lt_exp (ne_of_gt hh)]
  have hexp_i : 1 ≤ Real.exp ((i : ℝ) * h) := Real.one_le_exp (by positivity)
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
  have hgap : 1 < blockPoint R h (i + 1) - blockPoint R h i := by
    rw [blockPoint_eq hR, blockPoint_eq hR]
    have h1 : ((i + 1 : ℕ) : ℝ) * h = (i : ℝ) * h + h := by push_cast; ring
    rw [h1, Real.exp_add]
    have hdiff : (R : ℝ) * (Real.exp ((i : ℝ) * h) * Real.exp h) -
        (R : ℝ) * Real.exp ((i : ℝ) * h) =
        (R : ℝ) * Real.exp ((i : ℝ) * h) * (Real.exp h - 1) := by ring
    rw [hdiff]
    have hgt1 : (R : ℝ) * h < (R : ℝ) * Real.exp ((i : ℝ) * h) * (Real.exp h - 1) := by
      have h_eh : h < Real.exp h - 1 := by linarith
      have h_ri : (R : ℝ) ≤ (R : ℝ) * Real.exp ((i : ℝ) * h) :=
        le_mul_of_one_le_right hR_pos.le hexp_i
      calc
        (R : ℝ) * h ≤ ((R : ℝ) * Real.exp ((i : ℝ) * h)) * h :=
          mul_le_mul_of_nonneg_right h_ri hh.le
        _ < ((R : ℝ) * Real.exp ((i : ℝ) * h)) * (Real.exp h - 1) :=
          mul_lt_mul_of_pos_left h_eh (by positivity)
    linarith
  have hc1 : (⌈blockPoint R h i⌉₊ : ℝ) < blockPoint R h i + 1 :=
    Nat.ceil_lt_add_one (blockPoint_pos hR h i).le
  have hc2 : blockPoint R h (i + 1) ≤ (⌈blockPoint R h (i + 1)⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast (by linarith : (⌈blockPoint R h i⌉₊ : ℝ) < (⌈blockPoint R h (i + 1)⌉₊ : ℝ))

lemma block_mem_ge_R {R : ℕ} (hR : 1 ≤ R) {h : ℝ} (hh : 0 < h) {i r : ℕ}
    (hr : r ∈ block R h i) : R ≤ r := by
  have h1 : ⌈blockPoint R h i⌉₊ ≤ r := (Finset.mem_Ico.mp hr).1
  have h2 : (R : ℝ) ≤ blockPoint R h i := by
    have h0 := blockPoint_mono hR hh (Nat.zero_le i)
    rw [blockPoint_eq hR h 0, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one] at h0
    exact h0
  have h3 : R ≤ ⌈blockPoint R h i⌉₊ := by
    exact_mod_cast le_trans h2 (Nat.le_ceil _)
  exact le_trans h3 h1

lemma blockMass_pos {R : ℕ} (hR : 1 ≤ R) {h : ℝ} (hh : 0 < h)
    (hRh : 1 < (R : ℝ) * h) (i : ℕ) :
    0 < blockMass R h i := by
  unfold blockMass
  refine Finset.sum_pos (fun r hr => ?_) (block_nonempty hR hh hRh i)
  have hRr : 1 ≤ r := le_trans hR (block_mem_ge_R hR hh hr)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  positivity

lemma block_disjoint {R : ℕ} (hR : 1 ≤ R) {h : ℝ} (hh : 0 < h) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (block R h i) (block R h j) := by
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · unfold block
    rw [Finset.disjoint_left]
    intro r hri hrj
    rw [Finset.mem_Ico] at hri hrj
    have hbp : blockPoint R h (i + 1) ≤ blockPoint R h j := blockPoint_mono hR hh hlt
    have hceil : ⌈blockPoint R h (i + 1)⌉₊ ≤ ⌈blockPoint R h j⌉₊ := Nat.ceil_mono hbp
    omega
  · exact absurd rfl hij
  · unfold block
    rw [Finset.disjoint_left]
    intro r hri hrj
    rw [Finset.mem_Ico] at hri hrj
    have hbp : blockPoint R h (j + 1) ≤ blockPoint R h i := blockPoint_mono hR hh hgt
    have hceil : ⌈blockPoint R h (j + 1)⌉₊ ≤ ⌈blockPoint R h i⌉₊ := Nat.ceil_mono hbp
    omega

lemma blockIsometry_isometry {R : ℕ} (hR : 1 ≤ R) {h : ℝ} (hh : 0 < h)
    (hRh : 1 < (R : ℝ) * h) (K : ℕ) :
    (blockIsometry R h K)ᴴ * blockIsometry R h K = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, blockIsometry, Matrix.of_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    have hsub_block : block R h (i : ℕ) ⊆ blockUnion R h K :=
      Finset.subset_biUnion_of_mem (block R h) (Finset.mem_range.mpr i.isLt)
    have hterm : ∀ r : blockUnion R h K,
        star (if (r : ℕ) ∈ block R h (i : ℕ) then
            (((Real.sqrt (((r : ℕ) : ℝ) * blockMass R h (i : ℕ)))⁻¹ : ℝ) : ℂ) else 0) *
          (if (r : ℕ) ∈ block R h (i : ℕ) then
            (((Real.sqrt (((r : ℕ) : ℝ) * blockMass R h (i : ℕ)))⁻¹ : ℝ) : ℂ) else 0) =
        if (r : ℕ) ∈ block R h (i : ℕ) then
          (((((r : ℕ) : ℝ)⁻¹ * (blockMass R h (i : ℕ))⁻¹ : ℝ)) : ℂ) else 0 := by
      intro r
      by_cases hr : (r : ℕ) ∈ block R h (i : ℕ)
      · simp only [hr, ↓reduceIte, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul]
        congr 1
        have h1r : 1 ≤ (r : ℕ) := le_trans hR (block_mem_ge_R hR hh hr)
        have hr_pos : (0 : ℝ) < ((r : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hw_pos : 0 < blockMass R h (i : ℕ) := blockMass_pos hR hh hRh (i : ℕ)
        rw [← mul_inv, Real.mul_self_sqrt (mul_nonneg hr_pos.le hw_pos.le), mul_inv]
      · simp [hr]
    simp_rw [hterm]
    have hsum_attach : (∑ r : blockUnion R h K,
        if (r : ℕ) ∈ block R h (i : ℕ) then
          (((((r : ℕ) : ℝ)⁻¹ * (blockMass R h (i : ℕ))⁻¹ : ℝ)) : ℂ) else 0) =
        ∑ r ∈ blockUnion R h K,
          if r ∈ block R h (i : ℕ) then
            ((((r : ℝ)⁻¹ * (blockMass R h (i : ℕ))⁻¹ : ℝ)) : ℂ) else 0 := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (blockUnion R h K) (fun r =>
        if r ∈ block R h (i : ℕ) then
          ((((r : ℝ)⁻¹ * (blockMass R h (i : ℕ))⁻¹ : ℝ)) : ℂ) else 0)
    rw [hsum_attach, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hsub_block]
    have hreal : (∑ r ∈ block R h (i : ℕ),
        ((((r : ℝ)⁻¹ * (blockMass R h (i : ℕ))⁻¹ : ℝ)) : ℂ)) =
        (((∑ r ∈ block R h (i : ℕ), (r : ℝ)⁻¹) * (blockMass R h (i : ℕ))⁻¹ : ℝ) : ℂ) := by
      rw [Finset.sum_mul]
      push_cast
      rfl
    rw [hreal]
    have hw_pos : 0 < blockMass R h (i : ℕ) := blockMass_pos hR hh hRh (i : ℕ)
    change ((blockMass R h (i : ℕ) * (blockMass R h (i : ℕ))⁻¹ : ℝ) : ℂ) = 1
    rw [mul_inv_cancel₀ (ne_of_gt hw_pos), Complex.ofReal_one]
  · simp only [hij, ↓reduceIte]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hri : (r : ℕ) ∈ block R h (i : ℕ)
    · have hdisj := block_disjoint hR hh (Fin.val_ne_of_ne hij)
      have hrj : (r : ℕ) ∉ block R h (j : ℕ) := Finset.disjoint_left.mp hdisj hri
      simp [hri, hrj]
    · simp [hri]

lemma blockUnion_subset_Ico {R m K : ℕ} (hR : 1 ≤ R) {h : ℝ} (hh : 0 < h)
    (hbp : blockPoint R h K ≤ (m : ℝ)) :
    blockUnion R h K ⊆ Finset.Ico 1 m := by
  intro r hr
  unfold blockUnion at hr
  rcases Finset.mem_biUnion.mp hr with ⟨i, hi, hri⟩
  rw [Finset.mem_range] at hi
  have h1r : 1 ≤ r := le_trans hR (block_mem_ge_R hR hh hri)
  have hlt : r < ⌈blockPoint R h (i + 1)⌉₊ := (Finset.mem_Ico.mp hri).2
  have hle_m : ⌈blockPoint R h (i + 1)⌉₊ ≤ m :=
    Nat.ceil_le.mpr (le_trans (blockPoint_mono hR hh (by omega : i + 1 ≤ K)) hbp)
  exact Finset.mem_Ico.mpr ⟨h1r, lt_of_lt_of_le hlt hle_m⟩

lemma bandMatrix_quadForm_re (K : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (u : Fin K → ℂ) :
    (star u ⬝ᵥ (bandMatrix K θ *ᵥ u)).re =
      (1 / (2 * Real.pi)) * ∫ x in (-θ)..θ, ‖trigPoly u x‖ ^ 2 := by
  have hneg_norm : ∀ x : ℝ, ((‖trigPoly u (-x)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : Fin K, ∑ j : Fin K,
        star (u i) * u j * cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)) := by
    intro x
    have hconj_mul : ((‖trigPoly u (-x)‖ ^ 2 : ℝ) : ℂ) =
        star (trigPoly u (-x)) * trigPoly u (-x) := by
      simpa using (Complex.conj_mul' (trigPoly u (-x))).symm
    rw [hconj_mul]
    unfold trigPoly
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstar_exp : star (cexp (I * ((i : ℕ) : ℂ) * ((-x : ℝ) : ℂ))) =
        cexp (I * ((i : ℕ) : ℂ) * (x : ℂ)) := by
      change (starRingEnd ℂ) (cexp (I * ((i : ℕ) : ℂ) * ((-x : ℝ) : ℂ))) = _
      rw [← Complex.exp_conj]
      congr 1
      simp
    rw [star_mul', hstar_exp]
    calc
      star (u i) * cexp (I * ((i : ℕ) : ℂ) * (x : ℂ)) *
          (u j * cexp (I * ((j : ℕ) : ℂ) * ((-x : ℝ) : ℂ)))
          = star (u i) * u j *
            (cexp (I * ((i : ℕ) : ℂ) * (x : ℂ)) *
              cexp (I * ((j : ℕ) : ℂ) * ((-x : ℝ) : ℂ))) := by ring
      _ = star (u i) * u j * cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring
  have hint_ij : ∀ i j : Fin K, IntervalIntegrable
      (fun x : ℝ => star (u i) * u j * cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)))
      volume (-θ) θ := fun _ _ =>
    (continuous_const.mul (Continuous.cexp (by continuity))).intervalIntegrable _ _
  have hcomplex : star u ⬝ᵥ (bandMatrix K θ *ᵥ u) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ x in (-θ)..θ, ((‖trigPoly u (-x)‖ ^ 2 : ℝ) : ℂ) := by
    have hrhs : (∫ x in (-θ)..θ, ((‖trigPoly u (-x)‖ ^ 2 : ℝ) : ℂ)) =
        ∑ i : Fin K, ∑ j : Fin K, star (u i) * u j *
          ∫ x in (-θ)..θ, cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)) := by
      have hfun : (fun x : ℝ => ((‖trigPoly u (-x)‖ ^ 2 : ℝ) : ℂ)) =
          fun x : ℝ => ∑ i : Fin K, ∑ j : Fin K,
            star (u i) * u j * cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)) :=
        funext hneg_norm
      have houter := intervalIntegral.integral_finsetSum (a := -θ) (b := θ) (μ := volume)
        (s := Finset.univ)
        (f := fun (i : Fin K) (x : ℝ) => ∑ j : Fin K,
          star (u i) * u j * cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)))
        (fun i _ => (continuous_finsetSum Finset.univ fun j _ =>
          continuous_const.mul (Continuous.cexp (by continuity))).intervalIntegrable _ _)
      rw [hfun, houter]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hinner := intervalIntegral.integral_finsetSum (a := -θ) (b := θ) (μ := volume)
        (s := Finset.univ)
        (f := fun (j : Fin K) (x : ℝ) =>
          star (u i) * u j * cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (x : ℂ)))
        (fun j _ => hint_ij i j)
      rw [hinner]
      refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
    rw [hrhs, Finset.mul_sum]
    simp only [dotProduct, Matrix.mulVec, bandMatrix, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hre := congrArg Complex.re hcomplex
  have hint_ofReal : (∫ x in (-θ)..θ, ((‖trigPoly u (-x)‖ ^ 2 : ℝ) : ℂ)) =
      (((∫ x in (-θ)..θ, ‖trigPoly u (-x)‖ ^ 2) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [hint_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re] at hre
  have hcomp_neg : (∫ x in (-θ)..θ, ‖trigPoly u (-x)‖ ^ 2) =
      ∫ x in (-θ)..θ, ‖trigPoly u x‖ ^ 2 := by
    simpa using intervalIntegral.integral_comp_neg (fun x : ℝ => ‖trigPoly u x‖ ^ 2)
      (a := -θ) (b := θ)
  have _ := hθ0
  rw [hcomp_neg] at hre
  exact hre

lemma rescaledToeplitz_dom_bandMatrix (K : ℕ) {h η ω : ℝ} (hh : 0 < h) (hη : 0 < η)
    (hω : 0 < ω) (hω_eq : c0Hat ω = ((8 * η : ℝ) : ℂ)) (hθπ : h * ω ≤ Real.pi)
    (u : Fin K → ℂ) :
    8 * η * (star u ⬝ᵥ (bandMatrix K (h * ω) *ᵥ u)).re ≤
      (star u ⬝ᵥ (rescaledToeplitz K h *ᵥ u)).re := by
  let a_seq : ℤ → ℂ := fun t => ((h * c0 (h * (t : ℝ)) : ℝ) : ℂ)
  have h_mat : rescaledToeplitz K h = toeplitz K a_seq := by
    ext i j
    simp only [rescaledToeplitz, toeplitz, Matrix.of_apply, a_seq]
    congr 3
    push_cast
    ring
  have h38_0 := (claim_3_8 h 0 hh ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩).1
  have ha_summ : Summable (fun t : ℤ => ‖a_seq t‖) := by
    have hnorm_c : Summable (fun t : ℤ => ‖((c0 (h * (t : ℝ)) : ℝ) : ℂ) *
        cexp (-(I * (t : ℂ) * ((0 : ℝ) : ℂ)))‖) := h38_0.norm
    have hrew : (fun t : ℤ => ‖a_seq t‖) =
        fun t : ℤ => h * ‖((c0 (h * (t : ℝ)) : ℝ) : ℂ) *
          cexp (-(I * (t : ℂ) * ((0 : ℝ) : ℂ)))‖ := by
      ext t
      simp [a_seq, abs_of_pos hh, abs_of_nonneg (c0_nonneg _)]
    rw [hrew]
    exact hnorm_c.mul_left h
  have ha_conj : ∀ t : ℤ, a_seq (-t) = star (a_seq t) := by
    intro t
    change ((h * c0 (h * ((-t : ℤ) : ℝ)) : ℝ) : ℂ) =
      (starRingEnd ℂ) ((h * c0 (h * (t : ℝ)) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, Int.cast_neg]
    have hneg : h * -(t : ℝ) = -(h * (t : ℝ)) := by ring
    rw [hneg, c0_even]
  have h27 := lemma_2_7 a_seq ha_summ ha_conj K u
  rw [h_mat]
  have hsym_eq : ∀ x : ℝ, bilateralSymbol a_seq x = ((h : ℝ) : ℂ) * sampledSymbol h (-x) := by
    intro x
    unfold bilateralSymbol sampledSymbol
    rw [← tsum_mul_left]
    congr 1
    ext t
    dsimp [a_seq]
    push_cast
    have hexp : cexp (I * (t : ℂ) * (x : ℂ)) = cexp (-(I * (t : ℂ) * -(x : ℂ))) := by
      congr 1
      ring
    rw [hexp]
    ring
  have h37 := lemma_3_7
  have hsym_im : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, (bilateralSymbol a_seq x).im = 0 := by
    intro x hx
    have hnx : -x ∈ Set.Icc (-Real.pi) Real.pi := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h39 := (corollary_3_9 h (-x) hh hnx).1
    rw [hsym_eq x]
    simp [Complex.mul_im, h39]
  have hsym_re_lb : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      (c0Hat (x / h)).re ≤ (bilateralSymbol a_seq x).re := by
    intro x hx
    have hnx : -x ∈ Set.Icc (-Real.pi) Real.pi := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h39 := corollary_3_9 h (-x) hh hnx
    rw [hsym_eq x]
    have hre : (((h : ℝ) : ℂ) * sampledSymbol h (-x)).re = h * (sampledSymbol h (-x)).re := by
      simp [Complex.mul_re, h39.1]
    rw [hre]
    have hmul := mul_le_mul_of_nonneg_left h39.2 hh.le
    have h1 : h * (1 / h * (c0Hat (-x / h)).re) = (c0Hat (-x / h)).re := by
      field_simp [ne_of_gt hh]
    rw [h1] at hmul
    have hev : c0Hat (-x / h) = c0Hat (x / h) := by
      have hneg : -x / h = -(x / h) := by ring
      rw [hneg, (h37.1 (x / h)).2.2]
    rw [hev] at hmul
    exact hmul
  have hsym_nn : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, 0 ≤ (bilateralSymbol a_seq x).re := fun x hx =>
    le_trans (h37.1 (x / h)).2.1 (hsym_re_lb x hx)
  have hcont_sym : Continuous (bilateralSymbol a_seq) := by
    unfold bilateralSymbol
    refine continuous_tsum (fun t => continuous_const.mul (Continuous.cexp (by continuity)))
      ha_summ (fun t x => ?_)
    have hr : I * (t : ℂ) * (x : ℂ) = (((t : ℝ) * x : ℝ) : ℂ) * I := by push_cast; ring
    rw [norm_mul, hr, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcont_trig : Continuous (fun x : ℝ => ‖trigPoly u x‖ ^ 2) := by
    unfold trigPoly
    exact ((continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul (Continuous.cexp (by continuity))).norm).pow 2
  have hcont_prod : Continuous (fun x : ℝ => (bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2) :=
    (Complex.continuous_re.comp hcont_sym).mul hcont_trig
  have hre_27 : (star u ⬝ᵥ (toeplitz K a_seq *ᵥ u)).re =
      (1 / (2 * Real.pi)) *
        ∫ x in (-Real.pi)..Real.pi, (bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2 := by
    have hre := congrArg Complex.re h27
    have hfun_eq : ∀ x ∈ Set.uIcc (-Real.pi) Real.pi,
        (bilateralSymbol a_seq x * ((‖trigPoly u x‖ ^ 2 : ℝ) : ℂ)) =
        ((((bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2 : ℝ)) : ℂ) := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hsym_im x hx,
          mul_zero, zero_mul, add_zero]
    rw [intervalIntegral.integral_congr hfun_eq, intervalIntegral.integral_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re] at hre
    exact hre
  let θ := h * ω
  have hθ0 : 0 < θ := mul_pos hh hω
  have hband := bandMatrix_quadForm_re K hθ0 u
  rw [hre_27, hband]
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (a := -Real.pi) (b := -θ) (c := Real.pi)
    (hcont_prod.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (hcont_prod.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (a := -θ) (b := θ) (c := Real.pi)
    (hcont_prod.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (hcont_prod.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hleft_nn : 0 ≤ ∫ x in (-Real.pi)..(-θ),
      (bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2 := by
    refine intervalIntegral.integral_nonneg (by linarith only [hθπ]) fun x hx => ?_
    exact mul_nonneg (hsym_nn x ⟨hx.1, by linarith only [hx.2, hθ0, Real.pi_pos]⟩) (sq_nonneg _)
  have hright_nn : 0 ≤ ∫ x in θ..Real.pi,
      (bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2 := by
    refine intervalIntegral.integral_nonneg hθπ fun x hx => ?_
    exact mul_nonneg (hsym_nn x ⟨by linarith only [hx.1, hθ0, Real.pi_pos], hx.2⟩) (sq_nonneg _)
  have hmid_lb : (8 * η) * (∫ x in (-θ)..θ, ‖trigPoly u x‖ ^ 2) ≤
      ∫ x in (-θ)..θ, (bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith only [hθ0])
      ((continuous_const.mul hcont_trig).intervalIntegrable _ _)
      (hcont_prod.intervalIntegrable _ _) fun x hx => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hx_pi : x ∈ Set.Icc (-Real.pi) Real.pi :=
      ⟨by linarith only [hx.1, hθπ], by linarith only [hx.2, hθπ]⟩
    have hlb1 := hsym_re_lb x hx_pi
    have habs_le : |x / h| ≤ ω := by
      rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
      have habs_x : |x| ≤ h * ω := abs_le.mpr hx
      linarith only [habs_x]
    have hev_abs : (c0Hat (x / h)).re = (c0Hat |x / h|).re := by
      rcases le_or_gt 0 (x / h) with hnn | hneg
      · rw [abs_of_nonneg hnn]
      · rw [abs_of_neg hneg, (h37.1 (x / h)).2.2]
    have hanti : (c0Hat ω).re ≤ (c0Hat |x / h|).re :=
      h37.2.antitoneOn (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr hω.le) habs_le
    have hω_re : (c0Hat ω).re = 8 * η := by
      rw [hω_eq]
      exact Complex.ofReal_re _
    linarith only [hlb1, hev_abs, hanti, hω_re]
  have htotal : (8 * η) * (∫ x in (-θ)..θ, ‖trigPoly u x‖ ^ 2) ≤
      ∫ x in (-Real.pi)..Real.pi, (bilateralSymbol a_seq x).re * ‖trigPoly u x‖ ^ 2 := by
    linarith only [hsplit1, hsplit2, hleft_nn, hright_nn, hmid_lb]
  have h1 : 8 * η * (1 / (2 * Real.pi) * ∫ x in (-θ)..θ, ‖trigPoly u x‖ ^ 2) =
      (1 / (2 * Real.pi)) * ((8 * η) * ∫ x in (-θ)..θ, ‖trigPoly u x‖ ^ 2) := by ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left htotal (by positivity)

lemma pert_bound {K : ℕ} (E : Matrix (Fin K) (Fin K) ℂ) (u : Fin K → ℂ) :
    |(star u ⬝ᵥ (E *ᵥ u)).re| ≤ specNorm E * euclSq u := by
  let x : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 u
  let y : EuclideanSpace ℂ (Fin K) := (Matrix.toEuclideanLin E).toContinuousLinearMap x
  have hx_sq : ‖x‖ ^ 2 = euclSq u := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  have hy_sq : ‖y‖ ^ 2 = ∑ i : Fin K, ‖(E *ᵥ u) i‖ ^ 2 := by
    change ‖Matrix.toEuclideanLin E x‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2, Matrix.toLpLin_apply]
  have hy_le : ‖y‖ ≤ specNorm E * ‖x‖ :=
    ContinuousLinearMap.le_opNorm ((Matrix.toEuclideanLin E).toContinuousLinearMap) x
  have hcs : ‖star u ⬝ᵥ (E *ᵥ u)‖ ≤ ‖x‖ * ‖y‖ := by
    have h1 : ‖star u ⬝ᵥ (E *ᵥ u)‖ ≤ ∑ i : Fin K, ‖u i‖ * ‖(E *ᵥ u) i‖ := by
      simpa [dotProduct, norm_mul] using
        norm_sum_le Finset.univ (fun i : Fin K => star (u i) * (E *ᵥ u) i)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin K => ‖u i‖) (fun i : Fin K => ‖(E *ᵥ u) i‖)
    have hsq : ‖star u ⬝ᵥ (E *ᵥ u)‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
      calc
        ‖star u ⬝ᵥ (E *ᵥ u)‖ ^ 2 ≤ (∑ i : Fin K, ‖u i‖ * ‖(E *ᵥ u) i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (∑ i : Fin K, ‖u i‖ ^ 2) * (∑ i : Fin K, ‖(E *ᵥ u) i‖ ^ 2) := h2
        _ = (‖x‖ * ‖y‖) ^ 2 := by
          rw [mul_pow, hx_sq, hy_sq]
          rfl
    exact le_of_sq_le_sq hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    |(star u ⬝ᵥ (E *ᵥ u)).re| ≤ ‖star u ⬝ᵥ (E *ᵥ u)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖y‖ := hcs
    _ ≤ ‖x‖ * (specNorm E * ‖x‖) := mul_le_mul_of_nonneg_left hy_le (norm_nonneg _)
    _ = specNorm E * ‖x‖ ^ 2 := by ring
    _ = specNorm E * euclSq u := by rw [hx_sq]

lemma eucl_inner_eq_dotProduct {K : ℕ} (x y : EuclideanSpace ℂ (Fin K)) :
    inner ℂ x y = star x.ofLp ⬝ᵥ y.ofLp := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, dotProduct, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma repr_symm_eq_sum {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E) (w : EuclideanSpace ℂ ι) :
    b.repr.symm w = ∑ i : ι, w.ofLp i • b i := by
  have h := (b.sum_repr (b.repr.symm w)).symm
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

lemma band_subspace_exists {K : ℕ} {B : Matrix (Fin K) (Fin K) ℂ} (hB : B.IsHermitian) :
    ∃ U : Submodule ℂ (Fin K → ℂ),
      Module.finrank ℂ U = eigCountAtLeast hB (1 / 2) ∧
      ∀ u ∈ U, (1 / 2 : ℝ) * euclSq u ≤ (star u ⬝ᵥ (B *ᵥ u)).re := by
  let b := hB.eigenvectorBasis
  let S_B := Finset.univ.filter (fun idx : Fin K => (1 / 2 : ℝ) ≤ hB.eigenvalues idx)
  let extFn : (S_B → ℂ) → (Fin K → ℂ) :=
    fun c i => if hi : i ∈ S_B then c ⟨i, hi⟩ else 0
  let Φ : (S_B → ℂ) →ₗ[ℂ] (Fin K → ℂ) :=
    { toFun := fun c => (b.repr.symm (WithLp.toLp 2 (extFn c))).ofLp
      map_add' := fun c₁ c₂ => by
        have hadd : WithLp.toLp 2 (extFn (c₁ + c₂)) =
            WithLp.toLp 2 (extFn c₁) + WithLp.toLp 2 (extFn c₂) := by
          ext i
          by_cases hi : i ∈ S_B <;> simp [extFn, hi]
        rw [hadd, map_add]
        rfl
      map_smul' := fun r c => by
        have hsmul : WithLp.toLp 2 (extFn (r • c)) = r • WithLp.toLp 2 (extFn c) := by
          ext i
          by_cases hi : i ∈ S_B <;> simp [extFn, hi]
        rw [hsmul, map_smul]
        rfl }
  have hΦ_inj : Function.Injective Φ := by
    intro c₁ c₂ heq
    have h1 : b.repr.symm (WithLp.toLp 2 (extFn c₁)) =
        b.repr.symm (WithLp.toLp 2 (extFn c₂)) := WithLp.ofLp_injective 2 heq
    have h2 : extFn c₁ = extFn c₂ :=
      WithLp.toLp_injective 2 (b.repr.symm.injective h1)
    ext idx
    have h3 := congrFun h2 idx.1
    simpa [extFn, idx.2] using h3
  refine ⟨LinearMap.range Φ, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hΦ_inj, Module.finrank_pi, Fintype.card_coe]
    rfl
  · rintro u ⟨c, rfl⟩
    let w : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 (extFn c)
    let wB : EuclideanSpace ℂ (Fin K) :=
      WithLp.toLp 2 (fun i : Fin K => extFn c i * ((hB.eigenvalues i : ℝ) : ℂ))
    have heucl : euclSq (Φ c) = ∑ i : Fin K, ‖extFn c i‖ ^ 2 := by
      unfold euclSq
      have h1 : ∑ i : Fin K, ‖(Φ c) i‖ ^ 2 = ‖b.repr.symm w‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        rfl
      rw [h1, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
    have hBmul : B *ᵥ (Φ c) = (b.repr.symm wB).ofLp := by
      have hrepr1 : (b.repr.symm w).ofLp = ∑ i : Fin K, extFn c i • (b i).ofLp := by
        rw [repr_symm_eq_sum]
        ext k
        simp [w]
      have hrepr2 : (b.repr.symm wB).ofLp =
          ∑ i : Fin K, (extFn c i * ((hB.eigenvalues i : ℝ) : ℂ)) • (b i).ofLp := by
        rw [repr_symm_eq_sum]
        ext k
        simp [wB]
      change B *ᵥ (b.repr.symm w).ofLp = (b.repr.symm wB).ofLp
      rw [hrepr1, hrepr2, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, show b i = hB.eigenvectorBasis i from rfl,
        hB.mulVec_eigenvectorBasis i]
      ext k
      simp [Complex.real_smul, mul_assoc, mul_comm ((hB.eigenvalues i : ℝ) : ℂ)]
    have hquad_eq : (star (Φ c) ⬝ᵥ (B *ᵥ (Φ c))).re =
        ∑ i : Fin K, hB.eigenvalues i * ‖extFn c i‖ ^ 2 := by
      rw [hBmul]
      change (star (b.repr.symm w).ofLp ⬝ᵥ (b.repr.symm wB).ofLp).re = _
      rw [← eucl_inner_eq_dotProduct, LinearIsometryEquiv.inner_map_map, eucl_inner_eq_dotProduct]
      simp only [w, wB, dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc_sq : star (extFn c i) * (extFn c i * ((hB.eigenvalues i : ℝ) : ℂ)) =
          ((hB.eigenvalues i * ‖extFn c i‖ ^ 2 : ℝ) : ℂ) := by
        have h1 : star (extFn c i) * (extFn c i * ((hB.eigenvalues i : ℝ) : ℂ)) =
            ((hB.eigenvalues i : ℝ) : ℂ) * (star (extFn c i) * extFn c i) := by ring
        have h2 : star (extFn c i) * extFn c i = ((‖extFn c i‖ ^ 2 : ℝ) : ℂ) := by
          simpa using (Complex.conj_mul' (extFn c i))
        rw [h1, h2, ← Complex.ofReal_mul]
      rw [hc_sq, Complex.ofReal_re]
    rw [heucl, hquad_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ S_B
    · have hge : (1 / 2 : ℝ) ≤ hB.eigenvalues i := (Finset.mem_filter.mp hi).2
      exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)
    · have hz : extFn c i = 0 := by simp [extFn, hi]
      simp [hz]

lemma card_filter_equiv {α β : Type*} [Fintype α] [Fintype β] (σ : α ≃ β)
    (P : β → Prop) [DecidablePred P] [DecidablePred (fun i => P (σ i))] :
    (Finset.univ.filter (fun i : α => P (σ i))).card =
      (Finset.univ.filter P).card := by
  refine Finset.card_nbij σ (fun i hi => ?_) σ.injective.injOn (fun j hj => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [σ.apply_symm_apply]

lemma eigCount_from_eigAt {K : ℕ} {F : Matrix (Fin K) (Fin K) ℂ} (hF : F.IsHermitian)
    {q : ℕ} {τ : ℝ} (hq_le : q ≤ K)
    (heig : ∀ j : ℕ, 1 ≤ j → j ≤ q → τ < eigAt hF (j - 1)) :
    q ≤ eigCountAbove hF τ := by
  unfold eigCountAbove
  have hcard_eq : (Finset.univ.filter (fun i : Fin K => τ < hF.eigenvalues i)).card =
      (Finset.univ.filter (fun j : Fin (Fintype.card (Fin K)) => τ < hF.eigenvalues₀ j)).card := by
    unfold Matrix.IsHermitian.eigenvalues
    exact card_filter_equiv _ (fun j => τ < hF.eigenvalues₀ j)
  rw [hcard_eq]
  have hq_card : q ≤ Fintype.card (Fin K) := by simpa using hq_le
  let emb : Fin q ↪ Fin (Fintype.card (Fin K)) :=
    ⟨fun r => ⟨r.1, lt_of_lt_of_le r.2 hq_card⟩, fun r₁ r₂ h => Fin.ext (Fin.mk.inj h)⟩
  calc
    q = (Finset.univ.map emb).card := by simp
    _ ≤ (Finset.univ.filter (fun j : Fin (Fintype.card (Fin K)) => τ < hF.eigenvalues₀ j)).card := by
      refine Finset.card_le_card ?_
      intro j hj
      rcases Finset.mem_map.mp hj with ⟨r, _, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change τ < hF.eigenvalues₀ ⟨r.1, lt_of_lt_of_le r.2 hq_card⟩
      have h1 := heig (r.1 + 1) (by omega) (by omega)
      have hlt : r.1 < Fintype.card (Fin K) := lt_of_lt_of_le r.2 hq_card
      have hsub : r.1 + 1 - 1 = r.1 := by omega
      rw [hsub] at h1
      unfold eigAt at h1
      rwa [dif_pos hlt] at h1

lemma four_log_le_eps_mul {ε : ℝ} (hε0 : 0 < ε) {L : ℝ} (hL_pos : 0 < L)
    (hL_ge : (2 / ε) * (4 * |Real.log (8 / ε)| + Real.log 2 + 2) ≤ L) :
    4 * Real.log L + Real.log 2 + 2 ≤ ε * L := by
  let M : ℝ := 8 / ε
  have hM_pos : 0 < M := by positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos hL_pos hM_pos)
  rw [Real.log_div (ne_of_gt hL_pos) (ne_of_gt hM_pos)] at h1
  have hdiv : L / M = (ε / 8) * L := by
    dsimp [M]
    field_simp [ne_of_gt hε0]
  rw [hdiv] at h1
  have hlogM : Real.log M ≤ |Real.log M| := le_abs_self _
  have h4log : 4 * Real.log L ≤ (ε / 2) * L + 4 * |Real.log M| := by linarith
  have hhalf : 4 * |Real.log M| + Real.log 2 + 2 ≤ (ε / 2) * L := by
    have hmul := mul_le_mul_of_nonneg_left hL_ge (half_pos hε0).le
    have hsimp : (ε / 2) * ((2 / ε) * (4 * |Real.log M| + Real.log 2 + 2)) =
        4 * |Real.log M| + Real.log 2 + 2 := by
      dsimp [M]
      field_simp [ne_of_gt hε0]
    dsimp [M] at hsimp ⊢
    linarith
  linarith

lemma log_mul_const_le_half {C₁₆ : ℝ} (hC : 0 < C₁₆) {X : ℝ} (hX_pos : 0 < X)
    (hX_ge : 4 * Real.pi * C₁₆ * |Real.log (4 * Real.pi * C₁₆)| ≤ X) :
    C₁₆ * Real.log X ≤ X / (2 * Real.pi) := by
  let M₂ : ℝ := 4 * Real.pi * C₁₆
  have hM₂_pos : 0 < M₂ := by positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos hX_pos hM₂_pos)
  rw [Real.log_div (ne_of_gt hX_pos) (ne_of_gt hM₂_pos)] at h1
  have h2 : C₁₆ * (X / M₂) = X / (4 * Real.pi) := by
    dsimp [M₂]
    field_simp [ne_of_gt hC, ne_of_gt Real.pi_pos]
  have hlogM₂ : Real.log M₂ ≤ |Real.log M₂| := le_abs_self _
  have hmul := mul_le_mul_of_nonneg_left h1 hC.le
  have h3 : C₁₆ * Real.log X ≤ X / (4 * Real.pi) + C₁₆ * |Real.log M₂| := by
    nlinarith
  have h4 : C₁₆ * |Real.log M₂| ≤ X / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    dsimp [M₂] at hX_ge ⊢
    linarith
  have hsum_div : X / (4 * Real.pi) + X / (4 * Real.pi) = X / (2 * Real.pi) := by ring
  linarith only [h3, h4, hsum_div]

end AuxThm12

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ a Clb : ℝ, 0 < a ∧ 0 < Clb ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (d : ℕ) (c : ℕ → ℂ) (η : ℝ), 0 < η → IsBLT d c → coeffErr n sqrtSeq c ≤ η →
        a ≤ Real.log (1 / η) →
        Real.log (1 / η) ≤ (1 / 2 - ε) * Real.log (((n + 1) / 2 : ℕ) : ℝ) →
        Clb * Real.log n * Real.log (1 / η) ≤ (d : ℝ) := by
  rcases proposition_4_7 with ⟨a₁, ha₁_pos, h47_ex, C₄₇, A₀, hC₄₇_pos, h47_asymp⟩
  rcases lemma_3_16 with ⟨C₁₆, X₀, hC₁₆_pos, h316⟩
  rcases lemma_4_6 ε hε0 hε1 1 zero_lt_one with ⟨m₄₆, h46⟩
  let a : ℝ := max (max a₁ A₀) (max 16 (8 * Real.pi * C₄₇ + 8))
  have ha_pos : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16)
    (le_trans (le_max_left _ _) (le_max_right _ _))
  let Clb : ℝ := ε / (8 * Real.pi ^ 2)
  have hClb_pos : 0 < Clb := by positivity
  let X_req : ℝ := max (max X₀ 4)
    (4 * Real.pi * C₁₆ * |Real.log (4 * Real.pi * C₁₆)|)
  let L_min : ℝ := max 16
    (max ((2 / ε) * (4 * |Real.log (8 / ε)| + Real.log 2 + 2))
      ((Real.pi / (8 * ε)) * X_req))
  let n₀ : ℕ := max (2 * m₄₆ + 4) (⌈2 * Real.exp L_min⌉₊ + 10)
  refine ⟨a, Clb, ha_pos, hClb_pos, n₀, fun n hn d c η hη hc herr haA hAL => ?_⟩
  let m : ℕ := (n + 1) / 2
  have hn_ge10 : 10 ≤ n := le_trans (Nat.le_add_left 10 _) (le_trans (le_max_right _ _) hn)
  have hm_ge_m46 : m₄₆ ≤ m := by
    have h1 : 2 * m₄₆ + 4 ≤ n := le_trans (le_max_left _ _) hn
    dsimp [m]
    omega
  have hm_ge5 : 5 ≤ m := by dsimp [m]; omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have h2m_ge_n : (n : ℝ) ≤ 2 * (m : ℝ) := by
    have hnat : n ≤ 2 * m := by dsimp [m]; omega
    exact_mod_cast hnat
  have hexp_Lmin_le_m : Real.exp L_min ≤ (m : ℝ) := by
    have h1 : ⌈2 * Real.exp L_min⌉₊ + 10 ≤ n := le_trans (le_max_right _ _) hn
    have h2 : 2 * Real.exp L_min ≤ (⌈2 * Real.exp L_min⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈2 * Real.exp L_min⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : ⌈2 * Real.exp L_min⌉₊ ≤ n)
    linarith
  let L : ℝ := Real.log (m : ℝ)
  have hL_ge_min : L_min ≤ L := by
    dsimp [L]
    rw [← Real.log_exp L_min]
    exact Real.log_le_log (Real.exp_pos _) hexp_Lmin_le_m
  have hL_ge16 : 16 ≤ L := le_trans (le_max_left _ _) hL_ge_min
  have hL_pos : 0 < L := by linarith
  have hL_eps : 4 * Real.log L + Real.log 2 + 2 ≤ ε * L :=
    AuxThm12.four_log_le_eps_mul hε0 hL_pos
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hL_ge_min))
  have hL_Xreq : (Real.pi / (8 * ε)) * X_req ≤ L :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL_ge_min)
  let A : ℝ := Real.log (1 / η)
  have hA_ge16 : 16 ≤ A :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) haA
  have hA_pos : 0 < A := by linarith
  have hη_exp : η = Real.exp (-A) := by
    dsimp [A]
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hη]
  have hη_lt1 : η < 1 := by
    rw [hη_exp, Real.exp_lt_one_iff]
    linarith
  -- Obtain ω from Proposition 4.7
  have ha₁_le_A : a₁ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) haA
  have hA₀_le_A : A₀ ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) haA
  have h8piC_le_A : 8 * Real.pi * C₄₇ + 8 ≤ A :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) haA
  rcases (h47_ex η hη ha₁_le_A).exists with ⟨ω, hω_pos, hω_eq⟩
  have hω_asymp := h47_asymp η hη hA₀_le_A ω hω_pos hω_eq
  -- Deduce A / (2 * π) ≤ ω ≤ A
  have hlogA_bound : Real.log A ≤ A / 4 + 1 := by
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < A / 4)
    rw [Real.log_div (ne_of_gt hA_pos) (by norm_num)] at h1
    have hlog4_lt2 : Real.log 4 < 2 := by
      have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (4 : ℝ) < Real.exp 2 := by rw [he2]; nlinarith
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h4
    linarith
  have hlogA_pos : 0 < Real.log A := Real.log_pos (by linarith)
  have hC47_le : C₄₇ ≤ A / (8 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hω_lb : A / (2 * Real.pi) ≤ ω := by
    have habs := (abs_sub_le_iff.mp hω_asymp).2
    have hmain : (3 / 4 : ℝ) * A ≤ A - (1 / 2) * Real.log A := by linarith
    have hdiv : (3 / (4 * Real.pi)) * A ≤ (1 / Real.pi) * (A - (1 / 2) * Real.log A) := by
      have hmul := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 1 / Real.pi)
      have hrew : (1 / Real.pi) * ((3 / 4) * A) = (3 / (4 * Real.pi)) * A := by ring
      linarith
    have hsub : A / (2 * Real.pi) ≤ (3 / (4 * Real.pi)) * A - A / (8 * Real.pi) := by
      have hrew : (3 / (4 * Real.pi)) * A - A / (8 * Real.pi) = (5 / (8 * Real.pi)) * A := by ring
      have hrew2 : A / (2 * Real.pi) = (4 / (8 * Real.pi)) * A := by ring
      rw [hrew, hrew2]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by norm_num) (by positivity)) hA_pos.le
    linarith
  have hω_ub : ω ≤ A := by
    have habs := (abs_sub_le_iff.mp hω_asymp).1
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    have h1 : (1 / Real.pi) * (A - (1 / 2) * Real.log A) ≤ A / 3 := by
      calc
        (1 / Real.pi) * (A - (1 / 2) * Real.log A) ≤ (1 / Real.pi) * A := by
          refine mul_le_mul_of_nonneg_left (by linarith only [hlogA_pos]) (by positivity)
        _ = A / Real.pi := one_div_mul_eq_div Real.pi A
        _ ≤ A / 3 := div_le_div_of_nonneg_left hA_pos.le (by norm_num) hpi3.le
    have h2 : C₄₇ ≤ A / 24 := by
      have h3 : A / (8 * Real.pi) ≤ A / 24 :=
        div_le_div_of_nonneg_left hA_pos.le (by norm_num) (by linarith only [hpi3])
      linarith only [hC47_le, h3]
    linarith only [habs, h1, h2, hA_pos]
  -- Section 4 parameters R, h, K
  let R := sectionR m η
  let h := sectionH m η
  let K := sectionK m η
  have hh0 : 0 < h := div_pos hη hL_pos
  have hh1 : h ≤ 1 := by
    dsimp [h, sectionH]
    rw [div_le_one hL_pos]
    linarith
  have hL4_ge1 : 1 ≤ L ^ 4 / η ^ 2 := by
    rw [ one_le_div (by positivity)]
    have hη2 : η ^ 2 ≤ 1 := by nlinarith
    have hL4 : (1 : ℝ) ≤ L ^ 4 := by
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ L) 4
    linarith
  have hR_ge_quot : L ^ 4 / η ^ 2 ≤ (R : ℝ) := Nat.le_ceil _
  have hR_le_2quot : (R : ℝ) ≤ 2 * (L ^ 4 / η ^ 2) := by
    have hlt : (R : ℝ) < L ^ 4 / η ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hR1 : 1 ≤ R := by
    have h1 : (1 : ℝ) ≤ (R : ℝ) := le_trans hL4_ge1 hR_ge_quot
    exact_mod_cast h1
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
  have hRh_gt1 : 1 < (R : ℝ) * h := by
    have hge : L ^ 3 / η ≤ (R : ℝ) * h := by
      calc
        L ^ 3 / η = (L ^ 4 / η ^ 2) * (η / L) := by field_simp [ne_of_gt hη, ne_of_gt hL_pos]
        _ ≤ (R : ℝ) * h := mul_le_mul_of_nonneg_right hR_ge_quot hh0.le
    have hL3 : (8 : ℝ) ≤ L ^ 3 := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ L) 3
    have hgt : 1 < L ^ 3 / η := by rw [one_lt_div hη]; linarith
    exact lt_of_lt_of_le hgt hge
  -- Bound log(m / R) ≥ ε * L + 2
  have hlogR_ub : Real.log (R : ℝ) ≤ Real.log 2 + 4 * Real.log L + 2 * A := by
    have h1 := Real.log_le_log hR_pos hR_le_2quot
    have hquot_eq : 2 * (L ^ 4 / η ^ 2) = 2 * L ^ 4 * Real.exp (2 * A) := by
      have hη2_eq : η ^ 2 = (Real.exp (2 * A))⁻¹ := by
        rw [hη_exp, sq, ← Real.exp_add, ← Real.exp_neg]
        congr 1
        ring
      rw [hη2_eq, div_inv_eq_mul, mul_assoc]
    rw [hquot_eq, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp] at h1
    push_cast at h1
    linarith only [h1]
  have h2A_ub : 2 * A ≤ (1 - 2 * ε) * L := by
    have h := mul_le_mul_of_nonneg_left hAL (by norm_num : (0 : ℝ) ≤ 2)
    change 2 * A ≤ 2 * ((1 / 2 - ε) * L) at h
    have hrew : 2 * ((1 / 2 - ε) * L) = (1 - 2 * ε) * L := by ring
    linarith only [h, hrew]
  have hlog_mR_lb : ε * L + 2 ≤ Real.log ((m : ℝ) / (R : ℝ)) := by
    rw [Real.log_div (ne_of_gt hm_pos) (ne_of_gt hR_pos)]
    change ε * L + 2 ≤ L - Real.log (R : ℝ)
    linarith only [hL_eps, hlogR_ub, h2A_ub]
  have hKh_lb : ε * L ≤ (K : ℝ) * h := by
    have hfl : Real.log ((m : ℝ) / (R : ℝ)) / h - 1 < (K : ℝ) := Nat.sub_one_lt_floor _
    have hmul := mul_lt_mul_of_pos_right hfl hh0
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hh0), one_mul] at hmul
    linarith only [hlog_mR_lb, hh1, hmul]
  have hK_ge1 : 1 ≤ K := by
    have hpos : 0 < (K : ℝ) * h := lt_of_lt_of_le (by positivity) hKh_lb
    have hK_pos : 0 < (K : ℝ) := pos_of_mul_pos_left hpos hh0.le
    by_contra h0
    have hK0 : K = 0 := by omega
    rw [hK0] at hK_pos
    norm_num at hK_pos
  have hbp_le_m : blockPoint R h K ≤ (m : ℝ) := by
    have hlog_nn : 0 ≤ Real.log ((m : ℝ) / (R : ℝ)) / h := by
      have h1 : 0 ≤ ε * L + 2 := by positivity
      exact div_nonneg (le_trans h1 hlog_mR_lb) hh0.le
    have hfl : (K : ℝ) ≤ Real.log ((m : ℝ) / (R : ℝ)) / h := Nat.floor_le hlog_nn
    have hmul : (K : ℝ) * h ≤ Real.log ((m : ℝ) / (R : ℝ)) := (le_div_iff₀ hh0).mp hfl
    rw [Real.log_div (ne_of_gt hm_pos) (ne_of_gt hR_pos)] at hmul
    unfold blockPoint
    rw [← Real.exp_log hm_pos]
    exact Real.exp_le_exp.mpr (by linarith only [hmul])
  -- Apply Corollary 4.3 to S = blockUnion R h K and Q = blockIsometry R h K
  let S := blockUnion R h K
  let Q := blockIsometry R h K
  have hS_ne : S.Nonempty := by
    rcases AuxThm12.block_nonempty hR1 hh0 hRh_gt1 0 with ⟨r₀, hr₀⟩
    exact ⟨r₀, Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by omega), hr₀⟩⟩
  have hS_sub : S ⊆ Finset.Ico 1 m := AuxThm12.blockUnion_subset_Ico hR1 hh0 hbp_le_m
  have hQ_iso : Qᴴ * Q = 1 := AuxThm12.blockIsometry_isometry hR1 hh0 hRh_gt1 K
  rcases (corollary_4_3 n d c η hη hc herr S hS_ne hS_sub K Q hQ_iso).2.2 with ⟨hF, heigF_le_d⟩
  -- Operator-norm approximation from Lemma 4.6 (with δ = 1)
  have hspec_err : specNorm (blockCompression R h K sqrtSeq - rescaledToeplitz K h) ≤ η := by
    simpa [R, h, K] using h46 m hm_ge_m46 η hη hA_pos hAL
  -- Band matrix angle θ_* = h * ω
  let θ := h * ω
  have hθ0 : 0 < θ := mul_pos hh0 hω_pos
  have hθπ : θ ≤ Real.pi := by
    have h1 : θ ≤ η * A / L := by
      dsimp [θ, h, sectionH]
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω_ub hη.le) hL_pos.le
    have hAL_rough : A ≤ L := by
      have hsub_le : (1 / 2 - ε) * L ≤ 1 * L :=
        mul_le_mul_of_nonneg_right (by linarith only [hε0]) hL_pos.le
      change A ≤ (1 / 2 - ε) * L at hAL
      linarith only [hAL, hsub_le]
    have h2 : η * A / L ≤ 1 := by
      rw [div_le_one hL_pos]
      calc η * A ≤ 1 * A := mul_le_mul_of_nonneg_right hη_lt1.le hA_pos.le
        _ = A := one_mul A
        _ ≤ L := hAL_rough
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    linarith only [h1, h2, hpi3]
  -- Check X := K * θ ≥ X_req
  have hX_lb_LA : (ε / (2 * Real.pi)) * L * A ≤ (K : ℝ) * θ := by
    calc
      (ε / (2 * Real.pi)) * L * A = (ε * L) * (A / (2 * Real.pi)) := by ring
      _ ≤ ((K : ℝ) * h) * ω :=
        mul_le_mul hKh_lb hω_lb (by positivity) (by positivity)
      _ = (K : ℝ) * θ := by dsimp [θ]; ring
  have hX_ge_req : X_req ≤ (K : ℝ) * θ := by
    have h1 : X_req ≤ (8 * ε / Real.pi) * L := by
      have hmul := mul_le_mul_of_nonneg_left hL_Xreq (by positivity : 0 ≤ 8 * ε / Real.pi)
      have hsimp : (8 * ε / Real.pi) * ((Real.pi / (8 * ε)) * X_req) = X_req := by
        field_simp [ne_of_gt hε0, ne_of_gt Real.pi_pos]
      linarith only [hmul, hsimp]
    have h2 : (8 * ε / Real.pi) * L ≤ (ε / (2 * Real.pi)) * L * A := by
      have hrew : (8 * ε / Real.pi) * L = (ε / (2 * Real.pi)) * L * 16 := by ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left hA_ge16 (by positivity)
    linarith only [h1, h2, hX_lb_LA]
  have hX₀_le : X₀ ≤ (K : ℝ) * θ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX_ge_req
  rcases h316 K θ hθ0 hθπ hX₀_le with ⟨hB, hq_lb⟩
  let q : ℕ := eigCountAtLeast hB (1 / 2)
  -- Show q ≤ d via Courant-Fischer (Theorem 2.1) + Corollary 4.3
  rcases AuxThm12.band_subspace_exists hB with ⟨U, hU_dim, hU_quad⟩
  have hq_le_K : q ≤ K := by
    calc
      q = Module.finrank ℂ U := hU_dim.symm
      _ ≤ Module.finrank ℂ (Fin K → ℂ) := Submodule.finrank_le U
      _ = K := Module.finrank_fin_fun ℂ
  have hF_quad : ∀ u ∈ U, 3 * η * euclSq u ≤
      (star u ⬝ᵥ (blockCompression R h K sqrtSeq *ᵥ u)).re := by
    intro u hu
    have hdom := AuxThm12.rescaledToeplitz_dom_bandMatrix K hh0 hη hω_pos hω_eq hθπ u
    have hbu := hU_quad u hu
    have hvh : 4 * η * euclSq u ≤ (star u ⬝ᵥ (rescaledToeplitz K h *ᵥ u)).re := by
      have hmul := mul_le_mul_of_nonneg_left hbu (by positivity : 0 ≤ 8 * η)
      have h48 : 8 * η * (1 / 2 * euclSq u) = 4 * η * euclSq u := by ring
      linarith only [hdom, hmul, h48]
    let E := blockCompression R h K sqrtSeq - rescaledToeplitz K h
    have hpert := AuxThm12.pert_bound E u
    have hpert_η : |(star u ⬝ᵥ (E *ᵥ u)).re| ≤ η * euclSq u := by
      refine le_trans hpert ?_
      exact mul_le_mul_of_nonneg_right hspec_err (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hsplit_u : star u ⬝ᵥ (blockCompression R h K sqrtSeq *ᵥ u) =
        star u ⬝ᵥ (rescaledToeplitz K h *ᵥ u) + star u ⬝ᵥ (E *ᵥ u) := by
      dsimp [E]
      rw [← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel]
    have hre_split : (star u ⬝ᵥ (blockCompression R h K sqrtSeq *ᵥ u)).re =
        (star u ⬝ᵥ (rescaledToeplitz K h *ᵥ u)).re + (star u ⬝ᵥ (E *ᵥ u)).re := by
      rw [hsplit_u, Complex.add_re]
    have hpert_lo := (abs_le.mp hpert_η).1
    have h34 : 4 * η * euclSq u - η * euclSq u = 3 * η * euclSq u := by ring
    linarith only [hvh, hre_split, hpert_lo, h34]
  have hCF := (theorem_2_1 K (blockCompression R h K sqrtSeq) hF).2 q (3 * η) U hU_dim hF_quad
  have hq_le_eigF : q ≤ eigCountAbove hF (2 * η) := by
    refine AuxThm12.eigCount_from_eigAt hF hq_le_K fun j hj1 hjq => ?_
    have h23 : 2 * η < 3 * η := by linarith only [hη]
    exact lt_of_lt_of_le h23 (hCF j hj1 hjq)
  have hq_le_d : (q : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast le_trans hq_le_eigF heigF_le_d
  -- Conclude Clb * log n * log(1/η) ≤ q ≤ d
  have hlogX_small : C₁₆ * Real.log ((K : ℝ) * θ) ≤ ((K : ℝ) * θ) / (2 * Real.pi) :=
    AuxThm12.log_mul_const_le_half hC₁₆_pos (mul_pos (Nat.cast_pos.mpr (by omega)) hθ0)
      (le_trans (le_max_right _ _) hX_ge_req)
  have hq_half : ((K : ℝ) * θ) / (2 * Real.pi) ≤ (q : ℝ) := by
    have hdiv : (K : ℝ) * θ / Real.pi - ((K : ℝ) * θ) / (2 * Real.pi) =
        ((K : ℝ) * θ) / (2 * Real.pi) := by ring
    change (K : ℝ) * θ / Real.pi - C₁₆ * Real.log ((K : ℝ) * θ) ≤ (q : ℝ) at hq_lb
    linarith only [hq_lb, hlogX_small, hdiv]
  have hlogn_le_2L : Real.log (n : ℝ) ≤ 2 * L := by
    have hn_le_m2 : (n : ℝ) ≤ (m : ℝ) ^ 2 := by
      have hn10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge10
      nlinarith only [hn10, h2m_ge_n]
    have hlog := Real.log_le_log (by positivity) hn_le_m2
    rw [Real.log_pow] at hlog
    push_cast at hlog
    exact hlog
  calc
    Clb * Real.log (n : ℝ) * A
        ≤ Clb * (2 * L) * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA_pos.le
          exact mul_le_mul_of_nonneg_left hlogn_le_2L hClb_pos.le
    _ = (1 / (2 * Real.pi)) * ((ε / (2 * Real.pi)) * L * A) := by
      dsimp [Clb]
      ring
    _ ≤ (1 / (2 * Real.pi)) * ((K : ℝ) * θ) :=
      mul_le_mul_of_nonneg_left hX_lb_LA (by positivity)
    _ = ((K : ℝ) * θ) / (2 * Real.pi) := by ring
    _ ≤ (q : ℝ) := hq_half
    _ ≤ (d : ℝ) := hq_le_d

