-- Prove2me | solution 1 for BrailovskayaVanHandel.prob_norm_sum_gt_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T01:23:16.735363+00:00
-- url     : https://prove2.me/submissions/5c809d87-3765-4bc8-a64d-e556021cf1f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_BrailovskayaVanHandel_prob_abs_norm_sub_gaussian_gt_le_and_abs_expect_norm_sub_le
import Theorems.Thm_BandeiraBoedihardjoVanHandel_prob_norm_gaussian_gt_le_and_integral_norm_le

section
open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace StrongConvHighDeg.C217.PartL
/-- Splitting off coordinate `i`: a sum over `Fin n → Ω` is a sum over the value at `i` and the
remaining coordinates. -/
theorem sum_split {n : ℕ} {Ω E : Type*} [Fintype Ω] [AddCommMonoid E] (i : Fin n)
    (F : (Fin n → Ω) → E) :
    ∑ x : Fin n → Ω, F x =
      ∑ ω : Ω, ∑ y : ({j // j ≠ i} → Ω), F ((Equiv.funSplitAt i Ω).symm (ω, y)) := by
  rw [← (Equiv.funSplitAt i Ω).symm.sum_comp, Fintype.sum_prod_type]

theorem split_apply_self {n : ℕ} {Ω : Type*} (i : Fin n) (ω : Ω) (y : {j // j ≠ i} → Ω) :
    (Equiv.funSplitAt i Ω).symm (ω, y) i = ω := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem split_apply_ne {n : ℕ} {Ω : Type*} (i j : Fin n) (h : j ≠ i) (ω : Ω)
    (y : {j // j ≠ i} → Ω) :
    (Equiv.funSplitAt i Ω).symm (ω, y) j = y ⟨j, h⟩ := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

theorem sum_coord {n : ℕ} {Ω E : Type*} [Fintype Ω] [AddCommMonoid E] (i : Fin n)
    (f : Ω → E) :
    ∑ x : Fin n → Ω, f (x i) = Fintype.card ({j // j ≠ i} → Ω) • ∑ ω, f ω := by
  rw [sum_split i, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp

theorem sum_cross {n : ℕ} {Ω M E : Type*} [Fintype Ω] [AddCommGroup M] [AddCommGroup E]
    (B : M →+ M →+ E) (Z : Fin n → Ω → M) (hZ : ∀ i, ∑ ω, Z i ω = 0) (i j : Fin n)
    (hij : i ≠ j) :
    ∑ x : Fin n → Ω, B (Z i (x i)) (Z j (x j)) = 0 := by
  rw [sum_split i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  simp only [split_apply_self, split_apply_ne i j (Ne.symm hij)]
  rw [← AddMonoidHom.finsetSum_apply, ← map_sum, hZ i, map_zero, AddMonoidHom.zero_apply]

theorem avg_bilin {n : ℕ} {Ω M E : Type*} [Fintype Ω] [Nonempty Ω] [AddCommGroup M]
    [AddCommGroup E] [Module ℂ E] (B : M →+ M →+ E) (Z : Fin n → Ω → M)
    (hZ : ∀ i, ∑ ω, Z i ω = 0) :
    ((Fintype.card (Fin n → Ω) : ℂ))⁻¹ • ∑ x : Fin n → Ω, B (∑ i, Z i (x i)) (∑ j, Z j (x j)) =
      ∑ i, ((Fintype.card Ω : ℂ))⁻¹ • ∑ ω, B (Z i ω) (Z i ω) := by
  have hexp : ∀ x : Fin n → Ω, B (∑ i, Z i (x i)) (∑ j, Z j (x j)) =
      ∑ i, ∑ j, B (Z i (x i)) (Z j (x j)) := by
    intro x
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
    first | rfl | exact Finset.sum_comm
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single i (fun j _ hji => sum_cross B Z hZ i j (Ne.symm hji))
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [sum_coord i (fun ω => B (Z i ω) (Z i ω))]
  have hcard : Fintype.card (Fin n → Ω) =
      Fintype.card Ω * Fintype.card ({j // j ≠ i} → Ω) := by
    rw [Fintype.card_congr (Equiv.funSplitAt i Ω), Fintype.card_prod]
  have hpos : (Fintype.card ({j // j ≠ i} → Ω) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card ({j // j ≠ i} → Ω) := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv,
    mul_assoc, inv_mul_cancel₀ hpos, mul_one]

end StrongConvHighDeg.C217.PartL
end

section
open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace StrongConvHighDeg.C217
/-!
# Brailovskaya–van Handel Corollary 2.17 (finite uniform, self-adjoint form) from
# their Corollary 2.7 and Bandeira–Boedihardjo–van Handel Corollary 2.2 + Lemma 2.5

The Gaussian model of `Y = ∑ᵢ Zᵢ(ωᵢ)` is `G = ∑_{(i,ω)} g_{iω} |Ω|^{-1/2} Zᵢ(ω)`; it has the
covariance of `Y` (`avg_bilin`), so BBvH bounds `E‖G‖ ≤ 2σ + C √v √σ (log D)^{3/4}`, and BvH
Corollary 2.7 puts `‖Y‖` within `C ε(t)` of `E‖G‖` outside probability `D e^{-t}`.
-/
alias avg_bilin := StrongConvHighDeg.C217.PartL.avg_bilin

end StrongConvHighDeg.C217
end

section
open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace StrongConvHighDeg.C217.PartL
theorem sum_sum_eq_zero {n : ℕ} {Ω M : Type*} [Fintype Ω] [AddCommGroup M]
    (Z : Fin n → Ω → M) (hZ : ∀ i, ∑ ω, Z i ω = 0) :
    ∑ x : Fin n → Ω, ∑ i, Z i (x i) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sum_coord i (Z i), hZ i, smul_zero]

end StrongConvHighDeg.C217.PartL
end

section
open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace StrongConvHighDeg.C217
alias sum_sum_eq_zero := StrongConvHighDeg.C217.PartL.sum_sum_eq_zero

end StrongConvHighDeg.C217
end

section
open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace StrongConvHighDeg.C217.PartM
theorem cor217 :
    ∃ C : ℝ, 0 < C ∧ ∀ (D n : ℕ) (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (Z : Fin n → Ω → Matrix (Fin D) (Fin D) ℂ), 2 ≤ D →
      (∀ i ω, (Z i ω).IsHermitian) → (∀ i, ∑ ω, Z i ω = 0) → ∀ t : ℝ, 0 ≤ t →
      let card : ℝ := Fintype.card (Fin n → Ω)
      let Y : (Fin n → Ω) → Matrix (Fin D) (Fin D) ℂ := fun ω => ∑ i, Z i (ω i)
      let EY : Matrix (Fin D) (Fin D) ℂ := (card : ℂ)⁻¹ • ∑ ω, Y ω
      let σ : ℝ := Real.sqrt
        ‖toEuclideanCLM (𝕜 := ℂ) ((card : ℂ)⁻¹ • ∑ ω, (Y ω - EY) * (Y ω - EY))‖
      let σStar : ℝ := ⨆ (v : EuclideanSpace ℂ (Fin D)) (w : EuclideanSpace ℂ (Fin D))
        (_ : ‖v‖ = 1 ∧ ‖w‖ = 1),
        Real.sqrt ((∑ ω, ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (Y ω - EY) w⟫_ℂ‖ ^ 2) / card)
      let Cov : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun p q =>
        (card : ℂ)⁻¹ * ∑ ω, (Y ω - EY) p.1 p.2 * conj ((Y ω - EY) q.1 q.2)
      let v : ℝ := Real.sqrt ‖toEuclideanCLM (𝕜 := ℂ) Cov‖
      let R : ℝ := ⨆ (i : Fin n) (ω : Ω), ‖toEuclideanCLM (𝕜 := ℂ) (Z i ω)‖
      ((Finset.univ.filter fun ω : Fin n → Ω =>
          2 * σ + C * (Real.sqrt v * Real.sqrt σ * Real.log D ^ ((3 : ℝ) / 4) +
            σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
            R * t) < ‖toEuclideanCLM (𝕜 := ℂ) (Y ω)‖).card : ℝ) / card ≤
        4 * D * Real.exp (-t) := by
  obtain ⟨CA, hCA, hA⟩ :=
    BrailovskayaVanHandel.prob_abs_norm_sub_gaussian_gt_le_and_abs_expect_norm_sub_le
  obtain ⟨CB, hCB, hB⟩ := BandeiraBoedihardjoVanHandel.prob_norm_gaussian_gt_le_and_integral_norm_le
  refine ⟨max CA CB, lt_max_of_lt_left hCA, ?_⟩
  intro D n Ω _ _ Z hD hZ hZ0 t ht
  have hA' := (hA D n Ω 0 Z hD Matrix.isHermitian_zero hZ hZ0).1 t ht
  have hB' := (hB D (Fin n × Ω) 0
    (fun k => (((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2) hD).2
  simp only [zero_add] at hA' hB'
  intro card Y EY σ σStar Cov v R
  have hN : (0:ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hcard : (0:ℝ) < card := by
    show (0:ℝ) < (Fintype.card (Fin n → Ω) : ℝ); exact_mod_cast Fintype.card_pos
  have hEY : EY = 0 := by
    show ((card:ℂ))⁻¹ • ∑ ω : Fin n → Ω, ∑ i, Z i (ω i) = 0
    rw [sum_sum_eq_zero Z hZ0, smul_zero]
  have hcc : ((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ)) *
      ((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ)) = ((Fintype.card Ω : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hN.le]; push_cast; rfl
  have hAH : ∀ k : Fin n × Ω, ((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2)ᴴ =
      (((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2 := by
    intro k; rw [Matrix.conjTranspose_smul, (hZ k.1 k.2).eq, Complex.star_def, Complex.conj_ofReal]
  have hs : ∑ k : Fin n × Ω, ((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2) *
      ((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2) =
      (card : ℂ)⁻¹ • ∑ ω, (Y ω - EY) * (Y ω - EY) := by
    rw [hEY]
    simp only [sub_zero]
    have h := avg_bilin (AddMonoidHom.mul : Matrix (Fin D) (Fin D) ℂ →+ _ →+ _) Z hZ0
    simp only [AddMonoidHom.mul_apply] at h
    show _ = (((Fintype.card (Fin n → Ω) : ℝ)) : ℂ)⁻¹ •
      ∑ ω : Fin n → Ω, (∑ i, Z i (ω i)) * (∑ i, Z i (ω i))
    rw [Complex.ofReal_natCast, h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc]
  have hcov : (fun p q : Fin D × Fin D => ∑ k : Fin n × Ω,
      ((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2) p.1 p.2 *
        conj (((((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2) q.1 q.2)) = Cov := by
    funext p q
    show _ = (card : ℂ)⁻¹ * ∑ ω, (Y ω - EY) p.1 p.2 * conj ((Y ω - EY) q.1 q.2)
    rw [hEY]
    simp only [sub_zero]
    let B : Matrix (Fin D) (Fin D) ℂ →+ Matrix (Fin D) (Fin D) ℂ →+ ℂ :=
      { toFun := fun M =>
          { toFun := fun N => M p.1 p.2 * conj (N q.1 q.2)
            map_zero' := by simp
            map_add' := by intros; simp [mul_add] }
        map_zero' := by ext; simp
        map_add' := by intros; ext; simp [add_mul] }
    have h := avg_bilin B Z hZ0
    simp only [B, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul] at h
    show _ = (((Fintype.card (Fin n → Ω) : ℝ)) : ℂ)⁻¹ *
      ∑ ω : Fin n → Ω, (∑ i, Z i (ω i)) p.1 p.2 * conj ((∑ i, Z i (ω i)) q.1 q.2)
    rw [Complex.ofReal_natCast, h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    rw [← hcc]; ring
  simp only [hAH] at hB'
  rw [hs, hcov] at hB'
  generalize hEG : (∫ g : Fin n × Ω → ℝ, ‖toEuclideanCLM (𝕜 := ℂ)
    (∑ k, (g k : ℂ) • (((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2)‖
      ∂(Measure.pi fun _ => gaussianReal 0 1)) = EG at hA' hB'
  have hB2 : EG ≤ ‖toEuclideanCLM (𝕜 := ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)‖ + σ + σ +
      CB * Real.sqrt v * Real.sqrt (max σ σ) * Real.log D ^ ((3:ℝ)/4) := hB'
  rw [map_zero, norm_zero, max_self, zero_add] at hB2
  have hA2 : ((Finset.univ.filter fun ω : Fin n → Ω =>
      CA * (σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
        R * t) < |‖toEuclideanCLM (𝕜 := ℂ) (Y ω)‖ - EG|).card : ℝ) / card ≤
      D * Real.exp (-t) := hA'
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσS : 0 ≤ σStar := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hL : 0 ≤ Real.log D ^ ((3:ℝ)/4) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))) _
  have hε : 0 ≤ σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
      R * t :=
    add_nonneg (add_nonneg (mul_nonneg hσS (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hR _) (Real.rpow_nonneg hσ0 _))
        (Real.rpow_nonneg ht _))) (mul_nonneg hR ht)
  have hvσL : 0 ≤ Real.sqrt v * Real.sqrt σ * Real.log D ^ ((3:ℝ)/4) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hL
  have hsub : (Finset.univ.filter fun ω : Fin n → Ω =>
          2 * σ + max CA CB * (Real.sqrt v * Real.sqrt σ * Real.log D ^ ((3 : ℝ) / 4) +
            σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
            R * t) < ‖toEuclideanCLM (𝕜 := ℂ) (Y ω)‖) ⊆
      (Finset.univ.filter fun ω : Fin n → Ω =>
      CA * (σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
        R * t) < |‖toEuclideanCLM (𝕜 := ℂ) (Y ω)‖ - EG|) := by
    intro ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    refine lt_of_lt_of_le ?_ (le_abs_self _)
    have h1 := mul_le_mul_of_nonneg_right (le_max_left CA CB) hε
    have h2 := mul_le_mul_of_nonneg_right (le_max_right CA CB) hvσL
    nlinarith
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
    hcard.le) (hA2.trans ?_)
  have := Real.exp_pos (-t)
  have : (0:ℝ) ≤ D := Nat.cast_nonneg _
  nlinarith

end StrongConvHighDeg.C217.PartM
end

open Matrix ComplexConjugate in
open scoped InnerProductSpace in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (D n : ℕ) (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (Z : Fin n → Ω → Matrix (Fin D) (Fin D) ℂ), 2 ≤ D →
      (∀ i ω, (Z i ω).IsHermitian) → (∀ i, ∑ ω, Z i ω = 0) → ∀ t : ℝ, 0 ≤ t →
      let card : ℝ := Fintype.card (Fin n → Ω)
      let Y : (Fin n → Ω) → Matrix (Fin D) (Fin D) ℂ := fun ω => ∑ i, Z i (ω i)
      let EY : Matrix (Fin D) (Fin D) ℂ := (card : ℂ)⁻¹ • ∑ ω, Y ω
      let σ : ℝ := Real.sqrt
        ‖toEuclideanCLM (𝕜 := ℂ) ((card : ℂ)⁻¹ • ∑ ω, (Y ω - EY) * (Y ω - EY))‖
      let σStar : ℝ := ⨆ (v : EuclideanSpace ℂ (Fin D)) (w : EuclideanSpace ℂ (Fin D))
        (_ : ‖v‖ = 1 ∧ ‖w‖ = 1),
        Real.sqrt ((∑ ω, ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (Y ω - EY) w⟫_ℂ‖ ^ 2) / card)
      let Cov : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun p q =>
        (card : ℂ)⁻¹ * ∑ ω, (Y ω - EY) p.1 p.2 * conj ((Y ω - EY) q.1 q.2)
      let v : ℝ := Real.sqrt ‖toEuclideanCLM (𝕜 := ℂ) Cov‖
      let R : ℝ := ⨆ (i : Fin n) (ω : Ω), ‖toEuclideanCLM (𝕜 := ℂ) (Z i ω)‖
      ((Finset.univ.filter fun ω : Fin n → Ω =>
          2 * σ + C * (Real.sqrt v * Real.sqrt σ * Real.log D ^ ((3 : ℝ) / 4) +
            σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
            R * t) < ‖toEuclideanCLM (𝕜 := ℂ) (Y ω)‖).card : ℝ) / card ≤
        4 * D * Real.exp (-t) :=
  StrongConvHighDeg.C217.PartM.cor217
