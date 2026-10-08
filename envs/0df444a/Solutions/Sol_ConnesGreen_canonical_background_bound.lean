-- Prove2me | solution 1 for ConnesGreen.canonical_background_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T06:30:09.186133+00:00
-- url     : https://prove2.me/submissions/610f9199-af5f-4117-8627-43ca0287afc0

import Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
private theorem weighted_pairing (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) (ρ : CriticalZeros) :
    ⟪weightedGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ =
      (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) * mellinHat g ρ.1 := by
  simp only [weightedGreenColumn, inner_smul_left, RCLike.conj_ofReal, smul_eq_mul]
  rw [canonical_source_pairing_mellin T hT g hg ρ]
  simp
private theorem weighted_energy (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) (ρ : CriticalZeros) :
    ‖⟪weightedGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ‖ ^ 2 =
      (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2 := by
  rw [weighted_pairing T hT g hg ρ]
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
private theorem paired_energy (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) (ρ : CriticalZeros) :
    ‖⟪positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ‖ ^ 2 +
    ‖⟪negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ‖ ^ 2 =
      ((zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2 +
        (zeroMult (reflectedZero ρ).1 : ℝ) * ‖mellinHat g (reflectedZero ρ).1‖ ^ 2) / 2 := by
  let a := (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) * mellinHat g ρ.1
  let b := (Real.sqrt (zeroMult (reflectedZero ρ).1 : ℝ) : ℂ) * mellinHat g (reflectedZero ρ).1
  have he : ‖(a + b) / 2‖ ^ 2 + ‖(a - b) / 2‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
    simp only [norm_div, Complex.norm_ofNat, div_pow]
    nlinarith [parallelogram_law_with_norm ℂ a b]
  have hp : ⟪positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ = (a+b)/2 := by
    unfold positiveGreenColumn
    rw [inner_smul_left, inner_add_left, weighted_pairing T hT g hg ρ, weighted_pairing T hT g hg (reflectedZero ρ)]
    simp [a,b,smul_eq_mul,div_eq_mul_inv,mul_comm,map_ofNat]
  have hn : ⟪negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ = (a-b)/2 := by
    unfold negativeGreenColumn
    rw [inner_smul_left, inner_sub_left, weighted_pairing T hT g hg ρ, weighted_pairing T hT g hg (reflectedZero ρ)]
    simp [a,b,smul_eq_mul,div_eq_mul_inv,mul_comm,map_ofNat]
  rw [hp,hn,he]
  simp only [a,b,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hS : ∀ ρ ∈ S, reflectedZero ρ ∈ S) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
      ∑' ρ : CriticalZeros, if ρ ∈ S then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2 := by
  classical
  let x := sourceEmbed t (problemOneL g)
  let v := fun τ => sourceEmbed t (actualGreenSource τ)
  let P := fun ρ => ‖⟪positiveGreenColumn v ρ,x⟫_ℂ‖ ^ 2
  let N := fun ρ => ‖⟪negativeGreenColumn v ρ,x⟫_ℂ‖ ^ 2
  let C := fun ρ : CriticalZeros => (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2
  have hs (w : CriticalZeros → Physical t) (hw : Summable (fun ρ => ‖w ρ‖ ^ 2)) : Summable (fun ρ => ‖⟪w ρ,x⟫_ℂ‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ρ => ?_) (hw.mul_right (‖x‖ ^ 2))
    exact (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (w ρ) x) 2)
  have hP : Summable P := hs _ (canonical_actor_columns_summable t ht).1
  have hN : Summable N := hs _ (canonical_actor_columns_summable t ht).2
  have hC : Summable C := by
    apply Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (fun ρ => ?_) ((hP.add hN).mul_left 2)
    have he := paired_energy t ht g hg ρ
    change C ρ ≤ 2 * (P ρ + N ρ)
    have hr : 0 ≤ C (reflectedZero ρ) := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    change P ρ + N ρ = (C ρ + C (reflectedZero ρ)) / 2 at he
    linarith
  let e : CriticalZeros → ℝ := fun ρ => if ρ ∈ S then 0 else C ρ
  have he : Summable e := Summable.of_nonneg_of_le
    (fun ρ => by dsimp [e]; split_ifs <;> positivity)
    (fun ρ => by dsimp [e]; split_ifs; exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _); exact le_rfl) hC
  let R : CriticalZeros ≃ CriticalZeros :=
    ⟨reflectedZero, reflectedZero, reflectedZero_involutive, reflectedZero_involutive⟩
  have her : Summable (fun ρ => e (reflectedZero ρ)) := he.comp_injective R.injective
  have hmem (ρ : CriticalZeros) : reflectedZero ρ ∈ S ↔ ρ ∈ S := by
    constructor
    · intro h; simpa using hS (reflectedZero ρ) h
    · exact hS ρ
  have hboth : (fun ρ : CriticalZeros => if ρ ∈ S then 0 else P ρ + N ρ) =
      fun ρ => (e ρ + e (reflectedZero ρ)) / 2 := by
    funext ρ
    by_cases hρ : ρ ∈ S
    · simp [e,hρ,(hmem ρ).mpr hρ]
    · have hr : reflectedZero ρ ∉ S := fun h => hρ ((hmem ρ).mp h)
      simpa only [e,if_neg hρ,if_neg hr] using paired_energy t ht g hg ρ
  have hsum : Summable (fun ρ : CriticalZeros => if ρ ∈ S then 0 else P ρ + N ρ) := by
    rw [hboth]; exact (he.add her).div_const 2
  have heq : (∑' ρ : CriticalZeros, if ρ ∈ S then 0 else P ρ + N ρ) = ∑' ρ, e ρ := by
    rw [hboth,tsum_div_const,Summable.tsum_add he her]
    have hr : (∑' ρ, e (reflectedZero ρ)) = ∑' ρ, e ρ := R.tsum_eq e
    rw [hr]
    ring
  have hn : Summable (fun ρ : CriticalZeros => if ρ ∈ S then 0 else N ρ) :=
    Summable.of_nonneg_of_le (fun ρ => by split_ifs; exact le_rfl; exact sq_nonneg _)
      (fun ρ => by split_ifs <;> simp [P,N]) hsum
  have hle : (∑' ρ : CriticalZeros, if ρ ∈ S then 0 else N ρ) ≤ ∑' ρ, e ρ := by
    rw [← heq]
    exact hn.tsum_le_tsum (fun ρ => by split_ifs <;> simp [P,N]) hsum
  rw [canonicalBackgroundSynthesis,columnSynthesis_adjoint_norm_sq]
  change (∑' ρ : {ρ : CriticalZeros // ρ ∉ S}, N ρ.1) ≤ _
  change (∑' ρ : {ρ : CriticalZeros | ρ ∉ S}, N ρ.1) ≤ _
  rw [tsum_subtype {ρ : CriticalZeros | ρ ∉ S}]
  have hi : ({ρ : CriticalZeros | ρ ∉ S} : Set CriticalZeros).indicator N =
      fun ρ => if ρ ∈ S then 0 else N ρ := by
    funext ρ
    by_cases h : ρ ∈ S <;> simp [Set.indicator,h]
  rw [hi]
  exact hle
