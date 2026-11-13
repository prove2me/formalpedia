-- Prove2me | solution 1 for CountingLLL.RandomRAM.reciprocal_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:54:31.9431+00:00
-- url     : https://prove2.me/submissions/b3298a97-8149-4a34-93ef-9ba3e35baf49

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_stopping
import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_prefix_cross_moments
import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_cross_series

set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Reindex the upper triangle and strict lower triangle of the natural-number lattice. -/
private def triangleEquiv : ((ℕ × ℕ) ⊕ (ℕ × ℕ)) ≃ (ℕ × ℕ) where
  toFun x := match x with
    | .inl (i,d) => (i, i+d)
    | .inr (i,d) => (i+d+1, i)
  invFun x := if x.1 ≤ x.2 then .inl (x.1,x.2-x.1) else .inr (x.2,x.1-x.2-1)
  left_inv := by
    rintro (⟨i,d⟩ | ⟨i,d⟩)
    · simp
    · simp only [not_le_of_gt (show i < i+d+1 by omega), ↓reduceIte, Sum.inr.injEq, Prod.mk.injEq]
      constructor
      · trivial
      · omega
  right_inv := by
    rintro ⟨i,j⟩
    by_cases h : i ≤ j
    · simp only [h, ↓reduceIte]
      congr 1 <;> omega
    · simp only [h, ↓reduceIte]
      congr 1 <;> omega

/-- Square of an absolutely summable series as twice the upper triangle minus its diagonal. -/
private theorem triangle_tsum_identity (f : ℕ → ℝ) (hf : Summable fun i => ‖f i‖) :
    (∑' i, f i) ^ 2 =
      2 * (∑' p : ℕ × ℕ, f p.1 * f (p.1 + p.2)) - ∑' i, (f i)^2 := by
  let F : ℕ × ℕ → ℝ := fun p => f p.1 * f p.2
  let U : ℕ × ℕ → ℝ := fun p => f p.1 * f (p.1+p.2)
  let V : ℕ × ℕ → ℝ := fun p => f p.1 * f (p.1+(p.2+1))
  let D : ℕ → ℝ := fun i => (f i)^2
  have hF : Summable F := summable_mul_of_summable_norm hf hf
  have hU : Summable U := by
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1,p.1+p.2)) := by
      rintro ⟨a,b⟩ ⟨c,d⟩ h
      simp only [Prod.mk.injEq] at h
      congr 1 <;> omega
    exact hF.comp_injective hinj
  have hV : Summable V := by
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1,p.2+1)) := by
      rintro ⟨a,b⟩ ⟨c,d⟩ h
      simp only [Prod.mk.injEq] at h
      congr 1 <;> omega
    change Summable (fun p : ℕ × ℕ => U (p.1, p.2+1))
    exact hU.comp_injective hinj
  have hD : Summable D := by
    have hinj : Function.Injective (fun i : ℕ => (i,i)) := by
      intro a b h
      exact congrArg Prod.fst h
    have h := hF.comp_injective hinj
    change Summable (fun i : ℕ => f i * f i) at h
    change Summable (fun i : ℕ => f i ^ 2)
    simpa only [pow_two] using h
  have hsplit : (∑' p, F p) = (∑' p, U p) + (∑' p, V p) := by
    have heq := triangleEquiv.tsum_eq F
    have hl : Summable (fun x : ℕ × ℕ => F (triangleEquiv (Sum.inl x))) := by simpa [F,U,triangleEquiv] using hU
    have hr : Summable (fun x : ℕ × ℕ => F (triangleEquiv (Sum.inr x))) := by
      simpa [F,V,triangleEquiv, mul_comm, Nat.add_assoc] using hV
    rw [Summable.tsum_sum hl hr] at heq
    simpa [F,U,V,triangleEquiv,mul_comm,Nat.add_assoc] using heq.symm
  have hrows : ∀ i, (∑' d, U (i,d)) = D i + ∑' d, V (i,d) := by
    intro i
    have hs := (hU.prod_factor i).sum_add_tsum_nat_add 1
    simpa [U,V,D,pow_two,Nat.add_assoc] using hs.symm
  have hrowSum : (∑' p, U p) = (∑' i, D i) + (∑' p, V p) := by
    rw [hU.tsum_prod, hV.tsum_prod]
    simp_rw [hrows]
    exact (hD.tsum_add hV.prod)
  have hsquare : (∑' i, f i) ^ 2 = ∑' p, F p := by
    simpa [F,pow_two] using tsum_mul_tsum_of_summable_norm hf hf
  rw [hsquare, hsplit]
  linarith


theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) (hτ : ν {x | x ≠ 0} < 1) :
    let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
    let r : ℝ := ∫ x, x ∂ν
    let M : ℝ := ∫ x, x ^ 2 ∂ν
    let W : (ℕ → ℝ) → ℝ := fun ω => ∑' n : ℕ, ∏ k ∈ Finset.range n, ω k
    Integrable (fun ω => (W ω) ^ 2) μ ∧
    (∫ ω, (W ω) ^ 2 ∂μ) = (1 + r) / ((1 - r) * (1 - M)) := by
  dsimp only
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  let r : ℝ := ∫ x, x ∂ν
  let M : ℝ := ∫ x, x ^ 2 ∂ν
  let P : ℕ → (ℕ → ℝ) → ℝ := fun n ω => ∏ k ∈ Finset.range n, ω k
  let W : (ℕ → ℝ) → ℝ := fun ω => ∑' n, P n ω
  let C : (ℕ × ℕ) → (ℕ → ℝ) → ℝ := fun ij ω => P ij.1 ω * P (ij.1+ij.2) ω
  let T : (ℕ → ℝ) → ℝ := fun ω => ∑' ij, C ij ω
  let D : (ℕ → ℝ) → ℝ := fun ω => ∑' i, (P i ω)^2
  have hM0 : 0 ≤ M := integral_nonneg (fun x => sq_nonneg x)
  have hseries := CountingLLL.RandomRAM.reciprocal_cross_series ν hν hr0 hr1 hM
  have hCint : ∀ ij, Integrable (C ij) μ := fun ij =>
    (CountingLLL.RandomRAM.reciprocal_prefix_cross_moments ν hν ij.1 ij.2).1
  have hCnorm : Summable (fun ij => ∫ ω, ‖C ij ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs] using hseries.1
  have hTmean : (∫ ω, T ω ∂μ) = (1-M)⁻¹ * (1-r)⁻¹ := by
    rw [show T = fun ω => ∑' ij, C ij ω from rfl,
      ← integral_tsum_of_summable_integral_norm hCint hCnorm]
    exact hseries.2.2.2.1
  have hTpos : 0 < (1-M)⁻¹ * (1-r)⁻¹ :=
    mul_pos (inv_pos.mpr (by linarith)) (inv_pos.mpr (by linarith))
  have hTint : Integrable T μ := by
    by_contra hnot
    have hzero := integral_undef hnot
    linarith
  have hDint : ∀ i, Integrable (fun ω => (P i ω)^2) μ := by
    intro i
    have h := (CountingLLL.RandomRAM.reciprocal_prefix_cross_moments ν hν i 0).1
    simpa [C,P,pow_two] using h
  have hDterm : ∀ i, (∫ ω, (P i ω)^2 ∂μ) = M ^ i := by
    intro i
    have h := (CountingLLL.RandomRAM.reciprocal_prefix_cross_moments ν hν i 0).2.1
    simpa [P,M,pow_two] using h
  have hDnorm : Summable (fun i => ∫ ω, ‖(P i ω)^2‖ ∂μ) := by
    have heq : (fun i => ∫ ω, ‖(P i ω)^2‖ ∂μ) = (fun i => M^i) := by
      funext i
      have heq : (fun ω => ‖(P i ω)^2‖) = (fun ω => (P i ω)^2) := by
        funext ω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (P i ω))]
      rw [heq]
      exact hDterm i
    rw [heq]
    exact summable_geometric_of_lt_one hM0 hM
  have hDmean : (∫ ω, D ω ∂μ) = (1-M)⁻¹ := by
    rw [show D = fun ω => ∑' i, (P i ω)^2 from rfl,
      ← integral_tsum_of_summable_integral_norm hDint hDnorm]
    simp_rw [hDterm]
    exact tsum_geometric_of_lt_one hM0 hM
  have hDpos : 0 < (1-M)⁻¹ := inv_pos.mpr (by linarith)
  have hDintegrable : Integrable D μ := by
    by_contra hnot
    have hzero := integral_undef hnot
    linarith
  have hzeroAE : ∀ᵐ ω ∂μ, ∃ n, ω n = 0 :=
    (CountingLLL.RandomRAM.reciprocal_stopping ν).2.1 hτ
  have heq : (fun ω => (W ω)^2) =ᵐ[μ] (fun ω => 2*T ω - D ω) := by
    filter_upwards [hzeroAE] with ω hω
    obtain ⟨k, hk⟩ := hω
    have hsum : Summable (fun n => ‖P n ω‖) := by
      apply summable_of_ne_finset_zero (s := Finset.range (k+1))
      intro n hn
      have hkn : k < n := by simpa using hn
      have hz : P n ω = 0 := by
        unfold P
        exact Finset.prod_eq_zero (Finset.mem_range.mpr hkn) hk
      simp [hz]
    exact triangle_tsum_identity (fun n => P n ω) hsum
  constructor
  · exact ((hTint.const_mul 2).sub hDintegrable).congr heq.symm
  · rw [integral_congr_ae heq, integral_sub (hTint.const_mul 2) hDintegrable,
      integral_const_mul, hTmean, hDmean]
    have hfinal := hseries.2.2.2.2
    rw [hseries.2.2.2.1] at hfinal
    exact hfinal
