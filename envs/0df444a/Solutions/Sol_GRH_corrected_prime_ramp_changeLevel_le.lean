-- Prove2me | solution 1 for GRH.corrected_prime_ramp_changeLevel_le
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:45:07.018315+00:00
-- url     : https://prove2.me/submissions/402c05ac-dcc9-4c14-95db-6fa519ed3d16

import Mathlib

/-!
# Transfer of the corrected prime ramp under change of modulus

The coefficient difference is supported on powers of primes dividing the new
modulus. Its Dirichlet series converges absolutely in every right half-plane of
positive width, including at one. This identifies the change in the correction
term and leaves the bounded arithmetic weight `min 1 (y/n)`.
-/

noncomputable section

open ArithmeticFunction Complex Filter Finset Set Topology
open scoped Classical

namespace MasulloRampTransfer

private def coefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q) * (vonMangoldt n:ℂ)

private def difference {d q : ℕ} (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d) (n : ℕ) : ℂ :=
  coefficients (DirichletCharacter.changeLevel hdq ψ) n - coefficients ψ n

private theorem difference_zero_at_zero {d q : ℕ} (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d) :
    difference hdq ψ 0 = 0 := by
  simp [difference,coefficients]

private def primePowerEnvelope (p : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Set.range (p ^ · : ℕ → ℕ) then (n:ℝ)^(-α) else 0

private theorem primePowerEnvelope_nonneg (p : ℕ) (α : ℝ) (n : ℕ) :
    0 ≤ primePowerEnvelope p α n := by
  unfold primePowerEnvelope
  split_ifs <;> positivity

private theorem summable_primePowerEnvelope {p : ℕ} (hp : p.Prime) {α : ℝ} (hα : 0 < α) :
    Summable (primePowerEnvelope p α) := by
  classical
  have hOne : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  apply ((pow_right_injective₀ hp.pos hp.ne_one).summable_iff (f := primePowerEnvelope p α)
    (fun n hn => if_neg hn)).mp
  have hs : Summable (fun k : ℕ => ((p:ℝ)^(-α))^k) :=
    summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg hOne (by linarith))
  convert hs using 1
  funext k
  simp only [Function.comp_apply,primePowerEnvelope,Set.mem_range_self,if_true,Nat.cast_pow]
  rw [← Real.rpow_natCast_mul (by positivity),mul_comm,Real.rpow_mul (by positivity),
    Real.rpow_natCast]

private def modulusEnvelope (q : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ q.primeFactors, Real.log (p:ℝ) * primePowerEnvelope p α n

private theorem modulusEnvelope_nonneg (q : ℕ) (α : ℝ) (n : ℕ) :
    0 ≤ modulusEnvelope q α n :=
  Finset.sum_nonneg fun p _ => mul_nonneg (Real.log_natCast_nonneg p) (primePowerEnvelope_nonneg _ _ _)

private theorem summable_modulusEnvelope (q : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (modulusEnvelope q α) :=
  summable_sum (s := q.primeFactors) fun p hp =>
    (summable_primePowerEnvelope (Nat.prime_of_mem_primeFactors hp) hα).mul_left _

private theorem norm_difference_weight_le {d q : ℕ} [NeZero q] (hdq : d ∣ q)
    (ψ : DirichletCharacter ℂ d) (α : ℝ) (n : ℕ) :
    ‖difference hdq ψ n‖ * (n:ℝ)^(-α) ≤
      modulusEnvelope q α n := by
  classical
  have hnSum := modulusEnvelope_nonneg q α n
  by_cases hpp : IsPrimePow n
  · obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    by_cases hq : p ∣ q
    · have hpq : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hq,NeZero.ne _⟩
      have hNu : ¬ IsUnit ((p^k:ℕ) : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime,Nat.coprime_pow_left_iff hk,hp.coprime_iff_not_dvd]
        exact not_not_intro hq
      have hD : ‖difference hdq ψ (p^k)‖ ≤ Real.log (p:ℝ) := by
        rw [difference,coefficients, (DirichletCharacter.changeLevel hdq ψ).map_nonunit hNu,
          zero_mul,zero_sub,norm_neg,coefficients,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,vonMangoldt_apply_pow hk.ne',vonMangoldt_apply_prime hp,
          abs_of_nonneg (Real.log_natCast_nonneg p)]
        exact mul_le_of_le_one_left (Real.log_natCast_nonneg p) (ψ.norm_le_one _)
      have hTerm : ‖difference hdq ψ (p^k)‖ * ((p^k:ℕ):ℝ)^(-α) ≤
          Real.log (p:ℝ) * primePowerEnvelope p α (p^k) := by
        simpa only [primePowerEnvelope,Set.mem_range_self,if_true] using
          mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg (by positivity) (-α))
      exact hTerm.trans (Finset.single_le_sum (f := fun l : ℕ => Real.log (l:ℝ) * primePowerEnvelope l α (p^k))
        (fun l _ => mul_nonneg (Real.log_natCast_nonneg l) (primePowerEnvelope_nonneg _ _ _)) hpq)
    · have hC : (p^k).Coprime q := (Nat.coprime_pow_left_iff hk _ _).mpr
        (hp.coprime_iff_not_dvd.mpr hq)
      let u := ZMod.unitOfCoprime (p^k) hC
      have hu : (↑u : ZMod q) = (↑(p^k:ℕ) : ZMod q) := ZMod.coe_unitOfCoprime _ _
      have hEq : (DirichletCharacter.changeLevel hdq ψ) ((p^k:ℕ):ZMod q) =
          ψ ((p^k:ℕ):ZMod d) := by
        rw [← hu,ψ.changeLevel_eq_cast_of_dvd hdq u,hu,ZMod.cast_natCast hdq]
      simpa only [difference,coefficients,hEq,sub_self,norm_zero,zero_mul] using hnSum
  · have hΛ := vonMangoldt_eq_zero_iff.mpr hpp
    simpa only [difference,coefficients,hΛ,Complex.ofReal_zero,mul_zero,sub_self,norm_zero,zero_mul] using hnSum

private theorem summable_difference_weight {d q : ℕ} [NeZero q] (hdq : d ∣ q)
    (ψ : DirichletCharacter ℂ d) {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => ‖difference hdq ψ n‖ * (n:ℝ)^(-α)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (norm_difference_weight_le hdq ψ α) ?_
  exact summable_modulusEnvelope q hα

private def logDerivative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  deriv χ.LFunction s / χ.LFunction s

private theorem logDerivative_continuousAt_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : ContinuousAt (logDerivative χ) 1 := by
  have h := (χ.differentiableAt_LFunction 1 (.inr hχ))
  have hDiff : Differentiable ℂ χ.LFunction := fun s => χ.differentiableAt_LFunction s (.inr hχ)
  have hA : AnalyticAt ℂ χ.LFunction 1 := hDiff.analyticAt _
  exact hA.deriv.continuousAt.div h.continuousAt
    (χ.LFunction_ne_zero_of_re_eq_one Complex.one_re (.inl hχ))

private theorem LSeries_difference_eq {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d) {s : ℂ} (hs : 1 < s.re) :
    LSeries (difference hdq ψ) s =
      -(logDerivative (DirichletCharacter.changeLevel hdq ψ) s-logDerivative ψ s) := by
  let χ := DirichletCharacter.changeLevel hdq ψ
  have hSum (a : ℕ) [NeZero a] (φ : DirichletCharacter ℂ a) :
      LSeriesSummable (coefficients φ) s := φ.LSeriesSummable_twist_vonMangoldt hs
  have hEq (a : ℕ) [NeZero a] (φ : DirichletCharacter ℂ a) :
      LSeries (coefficients φ) s = -(logDerivative φ s) := by
    rw [logDerivative,φ.deriv_LFunction_eq_deriv_LSeries hs,φ.LFunction_eq_LSeries hs,← neg_div]
    exact φ.LSeries_twist_vonMangoldt_eq hs
  change LSeries (coefficients χ - coefficients ψ) s = _
  unfold LSeries
  rw [LSeries.term_sub]
  simp only [Pi.sub_apply]
  rw [(hSum q χ).tsum_sub (hSum d ψ)]
  change LSeries (coefficients χ) s - LSeries (coefficients ψ) s = _
  rw [hEq q χ,hEq d ψ]
  ring

private theorem logDerivative_difference_at_one {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d) (hψ : ψ ≠ 1) :
    logDerivative (DirichletCharacter.changeLevel hdq ψ) 1 - logDerivative ψ 1 =
      -(∑' n : ℕ, difference hdq ψ n/(n:ℂ)) := by
  let χ := DirichletCharacter.changeLevel hdq ψ
  let v := difference hdq ψ
  have hχ : χ ≠ 1 := fun h => hψ ((DirichletCharacter.changeLevel_eq_one_iff hdq).mp h)
  have hCont : ContinuousAt (fun x : ℝ => -(logDerivative χ (x:ℂ)-logDerivative ψ (x:ℂ))) 1 := by
    have h := ((logDerivative_continuousAt_one χ hχ).sub (logDerivative_continuousAt_one ψ hψ)).neg
    exact h.comp_of_eq Complex.continuous_ofReal.continuousAt Complex.ofReal_one
  have hL : Tendsto (fun x : ℝ => LSeries v (x:ℂ)) (𝓝[>] (1:ℝ))
      (𝓝 (∑' n : ℕ, v n/(n:ℂ))) := by
    apply tendsto_tsum_of_dominated_convergence
      (summable_difference_weight hdq ψ (show 0 < (1:ℝ) by norm_num))
    · intro n
      by_cases hn : n = 0
      · subst hn
        simp [LSeries.term]
      · have hPower : Continuous (fun x : ℝ => (n:ℂ)^(x:ℂ)) :=
          Complex.continuous_ofReal.const_cpow (.inl (by exact_mod_cast hn))
        have hQ := (continuousAt_const (y := v n)).div hPower.continuousAt
          (show (n:ℂ)^(↑(1:ℝ):ℂ) ≠ 0 by simpa only [Complex.ofReal_one,Complex.cpow_one] using
            (show (n:ℂ) ≠ 0 by exact_mod_cast hn))
        rw [show (fun x : ℝ => LSeries.term v (x:ℂ) n) = (fun x : ℝ => v n / (n:ℂ)^(x:ℂ)) from
          funext (fun x => LSeries.term_of_ne_zero hn _ _)]
        have ht := hQ.tendsto
        change Tendsto (fun x : ℝ => v n / (n:ℂ)^(x:ℂ)) (𝓝 (1:ℝ))
          (𝓝 (v n/(n:ℂ)^((1:ℝ):ℂ))) at ht
        rw [Complex.ofReal_one,Complex.cpow_one] at ht
        exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      by_cases hn : n = 0
      · simp [hn,LSeries.term]
      · rw [LSeries.term_of_ne_zero hn,norm_div,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
          Complex.ofReal_re,div_eq_mul_inv,← Real.rpow_neg (by positivity)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast Nat.pos_of_ne_zero hn) (neg_le_neg (le_of_lt hx))) (norm_nonneg _)
  have hEq : (fun x : ℝ => LSeries v (x:ℂ)) =ᶠ[𝓝[>] (1:ℝ)]
      (fun x : ℝ => -(logDerivative χ (x:ℂ)-logDerivative ψ (x:ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact LSeries_difference_eq hdq ψ (by simpa only [Complex.ofReal_re] using (show 1 < x from hx))
  have h := tendsto_nhds_unique hL ((hCont.mono_left nhdsWithin_le_nhds).congr' hEq.symm)
  change (∑' n : ℕ, v n/(n:ℂ)) = -(logDerivative χ 1-logDerivative ψ 1) at h
  exact neg_eq_iff_eq_neg.mp h.symm

private def complexRamp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ range (⌊y⌋₊+1), coefficients χ n * ((max (y/(n:ℝ)-1) 0:ℝ):ℂ)) +
    (y:ℂ) * logDerivative χ 1

private theorem complexRamp_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) :
    (complexRamp χ y).re =
      (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
          y * (deriv χ.LFunction 1 / χ.LFunction 1).re := by
  simp only [complexRamp,logDerivative,Complex.add_re,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  simp [coefficients,mul_comm]

private theorem min_one_le_rpow {x θ : ℝ} (hx : 0 < x) (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    min 1 x ≤ x^θ := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    calc x = x^(1:ℝ) := (Real.rpow_one x).symm
         _ ≤ x^θ := Real.rpow_le_rpow_of_exponent_ge hx h hθ₁
  · rw [min_eq_left h]
    exact Real.one_le_rpow h hθ

private theorem ramp_diff_eq_tsum {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d) (hψ : ψ ≠ 1) (y : ℝ) :
    complexRamp (DirichletCharacter.changeLevel hdq ψ) y - complexRamp ψ y =
      -(∑' n : ℕ, difference hdq ψ n * ((min 1 (y/(n:ℝ)):ℝ):ℂ)) := by
  let v := difference hdq ψ
  let u : ℕ → ℂ := fun n => v n * ((max (y/(n:ℝ)-1) 0:ℝ):ℂ)
  let b : ℕ → ℂ := fun n => v n / (n:ℂ)
  let c : ℕ → ℂ := fun n => v n * ((min 1 (y/(n:ℝ)):ℝ):ℂ)
  let F := range (⌊y⌋₊+1)
  have hu (n : ℕ) (hn : n ∉ F) : u n = 0 := by
    have hn' : ⌊y⌋₊ < n := by simp [F] at hn; omega
    have hn₀ : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn')
    have hnY : y < n := (Nat.lt_floor_add_one y).trans_le (by exact_mod_cast (Nat.succ_le_of_lt hn'))
    have hm : max (y/(n:ℝ)-1) 0 = 0 := max_eq_right (sub_nonpos.mpr
      ((div_le_one hn₀).mpr hnY.le))
    simp only [u,hm,Complex.ofReal_zero,mul_zero]
  have hBD (n : ℕ) : ‖b n‖ = ‖v n‖ * (n:ℝ)^(-(1:ℝ)) := by
    rw [norm_div,Complex.norm_natCast,Real.rpow_neg_one,div_eq_mul_inv]
  have hb : Summable b := by
    apply Summable.of_norm
    simpa only [hBD,v] using summable_difference_weight hdq ψ (show 0 < (1:ℝ) by norm_num)
  have hU : Summable u := (hasSum_sum_of_ne_finset_zero hu).summable
  have hUV (n : ℕ) : u n - (y:ℂ)*b n = -c n := by
    by_cases hz : n = 0
    · subst n
      simp [u,b,c,v,difference_zero_at_zero]
    · let x := y/(n:ℝ)
      have ha : max (x-1) 0 - x = -min 1 x := by
        rcases le_total x 1 with h | h
        · rw [max_eq_right (sub_nonpos.mpr h),min_eq_right h,zero_sub]
        · rw [max_eq_left (sub_nonneg.mpr h),min_eq_left h]
          ring
      have hf := congrArg Complex.ofReal ha
      simp only [x,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_neg] at hf
      simp only [u,b,c,div_eq_mul_inv] at *
      linear_combination v n * hf
  have hFirst : complexRamp (DirichletCharacter.changeLevel hdq ψ) y - complexRamp ψ y =
      (∑ n ∈ F,u n) - (y:ℂ)*(∑' n,b n) := by
    dsimp [complexRamp]
    have hF : (∑ n ∈ F, coefficients (DirichletCharacter.changeLevel hdq ψ) n *
          ((max (y/(n:ℝ)-1) 0:ℝ):ℂ)) -
        (∑ n ∈ F, coefficients ψ n * ((max (y/(n:ℝ)-1) 0:ℝ):ℂ)) = ∑ n ∈ F,u n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      simp only [u,v,difference,sub_mul]
    have hLS := logDerivative_difference_at_one hdq ψ hψ
    change logDerivative (DirichletCharacter.changeLevel hdq ψ) 1 - logDerivative ψ 1 = -(∑' n,b n) at hLS
    change _ = _ at hF
    dsimp only [F] at hF ⊢
    linear_combination hF + (y:ℂ)*hLS
  rw [hFirst,← (hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hu).tsum_eq,← hb.tsum_mul_left,← hU.tsum_sub (hb.mul_left _)]
  simp_rw [hUV]
  exact tsum_neg

private theorem complex_ramp_changeLevel_bound (q : ℕ) [NeZero q]
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) [NeZero d] (hdq : d ∣ q)
      (ψ : DirichletCharacter ℂ d), ψ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
      ‖complexRamp (DirichletCharacter.changeLevel hdq ψ) y - complexRamp ψ y‖ ≤ C*y^θ := by
  let w := modulusEnvelope q θ
  have hw : Summable w := summable_modulusEnvelope q hθ
  refine ⟨∑' n,w n,tsum_nonneg (modulusEnvelope_nonneg q θ),?_⟩
  intro d id hdq ψ hψ y hy
  let c : ℕ → ℂ := fun n => difference hdq ψ n * ((min 1 (y/(n:ℝ)):ℝ):ℂ)
  have hc (n : ℕ) : ‖c n‖ ≤ w n * y^θ := by
    by_cases hz : n = 0
    · subst n
      simpa only [c,difference_zero_at_zero,zero_mul,norm_zero] using
        mul_nonneg (modulusEnvelope_nonneg q θ 0) (Real.rpow_nonneg (by linarith) θ)
    have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hy₀ : 0 < y := zero_lt_one.trans_le hy
    have hdiv : 0 < y/(n:ℝ) := div_pos hy₀ hn
    dsimp only [c]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_min zero_le_one hdiv.le)]
    have h := min_one_le_rpow hdiv hθ.le hθ₁
    rw [Real.div_rpow hy₀.le hn.le] at h
    have hr : y^θ/(n:ℝ)^θ = y^θ*(n:ℝ)^(-θ) := by rw [Real.rpow_neg hn.le,div_eq_mul_inv]
    rw [hr] at h
    calc
      _ ≤ ‖difference hdq ψ n‖ * (y^θ*(n:ℝ)^(-θ)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = (‖difference hdq ψ n‖ * (n:ℝ)^(-θ))*y^θ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (norm_difference_weight_le hdq ψ θ n) (by positivity)
  have hcSum : Summable (fun n => ‖c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hc (hw.mul_right _)
  rw [ramp_diff_eq_tsum hdq ψ hψ y,norm_neg]
  change ‖∑' n,c n‖ ≤ _
  exact (norm_tsum_le_tsum_norm hcSum).trans
    ((hcSum.tsum_le_tsum hc (hw.mul_right _)).trans_eq tsum_mul_right)

end MasulloRampTransfer

open MasulloRampTransfer

theorem solution (q : ℕ) [NeZero q] (θ : ℝ)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    let R := fun (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ) =>
      (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod k)).re * max (y/(n:ℝ)-1) 0) +
          y * (deriv χ.LFunction 1 / χ.LFunction 1).re
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) [NeZero d] (hdq : d ∣ q) (ψ : DirichletCharacter ℂ d),
      ψ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
        |R q (DirichletCharacter.changeLevel hdq ψ) y - R d ψ y| ≤ C*y^θ := by
  obtain ⟨C,hC,hBound⟩ := complex_ramp_changeLevel_bound q hθ hθ₁
  refine ⟨C,hC,?_⟩
  intro d id hdq ψ hψ y hy
  dsimp only
  rw [← complexRamp_re,← complexRamp_re,← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (hBound d hdq ψ hψ y hy)

#print axioms solution
