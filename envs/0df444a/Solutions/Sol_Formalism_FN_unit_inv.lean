-- Prove2me | solution 1 for Formalism.FN.unit_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:18.7829+00:00
-- url     : https://prove2.me/submissions/deab9868-3370-4619-8fe1-82269d7fb146

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit
import Theorems.Thm_Formalism_FN_unit_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FN
open Filter Topology
namespace Formalism.FN
theorem _root_.solution {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r) (hb : b ≠ 0) (hw : wdeg b r = 0) :
    ∃ u : ℕ → K, ConvOn u r ∧ cmul b u = fun n => if n = 0 then 1 else 0 := by
  obtain ⟨h0, hM, ε, hε0, hε1, hε⟩ := unit_eps b r hr hc hb hw
  have hb0 : b 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at h0; linarith
  set M := gNorm b r with hMdef
  set B : PowerSeries K := PowerSeries.mk b with hB
  set u : ℕ → K := fun n => PowerSeries.coeff n B⁻¹ with hu
  have hmul : cmul b u = fun n => if n = 0 then 1 else 0 := by
    funext n
    have h := congrArg (PowerSeries.coeff n)
      (PowerSeries.mul_inv_cancel B (by rw [hB, PowerSeries.constantCoeff_mk]; exact hb0))
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i B * PowerSeries.coeff j B⁻¹)] at h
    simpa [cmul, u, B, PowerSeries.coeff_mk] using h
  refine ⟨u, ?_, hmul⟩

  have key : ∀ n, 1 ≤ n → ∀ C : ℝ, 0 ≤ C →
      (∀ i < n, (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) ≤ C) →
      M * (‖u n‖ * r ^ n) ≤ C := by
    intro n hn C hC h
    have hrec : b 0 * u n = -∑ i ∈ Finset.range n, b (i + 1) * u (n - (i + 1)) := by
      have e := congrFun hmul n
      simp only [cmul, if_neg (show n ≠ 0 by omega)] at e
      rw [Finset.sum_range_succ', Nat.sub_zero] at e
      linear_combination e
    have hrn : 0 < r ^ n := pow_pos hr n
    have hs : ‖∑ i ∈ Finset.range n, b (i + 1) * u (n - (i + 1))‖ ≤ C / r ^ n := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hC hrn.le)
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [le_div_iff₀ hrn, norm_mul]
      have e : r ^ n = r ^ (i + 1) * r ^ (n - (i + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      calc ‖b (i + 1)‖ * ‖u (n - (i + 1))‖ * (r ^ (i + 1) * r ^ (n - (i + 1)))
          = (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) := by ring
        _ ≤ C := h i hi'
    have h3 : M * ‖u n‖ ≤ C / r ^ n := by
      rw [← h0, ← norm_mul, hrec, norm_neg]; exact hs
    rw [le_div_iff₀ hrn] at h3
    calc M * (‖u n‖ * r ^ n) = M * ‖u n‖ * r ^ n := by ring
      _ ≤ C := h3
  have hu0 : M * (‖u 0‖ * r ^ 0) = 1 := by
    have e : b 0 * u 0 = 1 := by simpa [cmul] using congrFun hmul 0
    rw [pow_zero, mul_one, ← h0, ← norm_mul, e, norm_one]

  have decay : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ k0 : ℕ, 1 ≤ k0 →
      (∀ k, k0 ≤ k → ‖b k‖ * r ^ k ≤ δ * M) →
      ∀ n, M * (‖u n‖ * r ^ n) ≤ max δ (ε ^ (n / k0)) := by
    intro δ hδ0 hδ1 k0 hk0 hbk n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hu0]; simp
    apply key n hn _ (le_max_of_le_left hδ0)
    intro i hi
    have hv : 0 ≤ ‖u (n - (i + 1))‖ * r ^ (n - (i + 1)) := by positivity
    have hIH := ih (n - (i + 1)) (by omega)
    by_cases hik : k0 ≤ i + 1
    · have hX1 : max δ (ε ^ ((n - (i + 1)) / k0)) ≤ 1 :=
        max_le hδ1 (pow_le_one₀ hε0 hε1.le)
      calc (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))
          ≤ (δ * M) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) :=
            mul_le_mul_of_nonneg_right (hbk _ hik) hv
        _ = δ * (M * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (hIH.trans hX1) hδ0
        _ = δ := mul_one _
        _ ≤ _ := le_max_left _ _
    · have hm : n / k0 ≤ (n - (i + 1)) / k0 + 1 := by
        rw [← Nat.add_div_right _ (by omega : 0 < k0)]
        exact Nat.div_le_div_right (by omega)
      calc (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))
          ≤ (ε * M) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) :=
            mul_le_mul_of_nonneg_right (hε _ (by omega)) hv
        _ = ε * (M * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))) := by ring
        _ ≤ ε * max δ (ε ^ ((n - (i + 1)) / k0)) := mul_le_mul_of_nonneg_left hIH hε0
        _ = max (ε * δ) (ε ^ ((n - (i + 1)) / k0 + 1)) := by
            rw [mul_max_of_nonneg _ _ hε0, pow_succ']
        _ ≤ max δ (ε ^ (n / k0)) :=
            max_le_max (mul_le_of_le_one_left hδ0 hε1.le) (pow_le_pow_of_le_one hε0 hε1.le hm)

  show Tendsto (fun k : ℕ => ‖u k‖ * r ^ k) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro η hη
  have hηM : 0 < η * M / 2 := by positivity
  set δ := min 1 (η * M / 2) with hδ
  have hδ0 : 0 < δ := lt_min one_pos hηM
  obtain ⟨K1, hK1⟩ := eventually_atTop.1
    ((hc : Tendsto (fun k : ℕ => ‖b k‖ * r ^ k) atTop (𝓝 0)).eventually
      (gt_mem_nhds (mul_pos hδ0 hM)))
  set k0 := max K1 1 with hk0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hηM hε1
  refine ⟨m * k0, fun n hn => ?_⟩
  have hD := decay δ hδ0.le (min_le_left _ _) k0 (le_max_right _ _)
    (fun k hk => (hK1 k (le_trans (le_max_left _ _) hk)).le) n
  have hmn : m ≤ n / k0 := (Nat.le_div_iff_mul_le (by omega)).2 hn
  have hpow : ε ^ (n / k0) ≤ ε ^ m := pow_le_pow_of_le_one hε0 hε1.le hmn
  have hv : 0 ≤ ‖u n‖ * r ^ n := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hv]
  have hbound : M * (‖u n‖ * r ^ n) < η * M := by
    calc M * (‖u n‖ * r ^ n) ≤ max δ (ε ^ (n / k0)) := hD
      _ ≤ max (η * M / 2) (ε ^ m) := max_le_max (min_le_right _ _) hpow
      _ < η * M := max_lt (by linarith) (by linarith)
  nlinarith
end Formalism.FN
