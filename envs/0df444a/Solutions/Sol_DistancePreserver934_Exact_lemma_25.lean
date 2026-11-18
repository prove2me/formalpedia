-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_25
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:22:24.792889+00:00
-- url     : https://prove2.me/submissions/2ce0b2de-13a7-4a6b-b9de-244b1dc068b5

import Theorems.Thm_DistancePreserver934_Exact_lemma_24

set_option autoImplicit false
set_option maxRecDepth 2048
open Classical DistancePreserver934.Exact

private lemma sum_batch_cost (I : Finset ℕ) (q loss : ℕ → ℝ) (n p t s A : ℝ)
    (hn : 0 ≤ n) (ht : 0 < t) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hq : ∑ i ∈ I, q i ≤ p) (hsize : ∀ i ∈ I, t ≤ q i)
    (hcost : ∀ i ∈ I, loss i ≤ A*(n+q i*s)) :
    ∑ i ∈ I, loss i ≤ A*(n*p/t+p*s) := by
  have hcount : (I.card : ℝ)*t ≤ p := by
    calc
      _ = ∑ _i ∈ I, t := by simp
      _ ≤ ∑ i ∈ I, q i := Finset.sum_le_sum hsize
      _ ≤ p := hq
  have hcnt : (I.card : ℝ) ≤ p/t := (le_div_iff₀ ht).mpr hcount
  calc
    _ ≤ ∑ i ∈ I, A*(n+q i*s) := Finset.sum_le_sum hcost
    _ = A*(n*(I.card : ℝ)+(∑ i ∈ I,q i)*s) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_mul]
      simp [nsmul_eq_mul, mul_comm]

    _ ≤ A*(n*(p/t)+p*s) := by gcongr
    _ = _ := by ring

private lemma run_subset {V : Type} [Fintype V] (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    ∀ i < τ, (st (i+1)).2 ⊆ (st i).2 := by
  intro i hi
  rcases hrun.2 i hi with ⟨hk,hs⟩ | ⟨hk,hs⟩
  · obtain ⟨hp,q,hq,hl,hR',hup⟩ := hs
    rw [hR']; exact Finset.erase_subset _ _
  · obtain ⟨hp,hl,Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := hs
    rw [hR']; exact Finset.sdiff_subset

private lemma run_removed_sum {V : Type} [Fintype V] (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    ∑ i ∈ (Finset.range τ).filter (fun i => kind i = StepKind.two),
      (((st i).2 \ (st (i+1)).2).card : ℝ) ≤ (P.card : ℝ) := by
  classical
  have hsub := run_subset c₀ c₁ c₂ G H P τ st kind hrun
  calc
    _ ≤ ∑ i ∈ Finset.range τ, (((st i).2 \ (st (i+1)).2).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = ∑ i ∈ Finset.range τ, (((st i).2.card : ℝ)-((st (i+1)).2.card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hcard := Finset.card_sdiff_add_card_eq_card (hsub i (Finset.mem_range.mp hi))
      have hcast : (((st i).2 \ (st (i+1)).2).card : ℝ)+((st (i+1)).2.card : ℝ) = ((st i).2.card : ℝ) := by exact_mod_cast hcard
      linarith
    _ = ((st 0).2.card : ℝ)-((st τ).2.card : ℝ) := Finset.sum_range_sub' _ _
    _ ≤ (P.card : ℝ) := by rw [hrun.1]; simp


private lemma power_scale (n p C : ℝ) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) :
    (C^((4:ℝ)/9)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9))^(-(9:ℝ)/4) =
      C⁻¹*n^((1:ℝ)/4)*p⁻¹ := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_mul hC.le, ← Real.rpow_mul hn.le, ← Real.rpow_mul hp.le]
  norm_num [Real.rpow_neg_one]

private lemma power_scale_second (n p C : ℝ) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) :
    (C^((2:ℝ)/3)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9))^(-(3:ℝ)/2) =
      C⁻¹*n^((1:ℝ)/6)*p^(-(2:ℝ)/3) := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_mul hC.le, ← Real.rpow_mul hn.le, ← Real.rpow_mul hp.le]
  norm_num [Real.rpow_neg_one]

private lemma ratio_first (n p d C : ℝ) (hn : 0 < n) (hp : 0 < p) (hC : 1 ≤ C)
    (hd : C*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) ≤ d) :
    p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4) ≤ C⁻¹ := by
  have hc0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hbase : C^((4:ℝ)/9)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) ≤ d := by
    calc
      _ ≤ C*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) := by
        gcongr
        calc
          C^((4:ℝ)/9) ≤ C^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hC (by norm_num)
          _ = C := Real.rpow_one _
      _ ≤ d := hd
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < C^((4:ℝ)/9)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9)) hbase (by norm_num : -(9:ℝ)/4 ≤ 0)
  calc
    _ ≤ p*n^(-(1:ℝ)/4)*(C^((4:ℝ)/9)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9))^(-(9:ℝ)/4) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C⁻¹ := by
      rw [power_scale n p C hn hp hc0]
      have hnp : n^(-(1:ℝ)/4)*n^((1:ℝ)/4) = 1 := by rw [← Real.rpow_add hn]; norm_num
      field_simp
      nlinarith [hnp]

private lemma ratio_second (n p d C : ℝ) (hn : 0 < n) (hp : 0 < p) (hpn : p ≤ n) (hC : 1 ≤ C)
    (hd : C*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) ≤ d) :
    p*n^(-(1:ℝ)/2)*d^(-(3:ℝ)/2) ≤ C⁻¹ := by
  have hc0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hbase : C^((2:ℝ)/3)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) ≤ d := by
    calc
      _ ≤ C*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) := by
        gcongr
        calc
          C^((2:ℝ)/3) ≤ C^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hC (by norm_num)
          _ = C := Real.rpow_one _
      _ ≤ d := hd
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < C^((2:ℝ)/3)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9)) hbase (by norm_num : -(3:ℝ)/2 ≤ 0)
  have hpnroot : p^((1:ℝ)/3) ≤ n^((1:ℝ)/3) := Real.rpow_le_rpow hp.le hpn (by norm_num)
  have h1 : p*p^(-(2:ℝ)/3) = p^((1:ℝ)/3) := by
    conv_lhs => lhs; rw [← Real.rpow_one p]
    rw [← Real.rpow_add hp]; norm_num
  have h2 : n^(-(1:ℝ)/2)*n^((1:ℝ)/6) = n^(-(1:ℝ)/3) := by
    rw [← Real.rpow_add hn]; norm_num
  have h3 : n^((1:ℝ)/3)*n^(-(1:ℝ)/3) = 1 := by rw [← Real.rpow_add hn]; norm_num
  calc
    _ ≤ p*n^(-(1:ℝ)/2)*(C^((2:ℝ)/3)*n^(-(1:ℝ)/9)*p^((4:ℝ)/9))^(-(3:ℝ)/2) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C⁻¹*(p^((1:ℝ)/3)*n^(-(1:ℝ)/3)) := by
      calc
        _ = C⁻¹*((p*p^(-(2:ℝ)/3))*(n^(-(1:ℝ)/2)*n^((1:ℝ)/6))) := by
          rw [power_scale_second n p C hn hp hc0]; norm_num <;> ring
        _ = _ := by rw [h1,h2]
    _ ≤ C⁻¹*(n^((1:ℝ)/3)*n^(-(1:ℝ)/3)) := by gcongr
    _ = C⁻¹ := by rw [h3]; norm_num <;> ring

private lemma sqrt_radius (n d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    Real.sqrt (n^((1:ℝ)/2)*d^(-(3:ℝ)/2)) = n^((1:ℝ)/4)*d^(-(3:ℝ)/4) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hn.le, ← Real.rpow_mul hd.le]
  norm_num

private lemma loss_first_id (n p d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    n*p/(d^2*Real.sqrt (n^((1:ℝ)/2)*d^(-(3:ℝ)/2))) =
      (n*d)*(p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4)) := by
  rw [sqrt_radius n d hn hd, ← Real.rpow_two d]
  rw [div_eq_mul_inv, mul_inv, mul_inv, ← Real.rpow_neg hd.le, ← Real.rpow_neg hn.le,
    ← Real.rpow_neg hd.le]
  have h1 : d^(-(2:ℝ))*d^(-(-(3:ℝ)/4)) = d^(-(5:ℝ)/4) := by
    rw [← Real.rpow_add hd]; norm_num
  have h2 : d*d^(-(9:ℝ)/4) = d^(-(5:ℝ)/4) := by
    conv_lhs => lhs; rw [← Real.rpow_one d]
    rw [← Real.rpow_add hd]; norm_num
  calc
    _ = n*p*n^(-((1:ℝ)/4))*(d^(-(2:ℝ))*d^(-(-(3:ℝ)/4))) := by norm_num <;> ring
    _ = (n*d)*(p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4)) := by rw [h1]; rw [← h2]; norm_num <;> ring

private lemma loss_second_id (n p d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    p*Real.sqrt (n*(n^((1:ℝ)/2)*d^(-(3:ℝ)/2))/d) =
      (n*d)*(p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4)) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow (by positivity) hd.le,
    Real.mul_rpow hn.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hn.le, ← Real.rpow_mul hd.le]
  have hN : n^((1:ℝ)/2)*n^(((1:ℝ)/2)*((1:ℝ)/2)) = n^((3:ℝ)/4) := by
    rw [← Real.rpow_add hn]; norm_num
  have hN' : n*n^(-(1:ℝ)/4) = n^((3:ℝ)/4) := by
    conv_lhs => lhs; rw [← Real.rpow_one n]
    rw [← Real.rpow_add hn]; norm_num
  have hD : d^((-(3:ℝ)/2)*((1:ℝ)/2))/d^((1:ℝ)/2) = d^(-(5:ℝ)/4) := by
    rw [← Real.rpow_sub hd]; norm_num
  have hD' : d*d^(-(9:ℝ)/4) = d^(-(5:ℝ)/4) := by
    conv_lhs => lhs; rw [← Real.rpow_one d]
    rw [← Real.rpow_add hd]; norm_num
  calc
    _ = p*(n^((1:ℝ)/2)*n^(((1:ℝ)/2)*((1:ℝ)/2)))*(d^((-(3:ℝ)/2)*((1:ℝ)/2))/d^((1:ℝ)/2)) := by norm_num <;> ring
    _ = (n*d)*(p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4)) := by rw [hN,hD,← hN',← hD']; simp only [neg_div]; ring

private lemma loss_six_id (n p d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    p*Real.sqrt (n*6/d) =
      (n*d)*(Real.sqrt 6*(p*n^(-(1:ℝ)/2)*d^(-(3:ℝ)/2))) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow (by positivity) hd.le, Real.mul_rpow hn.le (by norm_num)]
  have hnid : n*n^(-(1:ℝ)/2) = n^((1:ℝ)/2) := by
    conv_lhs => lhs; rw [← Real.rpow_one n]
    rw [← Real.rpow_add hn]; norm_num
  have hdid : d*d^(-(3:ℝ)/2) = (d^((1:ℝ)/2))⁻¹ := by
    conv_lhs => lhs; rw [← Real.rpow_one d]
    rw [← Real.rpow_add hd, ← Real.rpow_neg hd.le]; norm_num
  rw [Real.sqrt_eq_rpow]
  calc
    _ = (n*n^(-(1:ℝ)/2))*(d*d^(-(3:ℝ)/2))*((6:ℝ)^((1:ℝ)/2)*p) := by rw [hnid,hdid]; norm_num <;> ring
    _ = _ := by norm_num <;> ring

private lemma radius_loss_bound (n p d C : ℝ) (hn : 0 < n) (hp : 0 < p) (hpn : p ≤ n) (hC : 1 ≤ C)
    (hd : C*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) ≤ d) :
    let r := max 6 (n^((1:ℝ)/2)*d^(-(3:ℝ)/2))
    n*p/(d^2*Real.sqrt r)+p*Real.sqrt (n*r/d) ≤ (n*d)*((2+Real.sqrt 6)*C⁻¹) := by
  dsimp only
  let r₀ := n^((1:ℝ)/2)*d^(-(3:ℝ)/2)
  have hc0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hr0 : 0 < r₀ := by dsimp [r₀]; positivity
  have hnd : 0 ≤ n*d := by positivity
  have hfirst : n*p/(d^2*Real.sqrt (max 6 r₀)) ≤ (n*d)*C⁻¹ := by
    calc
      _ ≤ n*p/(d^2*Real.sqrt r₀) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_right _ _)) (sq_nonneg d)
      _ = (n*d)*(p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4)) := loss_first_id n p d hn hd0
      _ ≤ (n*d)*C⁻¹ := mul_le_mul_of_nonneg_left (ratio_first n p d C hn hp hC hd) hnd
  have hsecond : p*Real.sqrt (n*(max 6 r₀)/d) ≤ (n*d)*((1+Real.sqrt 6)*C⁻¹) := by
    by_cases h6 : 6 ≤ r₀
    · rw [max_eq_right h6]
      calc
        _ = (n*d)*(p*n^(-(1:ℝ)/4)*d^(-(9:ℝ)/4)) := loss_second_id n p d hn hd0
        _ ≤ (n*d)*C⁻¹ := mul_le_mul_of_nonneg_left (ratio_first n p d C hn hp hC hd) hnd
        _ ≤ (n*d)*((1+Real.sqrt 6)*C⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hnd
          have := Real.sqrt_nonneg (6:ℝ)
          have : 0 ≤ Real.sqrt 6*C⁻¹ := mul_nonneg this (inv_nonneg.mpr hc0.le)
          nlinarith
    · rw [max_eq_left (le_of_not_ge h6)]
      calc
        _ = (n*d)*(Real.sqrt 6*(p*n^(-(1:ℝ)/2)*d^(-(3:ℝ)/2))) := loss_six_id n p d hn hd0
        _ ≤ (n*d)*(Real.sqrt 6*C⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hnd
          exact mul_le_mul_of_nonneg_left (ratio_second n p d C hn hp hpn hC hd) (Real.sqrt_nonneg _)
        _ ≤ (n*d)*((1+Real.sqrt 6)*C⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hnd
          have : 0 ≤ C⁻¹ := inv_nonneg.mpr hc0.le
          nlinarith
  change n*p/(d^2*Real.sqrt (max 6 r₀))+p*Real.sqrt (n*(max 6 r₀)/d) ≤ _
  linarith

theorem solution : ∀ c₀ c₁ c₂ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      Sec6Setting C G H P →
      ∀ (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind),
        IsRun c₀ c₁ c₂ G H P τ st kind →
          kindLoss τ st kind StepKind.two ≤ sec6n V * sec6d H / 20 := by
  intro c₀ c₁ c₂ hc₀
  obtain ⟨A,hA,C₂,h24⟩ := DistancePreserver934.Exact.lemma_24 c₀ c₁ c₂
  let B := A*(1+c₀⁻¹)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨max 30 (max C₂ (20*B*(2+Real.sqrt 6))),?_⟩
  intro C hC V inst G H P hset τ st kind hrun
  have hC30 : 30 ≤ C := (le_max_left _ _).trans hC
  have hC₂ : C₂ ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans hC)
  have hCbig : 20*B*(2+Real.sqrt 6) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  have hC1 : 1 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  let n := sec6n V
  let p : ℝ := P.card
  let d := sec6d H
  let r := sec6r H
  have hnnonneg : 0 ≤ n := Nat.cast_nonneg _
  have hp : 0 < p := (Real.rpow_nonneg hnnonneg _).trans_lt hset.2.2.1
  have hpn : p ≤ n := hset.2.2.2.1
  have hn : 0 < n := hp.trans_le hpn
  have hident : n*n^(-(1:ℝ)/9) = n^((8:ℝ)/9) := by
    conv_lhs => lhs; rw [← Real.rpow_one n]
    rw [← Real.rpow_add hn]; norm_num
  have hd : C*n^(-(1:ℝ)/9)*p^((4:ℝ)/9) ≤ d := by
    have h := hset.2.2.2.2
    change C*n^((8:ℝ)/9)*p^((4:ℝ)/9) < n*d at h
    rw [← hident] at h
    nlinarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have h24' := h24 C hC₂ V G H P hset
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<6) h24'.1.1
  classical
  let I := (Finset.range τ).filter (fun i => kind i = StepKind.two)
  let q : ℕ → ℝ := fun i => (((st i).2 \ (st (i+1)).2).card : ℝ)
  have hsumq : ∑ i ∈ I, q i ≤ p := run_removed_sum c₀ c₁ c₂ G H P τ st kind hrun
  have hsize : ∀ i ∈ I, c₀*d^2*Real.sqrt r ≤ q i := by
    intro i hi
    obtain ⟨hi,hkind⟩ := Finset.mem_filter.mp hi
    have hiτ := Finset.mem_range.mp hi
    have hs : Step2 c₀ c₁ c₂ G H P (st i) (st (i+1)) := by
      rcases hrun.2 i hiτ with ⟨hk,hs⟩ | ⟨hk,hs⟩
      · rw [hkind] at hk; cases hk
      · exact hs
    obtain ⟨hp',hl,Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := hs
    have hQeq : (st i).2 \ (st (i+1)).2 = Q := by rw [hR']; exact Finset.sdiff_sdiff_eq_self hQR
    simpa only [q, hQeq] using hlarge
  have hcost : ∀ i ∈ I, stepLoss st i ≤ A*(n+q i*Real.sqrt (n*r/d)) := by
    intro i hi
    obtain ⟨hi,hkind⟩ := Finset.mem_filter.mp hi
    exact h24'.2 τ st kind hrun i (Finset.mem_range.mp hi) hkind
  have hsum := sum_batch_cost I q (stepLoss st) n p (c₀*d^2*Real.sqrt r)
    (Real.sqrt (n*r/d)) A hn.le (by positivity) (Real.sqrt_nonneg _) hA.le hsumq hsize hcost
  change kindLoss τ st kind StepKind.two ≤ A*(n*p/(c₀*d^2*Real.sqrt r)+p*Real.sqrt (n*r/d)) at hsum
  have hfract : n*p/(c₀*d^2*Real.sqrt r) = c₀⁻¹*(n*p/(d^2*Real.sqrt r)) := by
    field_simp
  rw [hfract] at hsum
  have hAB : A ≤ B := by dsimp [B]; nlinarith [mul_nonneg hA.le (inv_nonneg.mpr hc₀.le)]
  have hAB' : A*c₀⁻¹ ≤ B := by dsimp [B]; nlinarith
  have hnum := radius_loss_bound n p d C hn hp hpn hC1 hd
  change n*p/(d^2*Real.sqrt r)+p*Real.sqrt (n*r/d) ≤ (n*d)*((2+Real.sqrt 6)*C⁻¹) at hnum
  have hcoef : B*((2+Real.sqrt 6)*C⁻¹) ≤ 1/20 := by
    have h : B*(2+Real.sqrt 6)/C ≤ 1/20 := by
      apply (div_le_iff₀ hCpos).mpr
      nlinarith
    simpa only [div_eq_mul_inv, mul_assoc] using h
  calc
    _ ≤ A*(c₀⁻¹*(n*p/(d^2*Real.sqrt r))+p*Real.sqrt (n*r/d)) := hsum
    _ = (A*c₀⁻¹)*(n*p/(d^2*Real.sqrt r))+A*(p*Real.sqrt (n*r/d)) := by ring
    _ ≤ B*(n*p/(d^2*Real.sqrt r))+B*(p*Real.sqrt (n*r/d)) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hAB' (by positivity))
        (mul_le_mul_of_nonneg_right hAB (by positivity))
    _ = B*(n*p/(d^2*Real.sqrt r)+p*Real.sqrt (n*r/d)) := by ring
    _ ≤ B*((n*d)*((2+Real.sqrt 6)*C⁻¹)) := mul_le_mul_of_nonneg_left hnum hB.le
    _ = (n*d)*(B*((2+Real.sqrt 6)*C⁻¹)) := by ring
    _ ≤ (n*d)*(1/20) := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = sec6n V*sec6d H/20 := by dsimp [n,d]; ring
