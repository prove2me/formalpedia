-- Prove2me | solution 1 for GRH.riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:45:50.667903+00:00
-- url     : https://prove2.me/submissions/eae906ea-b468-418e-b66f-9c96034795f5

import Mathlib
import Definitions.Def_GRH_SquarefreeBilinear
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Theorems.Thm_GRH_moebius_harmonic_decay_of_bounded_dirichlet_prefixes
import Theorems.Thm_GRH_liouville_harmonic_le_of_moebius_harmonic_le
import Theorems.Thm_GRH_reduced_liouville_harmonic_le_of_modulus_one
import Theorems.Thm_GRH_moebius_progression_le_of_liouville_progression_le
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

open Finset ArithmeticFunction Filter Topology Asymptotics
open scoped BigOperators zeta Moebius

open GRH

private theorem harmonic_of_RH
    (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1/2 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ,
      |reducedLiouvilleHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by
  classical
  let f (n : ℕ) := (moebius n:ℝ)*(n:ℝ)^(-σ)
  obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hhalf
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH)
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  have hbound (N : ℕ) : |∑ n ∈ range N, f n| ≤ max 0 B := by
    cases N with
    | zero => simp
    | succ N =>
      have he : range (N+1) = insert 0 (Icc 1 N) := by ext k; simp; omega
      rw [he, sum_insert (by simp),show f 0 = 0 by simp [f],zero_add]
      exact (hB ⟨N,rfl⟩).trans (le_max_right ..)
  have hC : 0 ≤ max 0 B := le_max_left .. 
  let Z := ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  let D := ∑ d ∈ q.divisors, |(moebius d:ℝ)| * (d:ℝ)^(-σ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => by positivity)
  have hD : 0 ≤ D := sum_nonneg (fun d _ => by positivity)
  refine ⟨((2 * max 0 B) * Z) * D, by positivity, ?_⟩
  intro U
  apply reduced_liouville_harmonic_le_of_modulus_one q σ _ hone.le (by positivity) _ U
  intro V
  apply liouville_harmonic_le_of_moebius_harmonic_le σ _ hhalf hone.le (by positivity) _ V
  exact moebius_harmonic_decay_of_bounded_dirichlet_prefixes σ _ hone.le hC hbound



private theorem harmonic_as_range (q U : ℕ) [NeZero q] :
    reducedLiouvilleHarmonic q U = ∑ n ∈ range (U+1),
      if Nat.Coprime n q then (liouville n : ℝ) / n else 0 := by
  classical
  unfold reducedLiouvilleHarmonic
  simp_rw [ZMod.isUnit_iff_coprime]
  have he : range (U+1) = insert 0 (Ioc 0 U) := by ext k; simp
  rw [he,sum_insert (by simp)]
  simp

private theorem sum_multiples_upto (N t : ℕ) (ht : 0 < t) (F : ℕ → ℝ) :
    (∑ k ∈ range (N+1), if t ∣ k then F k else 0) =
      ∑ j ∈ range (N/t+1), F (t*j) := by
  rw [←Finset.sum_filter]
  apply sum_bij' (fun k _ => k/t) (fun j _ => t*j)
  · intro k hk
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hk).1)))
  · intro j hj
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),dvd_mul_right _ _⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le ht).mp (Nat.le_of_lt_succ (mem_range.mp hj))
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    exact Nat.mul_div_cancel_left _ ht
  · intro k hk
    rw [Nat.mul_div_cancel' (mem_filter.mp hk).2]

private theorem div_floor_power_bound (U d : ℕ) (hd : 0 < d) (σ : ℝ) (hσ : σ ≤ 1) :
    (((U / d : ℕ) : ℝ) + 1) ^ (σ - 1) / (d : ℝ) ≤
      ((U:ℝ)+1) ^ (σ-1) * (d:ℝ)^(-σ) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hn : U+1 ≤ (U/d+1)*d := by
    have h1 := Nat.mod_lt U hd
    have h2 := Nat.mod_add_div U d
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (U/d)] 
    omega
  have hx : ((U:ℝ)+1)/(d:ℝ) ≤ ((U/d:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ hdR).mpr
    exact_mod_cast hn
  apply (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith : σ-1 ≤ 0)) hdR.le).trans_eq
  rw [Real.div_rpow (by positivity) hdR.le,div_div]
  have hpow : (d:ℝ)^(σ-1) * (d:ℝ) = (d:ℝ)^σ := by
    rw [←Real.rpow_add_one hdR.ne']; congr 1; ring
  rw [hpow,Real.rpow_neg hdR.le,div_eq_mul_inv]

private theorem harmonic_repeat_prime (q p U : ℕ) [NeZero q] [NeZero (q*p)] (hpq : p ∣ q) :
    reducedLiouvilleHarmonic (q*p) U = reducedLiouvilleHarmonic q U := by
  rw [harmonic_as_range,harmonic_as_range]
  apply sum_congr rfl
  intro n _
  simp only [Nat.coprime_mul_iff_right, and_iff_left_of_imp (fun h : n.Coprime q => h.of_dvd_right hpq)]

private theorem harmonic_insert_prime (q p U : ℕ) [NeZero q] [NeZero (q*p)]
    (hp : p.Prime) (hpq : ¬p ∣ q) :
    reducedLiouvilleHarmonic (q*p) U =
      reducedLiouvilleHarmonic q U + reducedLiouvilleHarmonic q (U/p)/(p:ℝ) := by
  classical
  let f (n : ℕ) := if n.Coprime q then (liouville n : ℝ) / n else 0
  have hcp : p.Coprime q := hp.coprime_iff_not_dvd.mpr hpq
  have hpval : liouville p = -1 := by rw [liouville_apply hp.ne_zero,cardFactors_apply_prime hp,pow_one]
  have hsum : (∑ k ∈ range (U+1), if p ∣ k then f k else 0) =
      -(reducedLiouvilleHarmonic q (U/p) / (p:ℝ)) := by
    rw [sum_multiples_upto U p hp.pos,harmonic_as_range,Finset.sum_div,←sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    simp only [f, Nat.coprime_mul_iff_left, liouville_apply_mul, hpval, Int.cast_mul,
      Int.cast_neg, Int.cast_one,Nat.cast_mul]
    by_cases hj : j.Coprime q
    · rw [if_pos (And.intro hcp hj),if_pos hj]; ring
    · rw [if_neg (fun h : p.Coprime q ∧ j.Coprime q => hj h.2),if_neg hj]; simp
  have hred : reducedLiouvilleHarmonic (q*p) U = reducedLiouvilleHarmonic q U -
      ∑ k ∈ range (U+1), if p ∣ k then f k else 0 := by
    rw [harmonic_as_range,harmonic_as_range,←sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    simp only [Nat.coprime_mul_iff_right,show k.Coprime p ↔ ¬p ∣ k from
      Nat.coprime_comm.trans hp.coprime_iff_not_dvd]
    by_cases hq : k.Coprime q <;> by_cases hk : p ∣ k <;> simp [hq,hk,f]
  rw [hred,hsum,sub_neg_eq_add]

private theorem remove_prime_harmonic_bound (q p : ℕ) [NeZero q] [NeZero (q*p)]
    (hp : p.Prime) (σ : ℝ) (hσ : 0 < σ) (h1 : σ ≤ 1)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ,
      |reducedLiouvilleHarmonic (q*p) U| ≤ C*((U:ℝ)+1)^(σ-1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ, |reducedLiouvilleHarmonic q U| ≤ C*((U:ℝ)+1)^(σ-1) := by
  obtain ⟨C,hC,h⟩ := H
  by_cases hpq : p ∣ q
  · exact ⟨C,hC,fun U => harmonic_repeat_prime q p U hpq ▸ h U⟩
  have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  let a := (p:ℝ)^(-σ)
  have ha : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  let K := C / (1-a)
  have hK : 0 ≤ K := div_nonneg hC (by linarith)
  have hid : C + K*a = K := by dsimp [K]; field_simp [ne_of_gt (sub_pos.mpr ha)]; ring
  refine ⟨K,hK,?_⟩
  intro U
  induction U using Nat.strong_induction_on with
  | h U ih =>
    by_cases hU : U = 0
    · simpa [hU,reducedLiouvilleHarmonic] using hK
    have he := harmonic_insert_prime q p U hp hpq
    have he' : reducedLiouvilleHarmonic q U =
        reducedLiouvilleHarmonic (q*p) U - reducedLiouvilleHarmonic q (U/p)/(p:ℝ) := by linarith
    rw [he']
    apply (abs_sub _ _).trans
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) p)]
    have hsmall := ih (U/p) (Nat.div_lt_self (Nat.pos_of_ne_zero hU) hp.one_lt)
    have hfrac : |reducedLiouvilleHarmonic q (U/p)| / (p:ℝ) ≤ K*a*((U:ℝ)+1)^(σ-1) := by
      apply (div_le_div_of_nonneg_right hsmall (Nat.cast_nonneg p)).trans
      rw [mul_div_assoc]
      exact (mul_le_mul_of_nonneg_left (div_floor_power_bound U p hp.pos σ h1) hK).trans_eq (by dsimp [a];ring)
    exact (add_le_add (h U) hfrac).trans_eq (by rw [←add_mul,hid])

private theorem modulus_one_of_fixed_modulus
    (q : ℕ) [hq0 : NeZero q] (σ : ℝ) (hσ : 0 < σ) (h1 : σ ≤ 1)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ,
      |reducedLiouvilleHarmonic q U| ≤ C*((U:ℝ)+1)^(σ-1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ, |reducedLiouvilleHarmonic 1 U| ≤ C*((U:ℝ)+1)^(σ-1) := by
  revert H hq0
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq0 H
    by_cases hq : q = 1
    · subst q; exact H
    obtain ⟨p,hp,d,hd⟩ := Nat.exists_prime_and_dvd hq
    have hd0 : d ≠ 0 := by rintro rfl; simp [NeZero.ne q] at hd
    have hdq : d < q := by
      rw [hd,mul_comm]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hd0) hp.one_lt
    letI : NeZero d := ⟨hd0⟩
    have hdq' : q = d*p := hd.trans (Nat.mul_comm ..)
    letI : NeZero (d*p) := ⟨Nat.mul_ne_zero hd0 hp.ne_zero⟩
    have Hprod : ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ, |reducedLiouvilleHarmonic (d*p) U| ≤ C*((U:ℝ)+1)^(σ-1) := by
      simpa only [←hdq'] using H
    exact ih d hdq (remove_prime_harmonic_bound d p hp σ hσ h1 Hprod)



private theorem sum_power (N : ℕ) (σ : ℝ) (hσ : 0 < σ) (h1 : σ ≤ 1) :
    (∑ k ∈ range N, ((k:ℝ)+1)^(σ-1)) ≤ (1+1/σ) * ((N:ℝ)+1)^σ := by
  have hanti : AntitoneOn (fun x : ℝ => x^(σ-1)) (Set.Icc (1:ℝ) (1+N)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx.1) hxy (by linarith)
  have hint := hanti.sum_le_integral (a:=N)
  rw [integral_rpow (.inl (by linarith)), show σ-1+1=σ by ring,Real.one_rpow] at hint
  have hsum : (∑ k ∈ range (N+1), ((k:ℝ)+1)^(σ-1)) =
       (∑ k ∈ range N, (1+((k+1:ℕ):ℝ))^(σ-1)) + 1 := by
    rw [sum_range_succ']; simp [add_comm]
  have hpos : 1 ≤ ((N:ℝ)+1)^σ :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) N]) hσ.le
  have hincl := sum_le_sum_of_subset_of_nonneg (s:=range N) (t:=range (N+1))
    (f:=fun k : ℕ => ((k:ℝ)+1)^(σ-1)) (range_mono (Nat.le_succ N)) (by intros; positivity)
  apply hincl.trans
  rw [hsum]
  apply (add_le_add hint (le_refl (1:ℝ))).trans
  rw [add_comm (1:ℝ) N]
  have hp : 0 ≤ 1/σ := by positivity
  nlinarith [div_eq_mul_inv (((N:ℝ)+1)^σ-1) σ,div_eq_mul_inv (1:ℝ) σ]

private theorem harmonic_to_ordinary (σ C : ℝ) (hσ : 0 < σ) (h1 : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |reducedLiouvilleHarmonic 1 U| ≤ C*((U:ℝ)+1)^(σ-1))
    (N : ℕ) :
    |∑ n ∈ range (N+1), (liouville n:ℝ)| ≤ (C*(2+1/σ))*((N:ℝ)+1)^σ := by
  let g (n : ℕ) := (liouville n:ℝ)/n
  have hsum (U : ℕ) : (∑ n ∈ range (U+1), g n) = reducedLiouvilleHarmonic 1 U := by
    have he : range (U+1) = insert 0 (Ioc 0 U) := by ext k; simp
    rw [he,sum_insert (by simp),reducedLiouvilleHarmonic]
    simp only [ZMod.isUnit_iff_coprime,if_pos (Nat.coprime_one_right _)]
    simp [g]
  have h := sum_range_by_parts (fun n : ℕ => (n:ℝ)) g (N+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add_one,add_sub_cancel_left,one_mul, hsum] at h
  have hval (n : ℕ) : (n:ℝ)*g n = (liouville n : ℝ) := by
    by_cases hn : n=0
    · simp [hn,g]
    · dsimp [g]; field_simp
  simp_rw [hval] at h
  rw [h]
  apply (abs_sub _ _).trans
  have hfirst : |(N:ℝ)*reducedLiouvilleHarmonic 1 N| ≤ C*((N:ℝ)+1)^σ := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) N)]
    apply (mul_le_mul_of_nonneg_left (H N) (Nat.cast_nonneg N)).trans
    calc _ ≤ ((N:ℝ)+1)*(C*((N:ℝ)+1)^(σ-1)) := by gcongr; linarith
         _ = _ := by
           have he := Real.rpow_add_one (show (N:ℝ)+1≠0 by positivity) (σ-1)
           rw [show σ-1+1=σ by ring] at he
           rw [he]; ring
  have hsecond : |∑ k ∈ range N, reducedLiouvilleHarmonic 1 k| ≤
      C*((1+1/σ)*((N:ℝ)+1)^σ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (fun i _ => H i)).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_power N σ hσ h1) hC
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

private theorem strip_of_harmonic (σ C : ℝ) (hhalf : 1/2 < σ) (h1 : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |reducedLiouvilleHarmonic 1 U| ≤ C*((U:ℝ)+1)^(σ-1))
    {s : ℂ} (hz : riemannZeta s = 0) (hnt : ¬∃ n : ℕ, s = -2*(n+1)) (hne : s≠1) :
    1-σ ≤ s.re ∧ s.re ≤ σ := by
  have hσ : 0 < σ := by linarith
  let B := C*(2+1/σ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K := B * (2:ℝ)^σ * (∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmob (N : ℕ) : |∑ n ∈ range (N+1), (moebius n:ℝ)| ≤ K*((N:ℝ)+1)^σ := by
    have he (a b : ZMod 1) : a = b := Subsingleton.elim .. 
    have ht := moebius_progression_le_of_liouville_progression_le 1 σ B hhalf hB
      (fun a _ N => by simpa only [if_pos (he _ _)] using harmonic_to_ordinary σ C hσ h1 hC H N)
      (1 : ZMod 1) isUnit_one N
    simpa only [if_pos (he _ _)] using ht
  apply nontrivial_zero_strip_of_moebius_summatory_power_bound hσ.le _ hz hnt hne
  apply Asymptotics.IsBigO.of_bound (K*(2:ℝ)^σ)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he : range (N+1) = insert 0 (Icc 1 N) := by ext k; simp; omega
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) σ)]
  have he' : ‖∑ n ∈ Icc 1 N, (moebius n:ℂ)‖ = |∑ n ∈ range (N+1), (moebius n:ℝ)| := by
    rw [he,sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero,Int.cast_zero,zero_add]
    rw [←Real.norm_eq_abs,←Complex.norm_real]
    norm_cast
    simp [Int.norm_eq_abs]
  rw [he']
  apply (hmob N).trans
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (N:ℝ)+1)
    (by linarith : (N:ℝ)+1 ≤ 2*(N:ℝ)) hσ.le
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)] at hpow
  exact (mul_le_mul_of_nonneg_left hpow hK).trans_eq (by ring)


theorem solution
    (q : ℕ) [NeZero q] :
    RiemannHypothesis ↔
      ∀ σ : ℝ, 1/2 < σ → σ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ,
        |reducedLiouvilleHarmonic q U| ≤ C*((U:ℝ)+1)^(σ-1) := by
  constructor
  · exact fun h σ hhalf hone => harmonic_of_RH h q σ hhalf hone
  · intro H s hz hnt hne
    by_contra hnot
    let d := |s.re-1/2|/2
    let e := min d (1/4)
    have hd : 0 < d := div_pos (abs_pos.mpr (sub_ne_zero.mpr hnot)) (by norm_num)
    have he : 0 < e := lt_min hd (by norm_num)
    have he1 : e ≤ 1/4 := min_le_right .. 
    have he2 : e ≤ d := min_le_left .. 
    let σ := 1/2 + e
    have hhalf : 1/2 < σ := by dsimp [σ]; linarith
    have h1 : σ < 1 := by dsimp [σ]; linarith
    obtain ⟨C,hC,h⟩ := modulus_one_of_fixed_modulus q σ (by linarith) h1.le (H σ hhalf h1)
    obtain ⟨hl,hr⟩ := strip_of_harmonic σ C hhalf h1.le hC h hz hnt hne
    have hw : |s.re-1/2| ≤ e := abs_le.mpr ⟨by dsimp [σ] at hl; linarith, by dsimp [σ] at hr; linarith⟩
    dsimp [d] at he2 hd
    linarith

