-- Prove2me | solution 1 for GRH.unconditional_logarithmic_saving_in_reduced_moebius_progressions
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:49:18.132084+00:00
-- url     : https://prove2.me/submissions/0e0662ae-ea84-4eff-8b41-859f42ec5397

import Theorems.Thm_GRH_siegel_walfisz_errors_at_divisor_quotients_have_linear_total
import Theorems.Thm_Helfgott_coprime_mobius_reciprocal_le_one
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset Filter Topology ArithmeticFunction GRH.LogarithmicMoebius
open scoped Classical

private noncomputable def logMu : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ)*Real.log n,by simp⟩

private theorem logConvolution : logMu = -((ArithmeticFunction.moebius : ArithmeticFunction ℝ)*vonMangoldt) := by
  have e : logMu*(ArithmeticFunction.zeta : ArithmeticFunction ℝ) = -vonMangoldt := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  calc
    logMu = (logMu*(ArithmeticFunction.zeta : ArithmeticFunction ℝ))*(ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
      rw [mul_assoc,ArithmeticFunction.coe_zeta_mul_coe_moebius,mul_one]
    _ = _ := by rw [e]; ring

/- Divisor-pair reindexing follows the public exact remainder proof
https://prove2.me/submissions/d3678297-aaf8-42d1-8177-c9a80f031779 . -/
private theorem weighted_convolution (n : ℕ) (w : ℕ → ℝ) (f g : ArithmeticFunction ℝ) :
    (∑ k ∈ Ioc 0 n, w k * (f * g) k) =
    ∑ d ∈ Ioc 0 n, f d * ∑ e ∈ Ioc 0 (n / d), w (d * e) * g e := by
  classical
  let box := (Ioc 0 n) ×ˢ (Ioc 0 n)
  calc
    _ = ∑ k ∈ Ioc 0 n, ∑ p ∈ box, if p.1 * p.2 = k then
          w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      refine sum_congr rfl fun k hk => ?_
      obtain ⟨hk0, hkn⟩ := mem_Ioc.mp hk
      rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk0.ne' hkn,
        mul_sum, ← sum_filter]
      refine sum_congr rfl fun p hp => ?_
      rw [(mem_filter.mp hp).2]
    _ = ∑ p ∈ box, if p.1 * p.2 ≤ n then w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      rw [sum_comm]
      refine sum_congr rfl fun p hp => ?_
      have hp' := mem_product.mp hp
      have hpos := Nat.mul_pos (mem_Ioc.mp hp'.1).1 (mem_Ioc.mp hp'.2).1
      simp [mem_Ioc, hpos]
    _ = _ := by
      rw [show box = _ from rfl, sum_product]
      refine sum_congr rfl fun d hd => ?_
      have hd0 := (mem_Ioc.mp hd).1
      rw [mul_sum]
      have heq : (Ioc 0 (n / d)) = (Ioc 0 n).filter (fun e => d * e ≤ n) := by
        ext e
        simp only [mem_Ioc, mem_filter]
        rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm e d]
        constructor
        · rintro ⟨he, h⟩
          exact ⟨⟨he, ((Nat.le_div_iff_mul_le hd0).mpr (by simpa [Nat.mul_comm] using h)).trans
            (Nat.div_le_self n d)⟩, h⟩
        · rintro ⟨⟨he, _⟩, h⟩
          exact ⟨he, h⟩
      rw [heq, sum_filter]
      apply sum_congr rfl
      intro e _
      dsimp only
      split_ifs <;> ring

private noncomputable def divided {q : ℕ} (a : (ZMod q)ˣ) (d : ℕ) : (ZMod q)ˣ :=
  if h : IsUnit (d : ZMod q) then h.unit⁻¹*a else 1

private theorem productRow {q : ℕ} (a : (ZMod q)ˣ) (d m : ℕ) :
    (∑ n ∈ Ioc 0 m, (if ((d*n : ℕ) : ZMod q) = (a : ZMod q) then (1:ℝ) else 0)*vonMangoldt n) =
    if IsUnit (d : ZMod q) then psi (divided a d : ZMod q) m else 0 := by
  classical
  by_cases h : IsUnit (d : ZMod q)
  · rw [if_pos h]
    unfold psi
    apply sum_congr rfl
    intro n _
    have eq : ((d*n : ℕ) : ZMod q) = (a : ZMod q) ↔ (n : ZMod q) = (divided a d : ZMod q) := by
      have lemma_u (u : (ZMod q)ˣ) : (u:ZMod q)*(n:ZMod q) = a ↔
          (n:ZMod q) = (↑u⁻¹:ZMod q)*(a:ZMod q) := by
        constructor
        · intro he
          calc
            _ = (↑u⁻¹ : ZMod q)*(↑u*(n:ZMod q)) := by simp [← mul_assoc]
            _ = _ := by rw [he]
        · intro he
          rw [he,← mul_assoc]
          simp
      simpa only [Nat.cast_mul,divided,dif_pos h,Units.val_mul,h.unit_spec] using lemma_u h.unit
    by_cases he : ((d*n : ℕ) : ZMod q) = (a : ZMod q)
    · simp [he,eq.mp he]
    · rw [if_neg he,if_neg (mt eq.mpr he),zero_mul]
  · rw [if_neg h]
    apply sum_eq_zero
    intro n _
    have e : ((d*n : ℕ) : ZMod q) ≠ (a : ZMod q) := by
      intro he
      rw [Nat.cast_mul] at he
      exact h (IsUnit.mul_iff.mp (he.symm ▸ a.isUnit)).1
    rw [if_neg e,zero_mul]

private theorem weightedBound {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (N : ℕ) :
    |residueLog (a : ZMod q) N| ≤ (∑ d ∈ Ioc 0 N,
       |psi (divided a d : ZMod q) (N/d)-(N:ℝ)/d/q.totient|) + (N:ℝ) := by
  classical
  let w := fun n : ℕ => if (n : ZMod q) = (a : ZMod q) then (1:ℝ) else 0
  let f := fun d : ℕ => if IsUnit (d : ZMod q) then (ArithmeticFunction.moebius d : ℝ) else 0
  let main := fun d : ℕ => (N:ℝ)/d/q.totient
  let v := fun d : ℕ => psi (divided a d : ZMod q) (N/d)
  have coeff : residueLog (a : ZMod q) N =
      -(∑ d ∈ Ioc 0 N, f d*v d) := by
    calc
      _ = ∑ n ∈ Ioc 0 N, w n*logMu n := by
        unfold residueLog
        apply sum_congr rfl
        intro n _
        dsimp [w,logMu]
        split_ifs <;> simp
      _ = -(∑ n ∈ Ioc 0 N, w n*((ArithmeticFunction.moebius : ArithmeticFunction ℝ)*vonMangoldt) n) := by
        rw [logConvolution,← sum_neg_distrib]
        apply sum_congr rfl
        intro n _
        simp
      _ = _ := by
        rw [weighted_convolution]
        congr 1
        apply sum_congr rfl
        intro d _
        change (ArithmeticFunction.moebius d : ℝ)*_ = _
        rw [show (∑ e ∈ Ioc 0 (N/d), w (d*e)*vonMangoldt e) = _ from productRow a d _]
        by_cases h : IsUnit (d : ZMod q) <;> simp [h,f,v]
  have hmain : ∑ d ∈ Ioc 0 N, f d*main d =
      ((N:ℝ)/q.totient)*GRH.reducedMoebiusHarmonic q N := by
    unfold GRH.reducedMoebiusHarmonic
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    by_cases h : IsUnit (d:ZMod q) <;> simp only [f,main,h,if_true,if_false,zero_mul,mul_zero]
    ring
  have hi : Ioc 0 N = Icc 1 N := by ext k; simp; omega
  have hh : |GRH.reducedMoebiusHarmonic q N| ≤ 1 := by
    simpa only [GRH.reducedMoebiusHarmonic,hi,ZMod.isUnit_iff_coprime] using
      Helfgott.coprime_mobius_reciprocal_le_one q N
  have hm : |∑ d ∈ Ioc 0 N, f d*main d| ≤ (N : ℝ) := by
    rw [hmain,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (N:ℝ)/q.totient)]
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans (by
      rw [mul_one]
      exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)))
  have hab (d : ℕ) : |f d| ≤ 1 := by
    dsimp [f]
    split_ifs
    · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
    · norm_num
  rw [coeff,abs_neg]
  calc
    _ = |(∑ d ∈ Ioc 0 N, f d*(v d-main d)) + ∑ d ∈ Ioc 0 N, f d*main d| := by
      simp only [mul_sub,sum_sub_distrib,sub_add_cancel]
    _ ≤ |∑ d ∈ Ioc 0 N, f d*(v d-main d)| + |∑ d ∈ Ioc 0 N, f d*main d| := abs_add_le _ _
    _ ≤ (∑ d ∈ Ioc 0 N, |v d-main d|)+(N:ℝ) := by
      apply add_le_add _ hm
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hab d)

private theorem logLoss (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (Real.log ((N:ℝ)+1)-Real.log n) ≤ (N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi : Ioc 0 (N+1)=insert (N+1) (Ioc 0 N) := by ext n; simp; omega
    let D := Real.log (((N:ℝ)+1)+1) - Real.log ((N:ℝ)+1)
    have hD : ((N:ℝ)+1)*D ≤ 1 := by
      let t : ℝ := (N:ℝ)+1
      have hp : 0<t := by dsimp [t]; positivity
      change t*(Real.log (t+1)-Real.log t) ≤ 1
      rw [← Real.log_div (by positivity) hp.ne']
      calc
        _ ≤ t*((t+1)/t-1) := mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos (by positivity) hp)) hp.le
        _ = _ := by field_simp; ring
    rw [hi,sum_insert (by simp)]
    simp only [Nat.cast_add,Nat.cast_one]
    change D + _ ≤ _
    have split (n : ℕ) : Real.log (((N:ℝ)+1)+1)-Real.log n =
        (Real.log ((N:ℝ)+1)-Real.log n)+D := by dsimp [D]; ring
    simp_rw [split]
    rw [sum_add_distrib]
    simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
    linarith only [ih,hD]

private theorem unweight {q : ℕ} (a : ZMod q) (N : ℕ) :
    |residue a N| *scale N ≤ |residueLog a N|+2*(N:ℝ) := by
  let f := fun n : ℕ => if (n : ZMod q)=a then (ArithmeticFunction.moebius n : ℝ) else 0
  have hs : 0 ≤ scale N := by unfold scale; linarith [Real.log_nonneg (by simp : (1:ℝ)≤(N:ℝ)+1)]
  have hlog : residueLog a N = ∑ n ∈ Ioc 0 N, f n*Real.log n := by
    unfold residueLog
    apply sum_congr rfl
    intro n _
    by_cases h : (n : ZMod q)=a <;> simp [h,f]
  have diff : residue a N*scale N-residueLog a N =
      ∑ n ∈ Ioc 0 N, f n*(scale N-Real.log n) := by
    rw [hlog]
    change (∑ n ∈ Ioc 0 N, f n)*scale N-_ = _
    simp only [sum_mul,mul_sub,sum_sub_distrib]
  have hcap : |residue a N*scale N-residueLog a N| ≤ 2*(N:ℝ) := by
    rw [diff]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, (1+(Real.log ((N:ℝ)+1)-Real.log n)) := by
        apply sum_le_sum
        intro n hn
        have H := mem_Ioc.mp hn
        have hn' : (0:ℝ)<n := by exact_mod_cast H.1
        have hN' : (n:ℝ) ≤ N := by exact_mod_cast H.2
        have hl := Real.log_le_log hn' (show (n:ℝ)≤(N:ℝ)+1 by linarith)
        have ha : |f n| ≤ 1 := by
          dsimp [f]
          split_ifs
          · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
          · norm_num
        rw [abs_mul,abs_of_nonneg (show 0 ≤ scale N-Real.log n by unfold scale; linarith)]
        exact (mul_le_of_le_one_left (by unfold scale;linarith) ha).trans_eq (by unfold scale;ring)
      _ ≤ _ := by
        rw [sum_add_distrib]
        simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
        linarith only [logLoss N]
  have tri := abs_sub_le (residue a N*scale N) (residueLog a N) 0
  rw [sub_zero,sub_zero,abs_mul,abs_of_nonneg hs] at tri
  linarith only [tri,hcap]

theorem solution (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : (ZMod q)ˣ) (N : ℕ),
      |residueLog (a : ZMod q) N| ≤ C*(N:ℝ) ∧ |residue (a : ZMod q) N| *scale N ≤ C*(N:ℝ) := by
  obtain ⟨K,hK,h⟩ := GRH.siegel_walfisz_errors_at_divisor_quotients_have_linear_total q
  refine ⟨K+3,by linarith,fun a N => ?_⟩
  have e := weightedBound a N
  have p := h N (divided a)
  have u := unweight (a : ZMod q) N
  have hn := Nat.cast_nonneg (α:=ℝ) N
  constructor <;> linarith only [e,p,u,hn]
