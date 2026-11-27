-- Prove2me | solution 1 for GRH.siegel_walfisz_errors_at_divisor_quotients_have_linear_total
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:47:44.82778+00:00
-- url     : https://prove2.me/submissions/900dfb38-3b64-471e-808d-d48f2a0c0cfe

import Definitions.Def_GRH_LogarithmicMoebius
import Theorems.Thm_SWPort_Davenport_siegel_walfisz_ap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset Filter Topology GRH.LogarithmicMoebius

private theorem decay (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    Real.exp (-c*Real.sqrt t)*(1+t)^2 ≤ 2+48/c^4 := by
  let y := Real.sqrt t
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have ee : 1 ≤ Real.exp (c*y) := Real.one_le_exp (mul_nonneg hc.le hy)
  have hp := Real.pow_div_factorial_le_exp (c*y) (mul_nonneg hc.le hy) 4
  norm_num at hp
  have hy2 : y^2=t := Real.sq_sqrt ht
  change Real.exp (-c*y)*(1+t)^2 ≤ _
  rw [neg_mul,Real.exp_neg,inv_mul_eq_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h4 : t^2 ≤ 24/c^4 * Real.exp (c*y) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hc _)).mpr
    rw [← hy2]
    calc
      _ = (c*y)^4 := by ring
      _ ≤ _ := by linarith only [hp]
  calc
    _ ≤ 2+2*t^2 := by nlinarith only [sq_nonneg (t-1)]
    _ ≤ 2*Real.exp (c*y)+2*(24/c^4*Real.exp (c*y)) :=
      add_le_add (by linarith only [ee]) (mul_le_mul_of_nonneg_left h4 (by norm_num))
    _ = _ := by ring

private noncomputable def err {q : ℕ} (a : (ZMod q)ˣ) (m : ℕ) : ℝ :=
  |psi (a : ZMod q) m-((m : ℝ)+1)/(q.totient : ℝ)|

private theorem localEnvelope (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : (ZMod q)ˣ) (j m : ℕ), 2^j ≤ m → m < 2^(j+1) →
      err a m ≤ C*(2:ℝ)^j/((j:ℝ)+1)^2 := by
  classical
  obtain ⟨c,B,hc,hB,hsw⟩ := SWPort.Davenport.siegel_walfisz_ap 1 (by norm_num)
  let l := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  have hl1 : l ≤ 1 := by dsimp [l]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  obtain ⟨J,hJ⟩ := exists_nat_ge ((q : ℝ)/l)
  let D := ∑ b : (ZMod q)ˣ, ∑ u ∈ range (2^J+1), err b u
  have hD : 0 ≤ D := sum_nonneg fun b _ => sum_nonneg fun u _ => abs_nonneg _
  let K := 2*B*((2+48/c^4)/l^2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+D*((J : ℝ)+1)^2,by positivity,fun a j m hlo hhi => ?_⟩
  have hj : 0 < (j:ℝ)+1 := by positivity
  apply (le_div_iff₀ (sq_pos_of_pos hj)).mpr
  by_cases h : J ≤ j
  · have hm : 1 ≤ m := (Nat.one_le_pow _ _ (by decide)).trans hlo
    let t := Real.log ((m : ℝ)+1)
    have ht : 0 ≤ t := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) m])
    have hlj : (j:ℝ)*l ≤ t := by
      have hp : (2:ℝ)^j ≤ (m:ℝ)+1 := (by exact_mod_cast hlo : (2:ℝ)^j ≤ m).trans (by linarith)
      simpa only [Real.log_pow] using Real.log_le_log (by positivity) hp
    have hq : (q : ℝ) ≤ t := le_trans (by
      exact (div_le_iff₀ hl).mp (hJ.trans (by exact_mod_cast h))) hlj
    have hb := (ZMod.isUnit_iff_coprime (a : ZMod q).val q).mp
      (by simpa only [ZMod.natCast_zmod_val] using a.isUnit)
    have sw := hsw (m+1) q (a : ZMod q).val (by omega) (NeZero.pos q)
      (by simpa only [Real.rpow_one,Nat.cast_add,Nat.cast_one] using hq) hb
    have eq : SWPort.Davenport.psiAP (m+1) q (a : ZMod q).val = psi (a : ZMod q) m := by
      unfold SWPort.Davenport.psiAP psi
      have hi : range (m+1)=insert 0 (Ioc 0 m) := by ext n; simp
      rw [hi,sum_insert (by simp)]
      simp
    rw [eq,Nat.cast_add,Nat.cast_one] at sw
    change err a m ≤ B*((m:ℝ)+1)*Real.exp (-c*Real.sqrt t) at sw
    have htj : ((j:ℝ)+1)*l ≤ 1+t := by linarith only [hlj,hl1]
    have hpol : Real.exp (-c*Real.sqrt t)*((j:ℝ)+1)^2 ≤ (2+48/c^4)/l^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
      calc
        _ = Real.exp (-c*Real.sqrt t)*(((j:ℝ)+1)*l)^2 := by ring
        _ ≤ Real.exp (-c*Real.sqrt t)*(1+t)^2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg hj.le hl.le) htj 2) (Real.exp_pos _).le
        _ ≤ _ := decay c t hc ht
    have hlen : (m:ℝ)+1 ≤ 2*(2:ℝ)^j := by
      have e : (m:ℝ)+1 ≤ (2:ℝ)^(j+1) := by exact_mod_cast Nat.succ_le_of_lt hhi
      simpa only [pow_succ,mul_comm] using e
    calc
      _ ≤ (B*((m:ℝ)+1))*(Real.exp (-c*Real.sqrt t)*((j:ℝ)+1)^2) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right sw (sq_nonneg _)
      _ ≤ (B*(2*(2:ℝ)^j))*((2+48/c^4)/l^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left hlen hB.le) hpol (by positivity) (by positivity)
      _ = K*(2:ℝ)^j := by dsimp [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hD (sq_nonneg ((J:ℝ)+1))]) (by positivity)
  · have hm : m < 2^J+1 := by
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : j+1 ≤ J)
      omega
    have he : err a m ≤ D := (single_le_sum (f:=fun u => err a u) (fun u _ => abs_nonneg _)
      (mem_range.mpr hm)).trans (single_le_sum (f:=fun b : (ZMod q)ˣ => ∑ u ∈ range (2^J+1), err b u)
        (fun b _ => sum_nonneg fun u _ => abs_nonneg _) (mem_univ a))
    have hjJ : (j:ℝ) ≤ J := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hh : err a m*((j:ℝ)+1)^2 ≤ D*((J:ℝ)+1)^2 := mul_le_mul he
      (pow_le_pow_left₀ hj.le (by linarith) 2) (sq_nonneg _) hD
    exact hh.trans ((le_add_of_nonneg_left hK).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))))

private theorem grouped (N : ℕ) (v : ℕ → ℝ) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hs : Summable b) (h : ∀ d ∈ Ioc 0 N, let j := Nat.log 2 (N/d); v d ≤ (2:ℝ)^j*b j) :
    ∑ d ∈ Ioc 0 N, v d ≤ (N:ℝ)*∑' j, b j := by
  classical
  let g := fun d : ℕ => Nat.log 2 (N/d)
  have hg (d : ℕ) (_ : d ∈ Ioc 0 N) : g d ∈ range (N+1) :=
    mem_range.mpr (Nat.lt_succ_of_le ((Nat.log_le_self _ _).trans (Nat.div_le_self ..)))
  rw [← sum_fiberwise_of_maps_to hg]
  calc
    _ ≤ ∑ j ∈ range (N+1), (N:ℝ)*b j := by
      apply sum_le_sum
      intro j _
      let S := (Ioc 0 N).filter fun d => g d=j
      have hsub : S ⊆ Ioc 0 (N/2^j) := by
        intro d hd
        obtain ⟨hm,he⟩ := mem_filter.mp hd
        have ⟨hd0,hdN⟩ := mem_Ioc.mp hm
        have hdiv := Nat.pow_log_le_self 2 (Nat.div_pos hdN hd0).ne'
        change 2^(g d) ≤ N/d at hdiv
        rw [he] at hdiv
        exact mem_Ioc.mpr ⟨hd0,(Nat.le_div_iff_mul_le (by positivity)).mpr
          (by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hdiv)⟩
      have hcard : S.card * 2^j ≤ N :=
        (Nat.le_div_iff_mul_le (by positivity)).mp (by simpa only [Nat.card_Ioc,Nat.sub_zero] using card_le_card hsub)
      calc
        _ ≤ ∑ _d ∈ S, (2:ℝ)^j*b j := sum_le_sum (fun d hd => by
          have h' := h d (mem_filter.mp hd).1
          change v d ≤ (2:ℝ)^(g d)*b (g d) at h'
          rwa [(mem_filter.mp hd).2] at h')
        _ = ((S.card : ℝ)*(2:ℝ)^j)*b j := by simp [mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hb j)
    _ = (N:ℝ)*∑ j ∈ range (N+1), b j := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun j _ => hb j)) (Nat.cast_nonneg _)

theorem solution (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → (ZMod q)ˣ),
      (∑ d ∈ Ioc 0 N, |psi (b d : ZMod q) (N/d) - (N:ℝ)/(d:ℝ)/(q.totient:ℝ)|) ≤ C*(N:ℝ) := by
  classical
  obtain ⟨K,hK,h⟩ := localEnvelope q
  let w := fun j : ℕ => (((j:ℝ)+1)^2)⁻¹
  have hw : Summable w := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1<2)))
  have hwn (j : ℕ) : 0 ≤ w j := by dsimp [w]; positivity
  have htot : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine ⟨(∑' j, K*w j)+1,add_nonneg (tsum_nonneg (fun j => mul_nonneg hK (hwn j))) zero_le_one,fun N b => ?_⟩
  have hb (d : ℕ) (hd : d ∈ Ioc 0 N) := h (b d) (Nat.log 2 (N/d)) (N/d)
    (Nat.pow_log_le_self 2 (Nat.div_pos (mem_Ioc.mp hd).2 (mem_Ioc.mp hd).1).ne')
    (Nat.lt_pow_succ_log_self (by decide : 1<2) _)
  have hs := grouped N (fun d => err (b d) (N/d)) (fun j => K*w j)
    (fun j => mul_nonneg hK (hwn j)) (hw.mul_left K) (fun d hd => (hb d hd).trans_eq (by dsimp [w];ring))
  have ha (d : ℕ) (hd : d ∈ Ioc 0 N) :
      |psi (b d : ZMod q) (N/d) - (N:ℝ)/d/q.totient| ≤ err (b d) (N/d)+1 := by
    have hd0 := (mem_Ioc.mp hd).1
    have hdp : (0:ℝ) < d := by exact_mod_cast hd0
    have lo : ((N/d : ℕ):ℝ) ≤ (N:ℝ)/d := Nat.cast_div_le
    have hi : (N:ℝ)/d ≤ ((N/d : ℕ):ℝ)+1 := (div_le_iff₀ hdp).mpr (by
      have hh' := (Nat.div_lt_iff_lt_mul hd0).mp (Nat.lt_succ_self (N/d))
      exact_mod_cast hh'.le)
    let m := ((N/d : ℕ):ℝ)+1
    have hdiff : |m/(q.totient:ℝ)-((N:ℝ)/d)/(q.totient:ℝ)| ≤ 1 := by
      rw [← sub_div,abs_div,abs_of_nonneg (by dsimp [m]; linarith only [hi]),abs_of_nonneg (Nat.cast_nonneg _)]
      exact (div_le_one₀ (by linarith : (0:ℝ)<q.totient)).mpr (by dsimp [m];linarith only [lo,htot])
    exact (abs_sub_le _ (m/(q.totient:ℝ)) _).trans (add_le_add le_rfl hdiff)
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, (err (b d) (N/d)+1) := sum_le_sum ha
    _ = (∑ d ∈ Ioc 0 N, err (b d) (N/d))+(N:ℝ) := by simp [sum_add_distrib]
    _ ≤ _ := by linarith only [hs]
