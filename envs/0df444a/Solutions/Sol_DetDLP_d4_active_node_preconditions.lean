-- Prove2me | solution 1 for DetDLP.d4_active_node_preconditions
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:29:17.478451+00:00
-- url     : https://prove2.me/submissions/be6faa81-520c-4636-a96d-20d182e9deac

import Definitions.Def_DetDLP_D3StoppedSchedule
import Definitions.Def_DetDLP_D4Plan
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
set_option autoImplicit false
namespace DetDLP.D3Stopped
open AppendixD4 Filter
private theorem width_le (S t : ℕ) : width S t ≤ level S := (Nat.div_le_self ..).trans (Nat.div_le_self ..)
private theorem shift_step (S t : ℕ) : shift S (t+1) = shift S t + 2 * width S (t+1) := by simp [shift,Finset.sum_range_succ,Nat.mul_add]
private theorem shift_init (S : ℕ) : shift S 0 = 2 * width S 0 := by simp [shift]
private theorem shift_mono (S : ℕ) : Monotone (shift S) := monotone_nat_of_le_succ fun t => by rw [shift_step]; omega
private theorem shift_small (S t : ℕ) : 32768 * shift S t ≤ level S := by
  have h : shift S t + 2 * width S t ≤ 4*(level S/131072) := by
    induction t with
    | zero => simp [shift_init,width]; omega
    | succ t ih =>
      rw [shift_step]; have h : width S (t+1) = width S t / 2 := by simp only [width,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_assoc]
      rw [h]; omega
  omega
private theorem grow : ∃ R : ℕ, ∀ r ≥ R, r^16 ≤ 2^r := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 16 (show (1:ℝ)<2 by norm_num)).bound (show (0:ℝ)<1 by norm_num)
  obtain ⟨R,hR⟩ := eventually_atTop.1 h
  refine ⟨R,fun r hr => ?_⟩
  have hv := hR r hr
  simp only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (r:ℝ)^16 by positivity),abs_of_nonneg (show (0:ℝ) ≤ 2^r by positivity), one_mul] at hv
  exact_mod_cast hv
private def prev (S t : ℕ) := if t = 0 then 0 else shift S (t-1)
private theorem prev_add (S t : ℕ) : shift S t = prev S t + 2*width S t := by cases t <;> simp [prev,shift_step,shift_init]
private theorem prev_mono (S : ℕ) : Monotone (prev S) := by
  intro t v h; cases t with
  | zero => simp [prev]
  | succ t => cases v with
    | zero => omega
    | succ v => simpa [prev] using shift_mono S (show t ≤ v by omega)
private theorem width_big {C S t : ℕ} (hC : 1 ≤ C) (hr : 131072^2*C ≤ (level S).sqrt)
    (ht : t < depth C S) : (level S).sqrt ≤ width S t := by
  let r := (level S).sqrt
  let k := 2^t
  have h1 : 1 ≤ r := by dsimp [r]; omega
  have hk : 1 ≤ k := Nat.pow_pos (by decide)
  have hp := (Nat.lt_clog_iff_pow_lt (by decide : 1<8)).mp ht
  change 8^t < C*max 1 r at hp; rw [max_eq_right h1] at hp
  have hc : k*(k*k) < C*r := by simpa only [k,← mul_pow,show 2*(2*2)=8 by decide] using hp
  have H : 131072*k ≤ r := by
    by_cases hh : 131072*C ≤ k*k
    · have := Nat.mul_le_mul_left k hh
      by_contra! h; have := Nat.mul_le_mul_left C h.le; nlinarith
    · have : k ≤ k*k := by nlinarith
      change 131072^2*C ≤ r at hr; omega
  apply (Nat.le_div_iff_mul_le (by positivity : 0<2^t)).2
  apply (Nat.le_div_iff_mul_le (by decide : 0<131072)).2
  have := Nat.mul_le_mul_left r H
  have hh := Nat.sqrt_le (level S); change r*r ≤ level S at hh
  change r*k*131072 ≤ level S; nlinarith
private theorem ceil_thresh {S : ℕ} (hr : 1 ≤ (level S).sqrt) : S ≤ threshold S * (level S).sqrt := by
  let r := (level S).sqrt
  have h := Nat.lt_mul_div_succ (S+r-1) (show 0<r from hr)
  change S ≤ (S+r-1)/max 1 r*r; rw [max_eq_right (show 1 ≤ r from hr)]
  rw [Nat.mul_succ,Nat.mul_comm r _] at h; omega
private theorem mult_bound {m u : ℕ} (hu : 1 ≤ u) (hm : u ≤ m) : mult m u * u ≤ 4*m := by
  exact (Nat.div_mul_le_self ..).trans (by omega)
private theorem inc_coarse {m a u : ℕ} (hu : 1 ≤ u) : increase m a u 0 ≤ 40*(m+1)*(a+1)*2^a := by
  have h : mult m u ≤ 3*m+1 := by
    apply Nat.le_of_lt_succ; apply (Nat.div_lt_iff_lt_mul hu).2
    have hh := Nat.mul_le_mul_left (3*m+1) hu
    have hh' : (3*m+2)*u = (3*m+1)*u+u := by ring
    change 3*m+u-1 < (3*m+2)*u; omega
  have ha : 1 ≤ 2^a := Nat.pow_pos (by decide)
  unfold increase tileScale; simp only [Nat.sub_zero]
  calc _ ≤ 8*(3*m+1)*2^a+8*m*(a+1)*2^a := Nat.add_le_add (by gcongr) (Nat.le_mul_of_pos_right _ ha)
       _ ≤ _ := by ring_nf; nlinarith [Nat.mul_le_mul_left (2^a) (Nat.zero_le (m*a))]

private theorem prec_bound {C S M d₀ P : ℕ} (s : Schedule) (hs : s = schedule C S M d₀)
    (_hC : 1 ≤ C) (hS : 1 ≤ S) (hR : max 256 C ≤ (level S).sqrt)
    (hg : (level S).sqrt^16 ≤ 2^(level S).sqrt)
    (hp : P ≤ S + 80*C*S*2^(prev S d₀)) (d : Fin s.D) (m : ℕ)
    (hm : S ≤ m*(level S).sqrt) (hu : (level S).sqrt ≤ s.u d) (hum : s.u d ≤ m)
    (hall : ∀ t : Fin s.D, 1 ≤ s.u t) (i : ℕ) (hi : i < s.u d) :
    (inherited s (C*S) P d.val + increase m (s.a d) (s.u d) i)*s.u d ≤ 34*m*tileScale (s.a d) i := by
  let r := (level S).sqrt; let L := level S
  let u := s.u d; let a := s.a d; let g := prev S (d₀+d.val)
  have hr : 256 ≤ r := (le_max_left ..).trans hR
  have hc : C ≤ r := (le_max_right ..).trans hR
  have hl : L ≤ 4*r^2 := by have := Nat.lt_succ_sqrt' L; change L < (r+1)^2 at this; nlinarith
  have hD : s.D ≤ r^2 := by
    rw [hs]; change (if M ≤ threshold S then 0 else depth C S - d₀) ≤ _
    split; omega
    apply (Nat.sub_le ..).trans
    change Nat.clog 8 (C*max 1 r) ≤ _; rw [max_eq_right (show 1 ≤ r by omega)]
    exact (Nat.clog_le_of_le_pow (Nat.lt_pow_self (n:=C*r) (by decide : 1<8)).le).trans (by nlinarith [Nat.mul_le_mul_right r hc])
  have hsl (t : Fin s.D) : s.a t ≤ L := by subst s; exact le_trans (by omega : shift S (d₀+t.val) ≤ 32768*shift S (d₀+t.val)) (shift_small ..)
  have hul : u ≤ L := by dsimp [u]; subst s; exact width_le ..
  have htile : 2^g * 2^r ≤ tileScale a i := by
    rw [← pow_add]; apply Nat.pow_le_pow_right (by decide)
    have he : a = g + 2*u := by dsimp [a,g,u]; subst s; apply prev_add
    change r ≤ u at hu; change i < u at hi; omega
  have hterm (t : Fin s.D) : (if t.val < d.val then increase (C*S / 8^(s.start+t.val)) (s.a t) (s.u t) 0 else 0) ≤ 40*((C+1)*S)*(L+1)*2^g := by
    split_ifs with ht
    · apply (inc_coarse (m := C*S/8^(s.start+t.val)) (a:=s.a t) (hall t)).trans
      have hx := Nat.div_le_self (C*S) (8^(s.start+t.val))
      have hprev : s.a t ≤ g := by dsimp [g]; subst s; change shift S (d₀+t.val) ≤ prev S (d₀+d.val); unfold prev; rw [if_neg (by omega)]; apply shift_mono; omega
      have hmass : C*S/8^(s.start+t.val)+1 ≤ (C+1)*S := by nlinarith
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 40 hmass) (Nat.succ_le_succ (hsl t))) (Nat.pow_le_pow_right (by decide) hprev)
    · omega
  have hI : inherited s (C*S) P d.val ≤ (1+80*C+40*s.D*(C+1)*(L+1))*S*2^g := by
    have hsum := Finset.sum_le_sum (s:=Finset.univ) fun t _ => hterm t
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hprev := prev_mono S (show d₀ ≤ d₀+d.val by omega)
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hprev
    have hpos : 1 ≤ 2^g := Nat.pow_pos (by decide)
    unfold inherited
    calc _ ≤ S+80*C*S*2^g+s.D*(40*((C+1)*S)*(L+1)*2^g) := Nat.add_le_add (hp.trans (by dsimp [g]; gcongr)) hsum
         _ ≤ _ := by nlinarith [Nat.mul_le_mul_left S hpos]
  have hcoef : (1+80*C+40*s.D*(C+1)*(L+1))*r*u ≤ r^16 := by
    calc _ ≤ (1+80*r+40*r^2*(r+1)*(4*r^2+1))*r*(4*r^2) := by gcongr; exact hul.trans hl
         _ ≤ 2000*r^8 := by nlinarith [show r^7 ≤ r^8 by exact Nat.pow_le_pow_right (by omega) (by decide),show r^6 ≤ r^8 by exact Nat.pow_le_pow_right (by omega) (by decide),show r^5 ≤ r^8 by exact Nat.pow_le_pow_right (by omega) (by decide),show r^4 ≤ r^8 by exact Nat.pow_le_pow_right (by omega) (by decide),show r^3 ≤ r^8 by exact Nat.pow_le_pow_right (by omega) (by decide)]
         _ ≤ _ := by have h : 2000 ≤ r^8 := (by norm_num : 2000 ≤ 256^8).trans (Nat.pow_le_pow_left hr _); exact (Nat.mul_le_mul_right (r^8) h).trans_eq (by ring)
  have hIu : inherited s (C*S) P d.val * u ≤ m * tileScale a i := calc
    _ ≤ ((1+80*C+40*s.D*(C+1)*(L+1))*(m*r)*2^g)*u := Nat.mul_le_mul_right u (hI.trans (by gcongr))
    _ = m * (2^g * ((1+80*C+40*s.D*(C+1)*(L+1))*r*u)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left m ((Nat.mul_le_mul_left _ (hcoef.trans hg)).trans htile)
  have ha := hsl d
  have hsmall : 8*(a+1)*u ≤ r^16 := by
    calc _ ≤ 8*(4*r^2+1)*(4*r^2) := by gcongr; exact ha.trans hl; exact hul.trans hl
         _ ≤ 160*r^4 := by nlinarith [show r^2 ≤ r^4 by exact Nat.pow_le_pow_right (by omega) (by decide)]
         _ ≤ _ := by have h : 160 ≤ r^12 := (by norm_num : 160 ≤ 256^12).trans (Nat.pow_le_pow_left hr _); exact (Nat.mul_le_mul_right (r^4) h).trans_eq (by ring)
  have hsc : 8*(a+1)*u ≤ tileScale a i := (hsmall.trans hg).trans ((Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0<2))).trans htile)
  have hmu := mult_bound (u:=u) (m:=m) (hall d) hum
  change (_ + increase m a u i)*u ≤ _
  unfold increase; nlinarith [Nat.mul_le_mul_right (tileScale a i) hmu, Nat.mul_le_mul_left m hsc]

private theorem explicitActive (C : ℕ) (hC : 0 < C) :
    ∃ L₀ : ℕ, ∀ (S M P d₀ : ℕ),
      L₀ ≤ level S → threshold S < M → M ≤ C*S/8^d₀ → 1 ≤ P →
      P ≤ S+80*C*S*(if d₀ = 0 then 1 else 2^shift S (d₀-1)) →
      cap S ≤ C*S ∧ 0 < 4*level S ∧ 2^(4*level S) ≤ (S+2)^5 ∧
      Active (schedule C S M d₀) (C*S) P 34 := by
  obtain ⟨R,hR⟩ := grow
  let R₀ := max R (131072^2*C+256)
  refine ⟨R₀^2,?_⟩
  intro S M P d₀ hL hM hmass _ hp
  let L := level S; let r := L.sqrt
  have hr₀ : R₀ ≤ r := Nat.le_sqrt'.2 hL
  have hr : 131072^2*C+256 ≤ r := (le_max_right ..).trans hr₀
  have hLr : r*r ≤ L := Nat.sqrt_le _
  have hCL : C ≤ L := by nlinarith
  have hLarge : 256 ≤ L := by nlinarith
  have hpos : 1 ≤ r := by omega
  have hSbig : 2^(L-1) < S := Nat.pow_lt_of_lt_clog (by omega : L-1 < L)
  have hS : 16 ≤ S := (show 2^4 ≤ 2^(L-1) from Nat.pow_le_pow_right (by decide) (by omega)).trans hSbig.le
  have hSup : S ≤ 2^L := Nat.le_pow_clog (by decide) _
  have hcs : S ≤ C*S := Nat.le_mul_of_pos_left S hC
  have hceil := ceil_thresh (S:=S) hpos
  have hCmass : C*S < (threshold S+1)*r*C := by
    have hh := Nat.mul_le_mul_right C hceil
    have hh' : 0 < r*C := Nat.mul_pos hpos hC
    change S ≤ threshold S*r at hceil
    calc C*S = S*C := Nat.mul_comm ..
         _ ≤ (threshold S*r)*C := hh
         _ < _ := by nlinarith
  have hdepth : d₀ < depth C S := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1<8)).2
    change 8^d₀ < C*max 1 r; rw [max_eq_right hpos]
    by_contra! h
    have hh := (Nat.le_div_iff_mul_le (by positivity)).mp hmass
    have hh' := Nat.mul_le_mul hM (show C*r ≤ 8^d₀ from h)
    nlinarith
  have hlast : C*S/8^(depth C S) ≤ threshold S := by
    apply Nat.le_of_lt_succ; apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    have hh := Nat.le_pow_clog (by decide : 1<8) (C*max 1 r)
    change C*max 1 r ≤ 8^(depth C S) at hh; rw [max_eq_right hpos] at hh
    exact hCmass.trans_le (by rw [Nat.mul_right_comm _ r C,Nat.mul_assoc]; gcongr)
  let s := schedule C S M d₀
  have he : s.start+s.D = depth C S := by change d₀+(if M ≤ threshold S then 0 else _) = _; rw [if_neg (by omega : ¬M ≤ threshold S)]; omega
  have hH : s.H = threshold S := min_eq_right hM.le
  have hdepth' (d : Fin s.D) : d₀+d.val < depth C S := by
    have := d.isLt; change (schedule C S M d₀).start+s.D = _ at he; change d₀+s.D = _ at he; omega
  have hwidth (d : Fin s.D) : r ≤ s.u d := width_big hC (by change 131072^2*C ≤ r; omega) (hdepth' d)
  have hcap : cap S ≤ S := (Nat.pow_le_pow_right (by decide : 1≤2) (by change (9*L+9)/10 ≤ L-1; omega)).trans hSbig.le
  have hκ : 2^(4*L) ≤ (S+2)^5 := by
    have he' : 2^L ≤ 2*S := by rw [show L = (L-1)+1 by omega,pow_succ]; omega
    calc 2^(4*L) = (2^L)^4 := by rw [←pow_mul,Nat.mul_comm]
         _ ≤ (2*S)^4 := by gcongr
         _ ≤ S^5 := by nlinarith [Nat.mul_le_mul_right (S^4) hS]
         _ ≤ _ := by gcongr; omega
  refine ⟨hcap.trans hcs,by change 0<4*L; omega,hκ,?_,?_⟩
  · change C*S/8^(s.start+s.D) ≤ s.H; rw [he,hH]; exact hlast
  · intro d m hlo hhi
    change s.H < m at hlo; rw [hH] at hlo
    have hm : S ≤ m*r := hceil.trans (Nat.mul_le_mul_right r hlo.le)
    have hrpow : r ≤ 2^r := (Nat.lt_pow_self (by decide : 1<2)).le
    have hcrit (e : ℕ) (he' : e+r ≤ L-1) : 2^e ≤ m := by
      have hh : 2^e*r ≤ S := calc
        _ ≤ 2^e*2^r := by gcongr
        _ = 2^(e+r) := (pow_add ..).symm
        _ ≤ 2^(L-1) := Nat.pow_le_pow_right (by decide) he'
        _ ≤ _ := hSbig.le
      exact Nat.le_of_mul_le_mul_right (hh.trans hm) hpos
    let a := s.a d; let u := s.u d
    have ha : 32768*a ≤ L := shift_small S _
    have hau : u ≤ a := by have hh := prev_add S (d₀+d.val); change width S (d₀+d.val) ≤ shift S (d₀+d.val); omega
    have hrL : 100*r ≤ L := by nlinarith
    have huM : u ≤ m := hau.trans ((Nat.lt_pow_self (by decide : 1<2)).le.trans (hcrit a (by omega)))
    refine ⟨hpos.trans (hwidth d),hau,huM,?_,?_,?_,?_,?_⟩
    · change 2*64^(4*a)*cap S ≤ m
      have hh : 2*64^(4*a)*cap S = 2^(1+24*a+(9*L+9)/10) := by
        change 2* (2^6)^(4*a)*2^_ = _; rw [← pow_mul]; simp only [pow_add,pow_one]; congr 2; ring
      rw [hh]; apply hcrit; omega
    · change 2^a*64^(2*a) ≤ m
      have hh : 2^a*64^(2*a) = 2^(13*a) := by change 2^a*(2^6)^(2*a)=_; rw [← pow_mul,← pow_add]; congr 1; ring
      rw [hh]; apply hcrit; omega
    · change 2*2^a ≤ 2^((9*L+9)/10); rw [← Nat.pow_succ']; apply Nat.pow_le_pow_right (by decide); omega
    · change points m a ≤ 2^(4*L)
      have hcL : C ≤ 2^L := hCL.trans (Nat.lt_pow_self (by decide : 1<2)).le
      have hm' : m ≤ 2^(2*L) := hhi.trans ((Nat.div_le_self ..).trans ((Nat.mul_le_mul hcL hSup).trans_eq (by rw [←pow_add]; ring_nf)))
      unfold points
      have hh : 1 ≤ m := by have := hwidth d; change r ≤ u at this; omega
      have ha' : 1 ≤ 2^(a+1) := Nat.pow_pos (by decide)
      calc _ ≤ m*2^(a+1) := (Nat.add_le_add_left hh _).trans_eq (by rw [←Nat.mul_succ]; congr 1; omega)
           _ ≤ 2^(2*L)*2^(a+1) := by gcongr
           _ ≤ _ := by rw [←pow_add]; apply Nat.pow_le_pow_right (by decide); omega
    · intro i hi
      apply prec_bound s rfl hC (by omega) (by change max 256 C ≤ r; omega) (hR r ((le_max_left ..).trans hr₀)) _ d m hm (hwidth d) huM (fun t => hpos.trans (hwidth t)) i hi
      simpa [prev,apply_ite (fun k : ℕ => 2^k)] using hp

private theorem ceil_power (x n j : ℕ) (r : ℝ) (hr : 0 ≤ r) (hx : x ≤ 2^n) (h : (n:ℝ)*r ≤ j) :
    Nat.ceil ((x:ℝ)^r) ≤ 2^j := by
  apply Nat.ceil_le.mpr
  have xx : (x:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hx
  calc
    _ ≤ ((2:ℝ)^n)^r := Real.rpow_le_rpow (Nat.cast_nonneg _) xx hr
    _ = (2:ℝ)^((n:ℝ)*r) := (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2:ℝ)^(j:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = _ := by norm_cast
open DetDLP DetDLP.D4Plan DetDLP.D3Stopped DetDLP.AppendixD4

set_option maxHeartbeats 1600000 in
theorem _root_.solution (C : ℕ) (hC : 0 < C) : ∃ L₀ : ℕ, ∀ {c : ℕ} (x : Input C c) (d M Δ p : ℕ),
    L₀ ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8^d →
    let a := shift x.S d; let u := width x.S d; let last := if d=0 then 0 else shift x.S (d-1)
    Δ ≤ max (C * Nat.ceil ((x.b:ℝ)^((3:ℝ)/4))) (2*2^last) →
    p ≤ x.p+80*x.S*2^last →
    1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2^(4*D3Stopped.level x.S) ∧
    2^a*64^(2*a) ≤ M ∧ (a+2)*64^(4*a)*max 1 Δ ≤ M ∧ max Δ (2*2^a) ≤ cap x.S ∧
    (∀ i < u, p+increase M a u i ≤ 64*M*tileScale a i/u) ∧
    ∀ i, p+increase M a u i ≤ x.p+80*x.S*2^a := by
  obtain ⟨L₁,H⟩ := explicitActive 1 (by decide)
  refine ⟨max L₁ (32*(32+2*C)+131072),?_⟩
  intro c x d M Δ p hl hM hm a u last hΔ hp
  let L := D3Stopped.level x.S
  have hb : x.b ≤ (2*C)*x.S := x.lower.trans ((Nat.mul_le_mul_left C (m14a_separator_edge_budget x.spec).1).trans_eq (by ring))
  let z := L/32
  have hz : 32+2*C ≤ z := by dsimp [z,L]; omega
  have hc : 2*C ≤ 2^z := (by omega : 2*C ≤ z).trans (Nat.lt_two_pow_self.le)
  have hs : x.S ≤ 2^(33*z) := (Nat.le_pow_clog (by decide : 1<2) x.S).trans (Nat.pow_le_pow_right (by decide) (by change L ≤ 33*(L/32); dsimp [z] at hz; omega))
  have hb' : x.b ≤ 2^(34*z) := hb.trans ((Nat.mul_le_mul hc hs).trans_eq (by rw [←pow_add]; congr 1; omega))
  have hbc := ceil_power x.b (34*z) (26*z) (3/4) (by norm_num) hb' (by push_cast; linarith)
  have hbase : C*Nat.ceil ((x.b:ℝ)^((3:ℝ)/4)) ≤ 2^(27*z) := (Nat.mul_le_mul (by omega : C ≤ 2^z) hbc).trans_eq (by rw [←pow_add]; congr 1; omega)
  have hprec : max 1 p ≤ x.S+80*1*x.S*(if d=0 then 1 else 2^shift x.S (d-1)) := by
    have := x.hp; have := x.pS; dsimp [last] at hp; split_ifs at hp ⊢ <;> simp_all only [pow_zero,mul_one] <;> omega
  obtain ⟨_,_,_,hterm,hacts⟩ := H x.S M (max 1 p) d ((le_max_left ..).trans hl) hM (by simpa using hm) (le_max_left ..) hprec
  let s := schedule 1 x.S M d
  have hsH : s.H = threshold x.S := min_eq_right hM.le
  have hd : 0 < s.D := by
    by_contra! he
    have := Nat.eq_zero_of_le_zero he
    change 1*x.S / 8^(d+s.D) ≤ s.H at hterm
    rw [this, Nat.add_zero,one_mul,hsH] at hterm; omega
  let j : Fin s.D := ⟨0, hd⟩
  obtain ⟨hu, hua, hum, _, pad, capA, pts, prec⟩ := hacts j M (by simpa only [←hsH] using hM) (by simpa [j,s,schedule] using hm)
  change 1 ≤ width x.S (d+0) at hu
  simp only [Nat.add_zero] at hu
  change width x.S (d+0) ≤ shift x.S (d+0) at hua
  change width x.S (d+0) ≤ M at hum
  change 2^(shift x.S (d+0))*64^(2*shift x.S (d+0)) ≤ M at pad
  change 2*2^(shift x.S (d+0)) ≤ cap x.S at capA
  change points M (shift x.S (d+0)) ≤ 2^(4*D3Stopped.level x.S) at pts
  simp only [Nat.add_zero] at hua hum pad capA pts
  have ha : 32768*a ≤ L := shift_small ..
  have hadd : a = last+2*u := prev_add ..
  have hd0 : Δ ≤ cap x.S := hΔ.trans (max_le (hbase.trans (Nat.pow_le_pow_right (by decide) (by change 27*(L/32) ≤ (9*L+9)/10; omega))) ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (by omega : last ≤ a))).trans capA))
  have hroom : (a+2)*64^(4*a)*max 1 Δ ≤ M := by
    let r := L.sqrt
    have hr : 256 ≤ r := Nat.le_sqrt'.mpr (by change 256^2 ≤ D3Stopped.level x.S; omega)
    have hcrit (e : ℕ) (he : e+r ≤ L-1) : 2^e ≤ M := by
      have hS := ceil_thresh (S:=x.S) (show 1 ≤ r by omega)
      have hbig : 2^(L-1) < x.S := Nat.pow_lt_of_lt_clog (by change L-1 < L; dsimp [L]; omega)
      apply Nat.le_of_mul_le_mul_right (c:=r) _ (by omega)
      calc 2^e*r ≤ 2^e*2^r := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
           _ = 2^(e+r) := (pow_add ..).symm
           _ ≤ x.S := (Nat.pow_le_pow_right (by decide) he).trans hbig.le
           _ ≤ M*r := hS.trans (Nat.mul_le_mul_right r hM.le)
    have hLr : 100*r ≤ L := by have h := Nat.sqrt_le L; change r*r ≤ L at h; nlinarith
    have hpos : 1 ≤ cap x.S := Nat.pow_pos (by decide)
    calc (a+2)*64^(4*a)*max 1 Δ ≤ 2^(a+2)*64^(4*a)*cap x.S := Nat.mul_le_mul (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le) (max_le hpos hd0)
         _ = 2^(a+2+24*a+(9*L+9)/10) := by change 2^_* (2^6)^(4*a)*2^_ = _; rw [←pow_mul,←pow_add,←pow_add]; congr 1; ring
         _ ≤ M := hcrit _ (by omega)
  refine ⟨hu,hua,hum,x.hl,pts,pad,hroom,max_le hd0 capA,?_,?_⟩
  · intro i hi
    have hh := prec i (by simpa [j,s,schedule] using hi)
    simp [j,s,schedule,inherited] at hh
    apply (Nat.le_div_iff_mul_le hu).2
    change (p+increase M (shift x.S d) (width x.S d) i)*width x.S d ≤ _
    have hpp : p ≤ max 1 p := le_max_right ..
    exact (Nat.mul_le_mul_right (width x.S d) (Nat.add_le_add_right hpp _)).trans (hh.trans (by change 34*M*tileScale a i ≤ 64*M*tileScale a i; gcongr <;> omega))
  · intro i
    have hmult : mult M u ≤ 4*M := (Nat.le_mul_of_pos_right _ hu).trans (mult_bound hu hum)
    have hM' := hm.trans (Nat.div_le_self ..)
    have ht : tileScale a i ≤ 2^a := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    have hadd' : a+1 ≤ 2^a := Nat.lt_two_pow_self
    have hinc : increase M a u i ≤ 40*x.S*2^a := by
      unfold increase
      calc _ ≤ 8*(4*x.S)*2^a+8*x.S*2^a := by gcongr; exact hmult.trans (Nat.mul_le_mul_left 4 hM')
           _ = _ := by ring
    have hprev : 2*2^last ≤ 2^a := by rw [←Nat.pow_succ']; apply Nat.pow_le_pow_right (by decide); omega
    have hstart := Nat.mul_le_mul_left (40*x.S) hprev
    nlinarith only [hp,hinc,hstart]

end DetDLP.D3Stopped
