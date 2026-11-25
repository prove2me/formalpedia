-- Prove2me | solution 1 for DetDLP.d4_unroll_tree_bit_budget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:37:19.386073+00:00
-- url     : https://prove2.me/submissions/13e53bd7-435f-4a0d-8cb4-bfc6fa222624

import Definitions.Def_DetDLP_D4UnrollBudget
import Definitions.Def_DetDLP_D4Plan
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
set_option autoImplicit false
open DetDLP DetDLP.D4Plan DetDLP.D3Stopped DetDLP.AppendixD4 DetDLP.D4RankCode DetDLP.D4UnrollBudget
private theorem width_le (S t : ℕ) : width S t ≤ D3Stopped.level S := (Nat.div_le_self ..).trans (Nat.div_le_self ..)
private theorem shift_step (S t : ℕ) : shift S (t+1) = shift S t + 2 * width S (t+1) := by simp [shift,Finset.sum_range_succ,Nat.mul_add]
private theorem shift_init (S : ℕ) : shift S 0 = 2 * width S 0 := by simp [shift]
private theorem shift_mono (S : ℕ) : Monotone (shift S) := monotone_nat_of_le_succ fun t => by rw [shift_step]; omega
private theorem shift_small (S t : ℕ) : 32768 * shift S t ≤ D3Stopped.level S := by
  have h : shift S t + 2 * width S t ≤ 4*(D3Stopped.level S/131072) := by
    induction t with
    | zero => simp [shift_init,width]; omega
    | succ t ih =>
      rw [shift_step]; have h : width S (t+1) = width S t / 2 := by simp only [width,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_assoc]
      rw [h]; omega
  omega
private def sites : ℕ → ℕ | 0 => 0 | k+1 => 1+64*sites k
private theorem site_lt (k : ℕ) : sites k < 64^k := by induction k with | zero => decide | succ k ih => simp [sites,pow_succ]; omega
private def potential (A q K D : ℕ) (s : ℕ×ℕ) := A*q*sites (D-s.1)+2*K*(2^(D-s.1)-1)*s.2
private def totalP (A q K D : ℕ) (l : List (ℕ×ℕ)) := (l.map (potential A q K D)).sum
private theorem childrenP (A q K D d M : ℕ) (hd : d < D) (f : Fin 64 → ℕ) (hm : ∑ i, f i = 2*M) :
    totalP A q K D (List.ofFn fun g => (d+1,f g)) + (A*q+2*K*M) = potential A q K D (d,M) := by
  let k := D-(d+1)
  have he : D-d=k+1 := by dsimp [k];omega
  simp only [totalP,List.map_ofFn,List.sum_ofFn,Function.comp_apply,potential,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,hm,he]
  change 64*(A*q*sites k)+2*K*(2^k-1)*(2*M)+(A*q+2*K*M) = A*q*sites (k+1)+2*K*(2^(k+1)-1)*M
  have h := Nat.pow_pos (n:=k) (by decide : 0<2)
  have h' : 2^(k+1)-1=2*(2^k-1)+1 := by rw [pow_succ];omega
  rw [h',sites];ring
private theorem work_fits {α : Type} {S D K A q : ℕ} (hq : 0 < q)
    (rad : ∀ d M n : ℕ, d < D → threshold S < M → M ≤ 2^d*S →
      (n:ℝ) ≤ (2^(shift S d+1)*points M (shift S d):ℕ)*Real.exp ((K:ℝ)*M/Real.sqrt (width S d)) →
      Nat.clog 2 n*q ≤ A*q+2*K*M)
    {l : List (ℕ×ℕ)} {t : D4RankCode.Tree α} (w : Work S D K l t) :
    (∀ i∈l, i.2 ≤ 2^i.1*S) → ∀ b, totalP A q K D l ≤ b*q+(q-1) → t.Fits b := by
  induction w with
  | done z => simp [D4RankCode.Tree.Fits]
  | @stop d M l t h w ih =>
    intro bounds b hb; apply ih (fun i hi => bounds _ (List.mem_cons_of_mem _ hi)) b
    simp only [totalP,List.map_cons,List.sum_cons] at hb ⊢; omega
  | @step d M rest n f hd hm count child mass tail ih =>
    intro bounds b hb
    have hx := bounds (d,M) List.mem_cons_self
    have rc := rad d M n hd hm hx count
    have paid : Nat.clog 2 n*q ≤ potential A q K D (d,M) := by
      by_cases hn : Nonempty (Fin n)
      · obtain ⟨i⟩ := hn; have := childrenP A q K D d M hd (child i) (mass i); omega
      · have : n=0 := by by_contra! h; exact hn ⟨⟨0,by omega⟩⟩
        simp [this]
    simp only [totalP,List.map_cons,List.sum_cons] at hb
    have fitsN : Nat.clog 2 n ≤ b := by
      by_contra! h
      have h' := Nat.mul_le_mul_right q (show b+1 ≤ Nat.clog 2 n by omega)
      rw [Nat.add_mul,one_mul] at h';omega
    refine ⟨fitsN, fun i => ih i ?_ _ ?_⟩
    · intro j hj; rcases List.mem_append.mp hj with hj|hj
      · obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hj
        have h' := Finset.single_le_sum (f:=child i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
        rw [mass] at h'
        change child i g ≤ 2^(d+1)*S; rw [pow_succ]; nlinarith only [h',hx]
      · exact bounds _ (List.mem_cons_of_mem _ hj)
    · have hc := childrenP A q K D d M hd (child i) (mass i)
      simp only [totalP,List.map_append,List.sum_append] at hc ⊢
      rw [Nat.sub_mul]; have hr := Nat.mul_le_mul_right q fitsN;omega

private theorem radixBound (S D K d M n : ℕ) (hd : d<D) (hD : D ≤ D3Stopped.level S)
    (hw : 1 ≤ width S D) (hm : M ≤ 2^d*S)
    (cnt : (n:ℝ) ≤ (2^(shift S d+1)*points M (shift S d):ℕ)*Real.exp ((K:ℝ)*M/Real.sqrt (width S d))) :
    Nat.clog 2 n*(max 1 (width S D).sqrt) ≤ 8*(D3Stopped.level S+1)*(max 1 (width S D).sqrt)+2*K*M := by
  let L := D3Stopped.level S; let a := shift S d; let q := max 1 (width S D).sqrt
  have hq : 1 ≤ q := le_max_left ..
  have hq' : q = (width S D).sqrt := max_eq_right (Nat.le_sqrt'.mpr (by simpa using hw))
  have hwd : width S D ≤ width S d := Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hd.le) (by positivity)
  have hqs : (q:ℝ) ≤ Real.sqrt (width S d) := (Real.le_sqrt (by positivity) (by positivity)).2 (by rw [hq',sq]; exact_mod_cast (Nat.sqrt_le _).trans hwd)
  have hLm : M ≤ 2^(2*L) := hm.trans ((Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 1 ≤2) (hd.le.trans hD)) (Nat.le_pow_clog (by decide : 1<2) S)).trans_eq (by rw [←pow_add,two_mul];rfl))
  have ha : a ≤ L := by have := shift_small S d; omega
  have harr : points M a ≤ 2^(2*L+a+2) := calc
    _ ≤ 2^(2*L)*2^(a+1)+1 := by unfold points; exact Nat.add_le_add_right (Nat.mul_le_mul hLm (Nat.sub_le ..)) 1
    _ ≤ _ := by rw [←pow_add,show 2*L+a+2=(2*L+(a+1))+1 by omega,pow_succ]; have := Nat.pow_pos (n:=2*L+(a+1)) (by decide : 0<2);omega
  have full : 2^(a+1)*points M a ≤ 2^(7*(L+1)) := (Nat.mul_le_mul_left _ harr).trans (by rw [←pow_add];apply Nat.pow_le_pow_right (by decide);omega)
  let k := 2*K*M/q+1
  have lt : 2*K*M < k*q := by simpa [k,Nat.mul_comm] using Nat.lt_mul_div_succ (2*K*M) (show 0<q from hq)
  have hlog := Real.log_two_gt_d9
  have hqt : (0:ℝ)<q := by exact_mod_cast hq
  have hkr : 2*(K:ℝ)*M ≤ (k:ℝ)*q := by exact_mod_cast lt.le
  have hex : Real.exp ((K:ℝ)*M/Real.sqrt (width S d)) ≤ (2:ℝ)^k := by
    conv_rhs => rw [←Real.exp_log (by norm_num : (0:ℝ)<2), ←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc _ ≤ (K:ℝ)*M/q := div_le_div_of_nonneg_left (by positivity) hqt hqs
         _ ≤ (k:ℝ)/2 := by apply (div_le_iff₀ hqt).2; linarith
         _ ≤ _ := by nlinarith only [mul_nonneg (Nat.cast_nonneg k) (show 0 ≤ Real.log 2-1/2 by linarith)]
  have hn : n ≤ 2^(7*(L+1)+k) := by
    have h := cnt.trans (mul_le_mul (by exact_mod_cast full : ((2^(a+1)*points M a:ℕ):ℝ) ≤ (2:ℝ)^(7*(L+1))) hex (Real.exp_pos _).le (by positivity))
    rw [←pow_add] at h; exact_mod_cast h
  have h := Nat.mul_le_mul_right q (Nat.clog_le_of_le_pow hn)
  have hdiv := Nat.div_mul_le_self (2*K*M) q
  change Nat.clog 2 n*q ≤ 8*(L+1)*q+2*K*M
  dsimp only [k] at h; rw [Nat.add_mul,Nat.add_mul,one_mul] at h
  nlinarith only [h,hdiv,Nat.le_mul_of_pos_left q (show 1 ≤ L+1 by omega)]


section
namespace DetDLP.TerminalBlockEstimate
abbrev lam := Nat.clog 2
theorem blocks (S b C m : ℕ) (hs : 2 ≤ S) (mass : b ≤ 2*C*S) (hc : 2*C+2 ≤ lam S)
    (blocks : m ≤ C*blockCount b) :
    (m:ℝ) ≤ 4*(C:ℝ)*(lam S:ℝ)^(1/4:ℝ) := by
  let L := lam S
  have scale : b+2 ≤ 2^(2*L) := calc
    _ ≤ (2*C+2)*S := by rw [Nat.add_mul]; omega
    _ ≤ (2^L)*(2^L) := Nat.mul_le_mul (hc.trans (Nat.lt_two_pow_self : L<2^L).le) (Nat.le_pow_clog (by decide) S)
    _ = _ := by rw [←pow_add,two_mul]
  have logN := Nat.clog_le_of_le_pow scale
  let t := (L:ℝ)^(1/4:ℝ)
  have one : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) (by norm_num)
  have cap : ((Nat.clog 2 (b+2):ℕ):ℝ)^(1/4:ℝ) ≤ 2*t := calc
    _ ≤ ((2:ℝ)*L)^(1/4:ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast logN) (by norm_num)
    _ = (2:ℝ)^(1/4:ℝ)*t := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by dsimp [t]; positivity)
  have rounding := Nat.ceil_lt_add_one (show 0 ≤ ((Nat.clog 2 (b+2):ℕ):ℝ)^(1/4:ℝ) by positivity)
  have ma : (blockCount b:ℝ) ≤ 4*t := by unfold blockCount; rw [Nat.cast_max]; apply max_le <;> push_cast <;> linarith
  calc
    _ ≤ (C:ℝ)*(blockCount b:ℝ) := by exact_mod_cast blocks
    _ ≤ (C:ℝ)*(4*t) := mul_le_mul_of_nonneg_left ma (Nat.cast_nonneg _)
    _ = _ := by ring
end DetDLP.TerminalBlockEstimate
end

private theorem depth_power (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    ((32:ℝ)^x)^Nat.clog 32 (4*m)  ≤  (128*(m:ℝ))^x := by
  let d := Nat.clog 32 (4*m)
  have lt := Nat.pow_pred_clog_lt_self (b:=32) (x:=4*m) (by decide) (by omega)
  have pos : 0 < d := by
    by_contra! hz; have hz' : Nat.clog 32 (4*m)=0 := by omega
    have h := Nat.le_pow_clog (b:=32) (by decide) (4*m); rw [hz'] at h; simp at h; omega
  have nat : 32^d  ≤  128*m := calc
    _ = 32^(d-1)*32 := by rw [←pow_succ]; congr 1; omega
    _  ≤  _ := by change 32^(d-1) < 4*m at lt; omega
  have cast : (32:ℝ)^d ≤ 128*(m:ℝ) := by exact_mod_cast nat
  calc
    _ = ((32:ℝ)^d)^x := Real.rpow_pow_comm (by norm_num) _ _
    _  ≤  _ := Real.rpow_le_rpow (by positivity) cast hx

private theorem scale_rate (M S b m lam C A B : ℝ) (hm : 0 ≤ m) (hb : 0 ≤ b) (hl : 0 < lam)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : M ≤ S) (hS : S ≤ C*m*b)
    (block : m ≤ C*lam^(1/4:ℝ)) :
    M*(A/Real.sqrt lam)*(128*m)^(3/10:ℝ)+(B*lam)*(128*m)^(6/5:ℝ)  ≤ 
    (C^2*A*(128*C)^(3/10:ℝ))*(b/lam^(7/40:ℝ))+
    (B*(128*C)^(6/5:ℝ))*lam^(13/10:ℝ) := by
  have hx := mul_le_mul_of_nonneg_left block (by norm_num : (0:ℝ) ≤ 128)
  have eps (x : ℝ) (h : 0 ≤ x) :
      (128*m)^x  ≤  (128*C)^x*lam^((1/4:ℝ)*x) := by
    rw [Real.rpow_mul hl.le,←Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ h
    linarith only [hx]
  have size : M  ≤  C^2*lam^(1/4:ℝ)*b := by
    apply hM.trans; apply hS.trans
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left block hC) hb using 1  <;> ring
  have first := mul_le_mul_of_nonneg_right size (show 0 ≤ A/Real.sqrt lam by positivity)
  have u := mul_le_mul first (eps (3/10) (by norm_num)) (by positivity) (by positivity)
  have v := mul_le_mul_of_nonneg_left (eps (6/5) (by norm_num)) (show 0 ≤ B*lam by positivity)
  refine (add_le_add u v).trans_eq ?_
  rw [Real.sqrt_eq_rpow,div_eq_mul_inv A,div_eq_mul_inv b,←Real.rpow_neg hl.le,←Real.rpow_neg hl.le]
  have one : lam^((1/4:ℝ))*lam^(-(1/2:ℝ))*lam^((1/4:ℝ)*(3/10:ℝ))=lam^(-(7/40:ℝ)) := by
    rw [←Real.rpow_add hl,←Real.rpow_add hl]; norm_num
  have two : lam*lam^((1/4:ℝ)*(6/5:ℝ))=lam^(13/10:ℝ) := by
    nth_rw 1 [←Real.rpow_one lam]; rw [←Real.rpow_add hl]; norm_num
  linear_combination C^2*A*(128*C)^(3/10:ℝ)*b*one + B*(128*C)^(6/5:ℝ)*two
set_option maxHeartbeats 1000000 in
theorem solution (C K : ℕ) (hC : 0<C) : ∃ L₀ Ktot : ℕ, ∀ {c : ℕ} (x : Input C c),
    let L := D3Stopped.level x.S; let D := Nat.clog 32 (4*x.m); let B := budget x.S D K
    L₀ ≤ L → ((B:ℝ) ≤ Ktot*((x.b:ℝ)/(L:ℝ)^(7/40:ℝ)+(L:ℝ)^(13/10:ℝ))) ∧
      ((2:ℝ)^B ≤ Real.exp (Ktot*((x.b:ℝ)/(L:ℝ)^(7/40:ℝ)+(L:ℝ)^(13/10:ℝ)))) ∧
      ∀ {α : Type} {M : ℕ} {t : D4RankCode.Tree α}, M ≤ x.S → Work x.S D K [(0,M)] t → t.Fits B := by
  let C' : ℝ := 4*C
  let A : ℝ := 2048*K
  let F := C'^2*A*(128*C')^(3/10:ℝ)
  let G := 16*(128*C')^(6/5:ℝ)
  refine ⟨(131072*512*C+4)^2,⌈max F G⌉₊,?_⟩
  intro c x L D B big
  have hl : 1 ≤ L := (Nat.one_le_pow _ _ (by omega)).trans big
  have hlr : (1:ℝ) ≤ L := by exact_mod_cast hl
  have hlo : (0:ℝ) < L := by linarith
  have hbnd := (m14a_separator_edge_budget x.spec).1
  have hb : x.b ≤ (2*C)*x.S := x.lower.trans ((Nat.mul_le_mul_left C hbnd).trans_eq (by ring))
  have hS : 2 ≤ x.S := by
    by_contra! h
    have h' : x.S ≤ 2^0 := by simpa using h
    have := Nat.clog_le_of_le_pow h'
    change 1 ≤ Nat.clog 2 x.S at hl;omega
  have block := TerminalBlockEstimate.blocks _ _ _ _ hS hb (by change 2*C+2 ≤ L; nlinarith only [big,hC]) x.mb
  change (x.m:ℝ) ≤ C'*(L:ℝ)^(1/4:ℝ) at block
  have hz := depth_power x.m x.hm 1 (by norm_num); simp only [Real.rpow_one] at hz
  have zd : (2:ℝ)^D ≤ 128*x.m := (pow_le_pow_left₀ (by norm_num) (by norm_num : (2:ℝ) ≤ 32) D).trans hz
  have zsqrt : (2:ℝ)^D ≤ (512*C)*Real.sqrt L := by
    apply zd.trans
    have le := Real.rpow_le_rpow_of_exponent_le hlr (by norm_num : (1:ℝ)/4 ≤ 1/2)
    rw [←Real.sqrt_eq_rpow] at le
    dsimp [C'] at block
    nlinarith only [block,mul_le_mul_of_nonneg_left le (show (0:ℝ)≤4*C by positivity)]
  have hbig : (131072*512*(C:ℝ)+4)^2 ≤ L := by exact_mod_cast big
  have hsqrt : 131072*512*(C:ℝ)+4 ≤ Real.sqrt L := (Real.le_sqrt (by positivity) hlo.le).mpr hbig
  have hw : 1 ≤ width x.S D := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0<2^D)).mpr
    apply (Nat.le_div_iff_mul_le (by decide : 0<131072)).mpr
    change 1*2^D*131072 ≤ L
    have sq := Real.sq_sqrt hlo.le
    have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (L:ℝ))
    exact_mod_cast (show (1:ℝ)*2^D*131072 ≤ L by nlinarith only [zsqrt,hmul,sq,Real.sqrt_nonneg (L:ℝ)])
  have hD : D ≤ L := Nat.lt_two_pow_self.le.trans ((by simpa using (Nat.le_div_iff_mul_le (by positivity : 0<2^D)).mp hw : 2^D ≤ L/131072).trans (Nat.div_le_self ..))
  let q := max 1 (width x.S D).sqrt
  have hq : 1 ≤ q := le_max_left ..
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hwq : width x.S D + 1 ≤ 4*q^2 := by
    have ht := Nat.lt_succ_sqrt' (width x.S D); have hle : (width x.S D).sqrt ≤ q := le_max_right ..
    nlinarith only [ht, Nat.pow_le_pow_left hle 2,hle,hq,Nat.le_mul_of_pos_left q hq]
  have hfloor : L < (width x.S D+1)*(131072*2^D) := by
    rw [width,Nat.div_div_eq_div_mul]; simpa [Nat.mul_comm] using Nat.lt_mul_div_succ L (by positivity : 0<131072*2^D)
  have hLL : L ≤ 1024^2*q^2*(2^D) := (hfloor.le.trans (Nat.mul_le_mul_right _ hwq)).trans (by ring_nf;omega)
  have hroot : Real.sqrt L ≤ 1024*q*Real.sqrt ((2:ℝ)^D) := by
    apply (Real.sqrt_le_iff).mpr; constructor
    · positivity
    · rw [mul_pow,Real.sq_sqrt (by positivity)]
      convert (show (L:ℝ) ≤ 1024^2*(q:ℝ)^2*(2:ℝ)^D by exact_mod_cast hLL) using 1 <;> ring
  have eq2 : (32:ℝ)^(1/5:ℝ)=2 := by rw [show (32:ℝ)=(2:ℝ)^5 by norm_num,←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]; norm_num
  have depthM : (2:ℝ)^D*Real.sqrt ((2:ℝ)^D) ≤ (128*x.m:ℝ)^(3/10:ℝ) := by
    have rt : ((32:ℝ)^(1/10:ℝ))^D=Real.sqrt ((2:ℝ)^D) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_pow_comm (by norm_num),←eq2,←Real.rpow_mul (by norm_num)];norm_num
    rw [←rt,←mul_pow,←eq2,←Real.rpow_add (by norm_num : (0:ℝ)<32)]
    convert depth_power x.m x.hm (3/10) (by norm_num) using 1 <;> norm_num [D]
  have depthN : (64:ℝ)^D ≤ (128*x.m:ℝ)^(6/5:ℝ) := by
    convert depth_power x.m x.hm (6/5) (by norm_num) using 2
    rw [show (32:ℝ)=(2:ℝ)^5 by norm_num,←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)];norm_num
  have massBudget : ((2*K*(2^D-1)*x.S/q:ℕ):ℝ) ≤ (x.S:ℝ)*(A/Real.sqrt L)*(128*x.m:ℝ)^(3/10:ℝ) := by
    apply (Nat.cast_div_le ..).trans
    have hnat : 2*K*(2^D-1)*x.S ≤ 2*K*2^D*x.S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le ..))
    have bound : ((2*K*(2^D-1)*x.S:ℕ):ℝ) ≤ 2*(K:ℝ)*2^D*x.S := by exact_mod_cast hnat
    have hsq : 0 < Real.sqrt L := Real.sqrt_pos.2 hlo
    apply (div_le_iff₀ hqR).mpr
    dsimp only [A] at *
    have hp := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(K:ℝ)*2^D*x.S by positivity)
    have hz' := mul_le_mul_of_nonneg_left depthM (show 0 ≤ (x.S:ℝ)*(2048*K)*q by positivity)
    field_simp [hsq.ne']
    nlinarith only [mul_le_mul_of_nonneg_right bound hsq.le,hp,hz']
  have hcost : (B:ℝ) ≤ (x.S:ℝ)*(A/Real.sqrt L)*(128*x.m:ℝ)^(3/10:ℝ)+(16*(L:ℝ))*(128*x.m:ℝ)^(6/5:ℝ) := by
    change ((8*(L+1)*64^D+_:ℕ):ℝ) ≤ _
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_one]
    have hsite := mul_le_mul (show 8*((L:ℝ)+1) ≤ 16*L by linarith) depthN (by positivity) (by positivity)
    linarith only [massBudget,hsite]
  have Cpos : 0 ≤ C' := by dsimp [C'];positivity
  have hmass : (x.S:ℝ) ≤ C'*x.m*x.b := (by exact_mod_cast x.hS : (x.S:ℝ) ≤ C*x.m*x.b).trans (by dsimp [C']; nlinarith only [show 0 ≤ (C:ℝ)*x.m*x.b by positivity])
  have rate := scale_rate (x.S:ℝ) x.S x.b x.m L C' A 16 (by positivity) (by positivity) hlo Cpos (by dsimp [A];positivity) (by norm_num) le_rfl hmass block
  have Fbound : F ≤ (⌈max F G⌉₊:ℝ) := (le_max_left ..).trans (Nat.le_ceil _)
  have Gbound : G ≤ (⌈max F G⌉₊:ℝ) := (le_max_right ..).trans (Nat.le_ceil _)
  have final := hcost.trans (rate.trans ((add_le_add (mul_le_mul_of_nonneg_right Fbound (show 0 ≤ (x.b:ℝ)/(L:ℝ)^(7/40:ℝ) by positivity)) (mul_le_mul_of_nonneg_right Gbound (show 0 ≤ (L:ℝ)^(13/10:ℝ) by positivity))).trans_eq (mul_add ..).symm))
  refine ⟨final,?_,?_⟩
  · conv_lhs => rw [←Real.exp_log (by norm_num : (0:ℝ)<2),←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr; apply le_trans _ final; nlinarith only [mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9]) (Nat.cast_nonneg B)]
  · intro α M t hm w
    apply work_fits (A:=8*(L+1)) (q:=q) hq (fun d M n hd _ hm hc => radixBound _ _ _ _ _ _ hd hD hw hm hc) w
    · intro i hi; simp only [List.mem_singleton] at hi;subst i;simpa using hm
    · have hs := (site_lt D).le
      have hrem := Nat.mod_lt (2*K*(2^D-1)*x.S) hq
      have hdiv := Nat.mod_add_div (2*K*(2^D-1)*x.S) q
      change totalP _ _ _ _ _ ≤ budget _ _ _*q+(q-1)
      simp only [totalP,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,potential,Nat.sub_zero,budget]
      change 8*(L+1)*q*sites D+2*K*(2^D-1)*M ≤ (8*(L+1)*64^D+2*K*(2^D-1)*x.S/q)*q+(q-1)
      have remle : 2*K*(2^D-1)*x.S % q ≤ q-1 := by omega
      nlinarith only [Nat.mul_le_mul_left (8*(L+1)*q) hs,Nat.mul_le_mul_left (2*K*(2^D-1)) hm,hdiv,remle]
