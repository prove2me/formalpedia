-- Prove2me | solution 1 for DetDLP.terminal_digit_query_size_and_count
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T19:41:23.034238+00:00
-- url     : https://prove2.me/submissions/38273004-89b2-4e23-9b6c-755d54ad370a

import Definitions.Def_DetDLP_FactorBase

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

section
namespace DetDLP.DigitQueryBudget
theorem depth_power (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
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

theorem sixtyfour_id : (64:ℝ)=(32:ℝ)^(6/5:ℝ) := by
  rw [show (32:ℝ)=(2:ℝ)^5 by norm_num,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num

noncomputable def growth (C : ℕ) : ℝ := 16*C+(512*(C:ℝ))^(6/5:ℝ)
theorem vertices (C L m : ℕ) (hl : 1≤L) (hm : 0 < m) (mb : (m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ)) :
    ((4*m+64^Nat.clog 32 (4*m):ℕ):ℝ) ≤ growth C*(L:ℝ)^(3/10:ℝ) := by
  have hl' : (1:ℝ)≤L := by exact_mod_cast hl
  have fine := Real.rpow_le_rpow_of_exponent_le hl' (by norm_num : (1/4:ℝ) ≤ 3/10)
  have a := mul_le_mul_of_nonneg_left mb (by norm_num : (0:ℝ)≤4)
  have b := mul_le_mul_of_nonneg_left fine (show 0≤16*(C:ℝ) by positivity)
  have small : 4*(m:ℝ) ≤ 16*C*(L:ℝ)^(3/10:ℝ) := by linarith only [a,b]
  have d := depth_power m hm (6/5) (by norm_num)
  rw [←sixtyfour_id] at d
  have s : 128*(m:ℝ) ≤ (512*C)*(L:ℝ)^(1/4:ℝ) := by linarith only [mb]
  have t := Real.rpow_le_rpow (by positivity : 0≤128*(m:ℝ)) s (by norm_num : (0:ℝ)≤6/5)
  rw [Real.mul_rpow (show 0 ≤ 512*(C:ℝ) by positivity) (by positivity),←Real.rpow_mul (Nat.cast_nonneg L)] at t
  norm_num at t
  unfold growth
  push_cast
  rw [add_mul]
  exact add_le_add small (d.trans t)
theorem guard_log (S m p : ℕ) (L : ℕ) (hl : 2≤L) (hs : S≤2^L) (hm : 4*m ≤ 2*S) (hp : p≤S) :
    let D := Nat.clog 32 (4*m)
    let g := 64*(S+1)*(L+1)*2^L*64^D
    p+g+1 ≤ 2^(16*L) := by
  intro D g
  have inc : 2*2^L ≤ 32^L := by
    calc
      _ = 2^(L+1) := by rw [pow_succ]; ring
      _ ≤ 2^(5*L) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have dd : D≤L := Nat.clog_le_of_le_pow (hm.trans ((Nat.mul_le_mul_left 2 hs).trans inc))
  have d64 : 64^D ≤ 2^(6*L) := calc
    _ ≤ 64^L := Nat.pow_le_pow_right (by decide) dd
    _ = _ := by rw [show (64:ℕ)=2^6 by decide,←pow_mul]
  have lsize : L+1≤2^L := Nat.lt_two_pow_self
  have sp : S+1≤2^(L+1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n:=L); omega
  have gg := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 64 sp) lsize) (Nat.le_refl (2^L))) d64
  have ge : g ≤ 2^(9*L+7) := by
    apply gg.trans_eq
    rw [show (64:ℕ)=2^6 by decide,←pow_add,←pow_add,←pow_add,←pow_add]
    congr 1; omega
  have main : S+1 ≤ 2^(9*L+7) := sp.trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ 2^(9*L+7)+2^(9*L+7) := by omega
    _ = 2^(9*L+7+1) := by rw [pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
theorem tuple_count (C L m n q h : ℕ) (hl : 2 ≤ L) (hm : 0 < m) (hn : n ≤ 4*m+64^Nat.clog 32 (4*m))
    (mb : (m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ)) (hq : q+1 ≤ 2^(16*L)) :
    (((q/h+1)^n:ℕ):ℝ) ≤ Real.exp ((16*Real.log 2*growth C)*(L:ℝ)^(13/10:ℝ)) := by
  have vc : (n:ℝ) ≤ growth C*(L:ℝ)^(3/10:ℝ) :=
    (show (n:ℝ) ≤ ((4*m+64^Nat.clog 32 (4*m):ℕ):ℝ) by exact_mod_cast hn).trans (vertices C L m (by omega) hm mb)
  have hJ := (Nat.add_le_add_right (Nat.div_le_self q h) 1).trans hq
  have count : (q/h+1)^n ≤ 2^(16*L*n) := (Nat.pow_le_pow_left hJ n).trans_eq (pow_mul ..).symm
  have e := mul_le_mul_of_nonneg_left vc (show 0 ≤ 16*Real.log 2*(L:ℝ) by positivity)
  calc
    _ ≤ (2:ℝ)^(16*L*n) := by exact_mod_cast count
    _ = Real.exp (Real.log 2*((16*L*n:ℕ):ℝ)) := by
      rw [mul_comm (Real.log 2) _,Real.exp_nat_mul,Real.exp_log (by norm_num : 0 < (2:ℝ))]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have xx : (L:ℝ)*(L:ℝ)^(3/10:ℝ)=(L:ℝ)^(13/10:ℝ) := by
        nth_rw 1 [←Real.rpow_one (L:ℝ)]
        rw [←Real.rpow_add (by exact_mod_cast (show 0 < L by omega))]
        norm_num
      push_cast; rw [←xx]; linarith only [e]
theorem quartic (L : ℕ) (big : 24 ≤ L) : L^4 ≤ 2^(L-1) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le big
  clear big
  induction u with
  | zero => decide
  | succ u ih =>
    rw [show 24+(u+1)-1=(24+u-1)+1 by omega,pow_succ]
    apply le_trans _ (Nat.mul_le_mul_right 2 ih)
    nlinarith [Nat.zero_le (u^4),Nat.zero_le (u^3),Nat.zero_le (u^2)]
theorem linear_inputs (C A B L S m b n ell edges : ℕ)
    (hl : 24 ≤ L) (hs : 2 ≤ S) (logS : L=Nat.clog 2 S)
    (mb : m ≤ 4*C*L) (sb : S ≤ C*m*b) (nv : n ≤ A*L) (length : ell ≤ B*L)
    (edge : edges ≤ C*b) (hb : 0 < b) :
    let h := max 1 (edges/(n+1))
    let P := edges+n*h+n*Nat.clog 2 (4*L*ell)+2
    let ell' := (n*(4*L-1)+1)*ell
    let F := 4*C^2
    P ≤ (2*C+A*F+4*A*B*F+2)*b ∧ ell' ≤ ((4*A+1)*B*F)*b ∧ n ≤ A*F*b := by
  intro h P ell' F
  have cubic : L^3 ≤ F*b := by
    apply Nat.le_of_mul_le_mul_left (c:=L) _ (by omega)
    calc
      L*L^3 = L^4 := by ring
      _ ≤ 2^(L-1) := quartic L hl
      _ ≤ S := by rw [logS]; exact (Nat.pow_pred_clog_lt_self (by decide) hs).le
      _ ≤ C*m*b := sb
      _ ≤ C*(4*C*L)*b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ mb)
      _ = L*(F*b) := by dsimp only [F]; ring
  have base : 1 ≤ L := by omega
  have l3 : L ≤ L^3 := (Nat.le_self_pow (by decide) _)
  have ncap : n ≤ A*F*b := by
    apply nv.trans
    exact (Nat.mul_le_mul_left A (l3.trans cubic)).trans_eq (by ring)
  have cl : Nat.clog 2 (4*L*ell) ≤ 4*L*ell := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have ndig : n*h ≤ n+edges := by
    by_cases z : edges/(n+1)=0
    · simp [h,z]
    · have hh : h=edges/(n+1) := max_eq_right (Nat.one_le_iff_ne_zero.mpr z)
      rw [hh]
      have hm := Nat.div_mul_le_self edges (n+1)
      rw [Nat.mul_add,Nat.mul_one] at hm
      rw [Nat.mul_comm]; omega
  have lc : n*Nat.clog 2 (4*L*ell) ≤ (4*A*B*F)*b := calc
    _ ≤ (A*L)*(4*L*(B*L)) := Nat.mul_le_mul nv (cl.trans (Nat.mul_le_mul_left _ length))
    _ = (4*A*B)*L^3 := by ring
    _ ≤ (4*A*B)*(F*b) := Nat.mul_le_mul_left _ cubic
    _ = _ := by ring
  have first : P ≤ (2*C+A*F+4*A*B*F+2)*b := by
    dsimp only [P]; rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
    rw [Nat.mul_assoc 2 C]; omega
  have small : 1 ≤ L*L := Nat.mul_pos (by omega) (by omega)
  have f : n*(4*L-1)+1 ≤ (4*A+1)*(L*L) := calc
    _ ≤ (A*L)*(4*L)+L*L := Nat.add_le_add (Nat.mul_le_mul nv (Nat.sub_le ..)) small
    _ = _ := by ring
  have len : ell' ≤ ((4*A+1)*B*F)*b := calc
    _ ≤ ((4*A+1)*(L*L))*(B*L) := Nat.mul_le_mul f length
    _ = ((4*A+1)*B)*L^3 := by ring
    _ ≤ ((4*A+1)*B)*(F*b) := Nat.mul_le_mul_left _ cubic
    _ = _ := by ring
  exact ⟨first,len,ncap⟩
theorem full (C : ℕ) : ∃ (K e : ℕ) (c : ℝ),0 ≤ c ∧
    ∀ (S m b p ell edges n : ℕ),let L := Nat.clog 2 S
      let D := Nat.clog 32 (4*m)
      let q := p+64*(S+1)*(L+1)*2^L*64^D
      let h := max 1 (edges/(n+1))
      24+2*C ≤ L → 2 ≤ b → 0 < m → 0 < ell → 2 ≤ S → 4*m ≤ 2*S → b ≤ 2*C*S →
      m ≤ C*blockCount b → S ≤ C*m*b → edges ≤ C*b → ell ≤ C*m → p ≤ S →
      n ≤ 4*m+64^D →
      1 ≤ edges+n*h+n*Nat.clog 2 (4*L*ell)+2 ∧ edges+n*h+n*Nat.clog 2 (4*L*ell)+2 ≤ K*b ∧
      1 ≤ (n*(4*L-1)+1)*ell ∧ (n*(4*L-1)+1)*ell ≤ K*b ∧ n ≤ b^e ∧
      (((q/h+1)^n:ℕ):ℝ) ≤ Real.exp (c*(L:ℝ)^(13/10:ℝ)) := by
  let A := Nat.ceil (growth C)
  let B := 4*C^2
  let K := 2*C+A*B+4*A*B*B+2+(4*A+1)*B*B
  have pos : 0 ≤ growth C := by unfold growth; positivity
  refine ⟨K,A*B+1,16*Real.log 2*growth C,by positivity,?_⟩
  intro S m b p ell edges n L D q h large hb hm he hs mS mass blocks sb eb lell hp hn
  have lo : 1 ≤ L := by omega
  have rl : (1:ℝ)≤L := by exact_mod_cast lo
  have mb := TerminalBlockEstimate.blocks S b C m hs mass (by change 2*C+2 ≤ L; omega) blocks
  change (m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ) at mb
  have mL : m ≤ 4*C*L := by
    exact_mod_cast mb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le rl (by norm_num)) (by positivity))
  have nL : n ≤ A*L := by
    have n0 : (n:ℝ)≤growth C*(L:ℝ)^(3/10:ℝ) :=
      (show (n:ℝ)≤((4*m+64^D:ℕ):ℝ) by exact_mod_cast hn).trans (vertices C L m lo hm mb)
    have n1 := n0.trans (mul_le_mul (Nat.le_ceil (growth C)) (Real.rpow_le_self_of_one_le rl (by norm_num)) (by positivity) (Nat.cast_nonneg _))
    exact_mod_cast n1
  have eL : ell ≤ B*L := lell.trans ((Nat.mul_le_mul_left C mL).trans_eq (by dsimp only [B]; ring))
  obtain ⟨smallP,smallL,smallN⟩ := linear_inputs C A B L S m b n ell edges (by omega) hs rfl mL sb nL eL eb (by omega)
  have power : A*B ≤ b^(A*B) := (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left hb _)
  have total := tuple_count C L m n q h (by omega) hm hn mb (guard_log S m p L (by omega) (Nat.le_pow_clog (by decide) S) mS hp)
  refine ⟨by omega,smallP.trans (Nat.mul_le_mul_right _ (by dsimp only [B,K]; omega)),
    Nat.mul_pos (by omega) he,smallL.trans (Nat.mul_le_mul_right _ (by dsimp only [B,K]; omega)),?_,total⟩
  rw [pow_succ]; exact smallN.trans (Nat.mul_le_mul_right _ power)
end DetDLP.DigitQueryBudget
end

open DetDLP

theorem solution (C : ℕ) : ∃ (K e : ℕ) (c : ℝ),0 ≤ c ∧
    ∀ (S m b p ell edges n : ℕ),let L := Nat.clog 2 S
      let D := Nat.clog 32 (4*m)
      let q := p+64*(S+1)*(L+1)*2^L*64^D
      let h := max 1 (edges/(n+1))
      24+2*C ≤ L → 2 ≤ b → 0 < m → 0 < ell → 2 ≤ S → 4*m ≤ 2*S → b ≤ 2*C*S →
      m ≤ C*blockCount b → S ≤ C*m*b → edges ≤ C*b → ell ≤ C*m → p ≤ S →
      n ≤ 4*m+64^D →
      1 ≤ edges+n*h+n*Nat.clog 2 (4*L*ell)+2 ∧ edges+n*h+n*Nat.clog 2 (4*L*ell)+2 ≤ K*b ∧
      1 ≤ (n*(4*L-1)+1)*ell ∧ (n*(4*L-1)+1)*ell ≤ K*b ∧ n ≤ b^e ∧
      (((q/h+1)^n:ℕ):ℝ) ≤ Real.exp (c*(L:ℝ)^(13/10:ℝ)) := by
  exact DigitQueryBudget.full C
