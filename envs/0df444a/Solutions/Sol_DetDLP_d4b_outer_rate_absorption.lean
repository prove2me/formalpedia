-- Prove2me | solution 1 for DetDLP.d4b_outer_rate_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:53:08.632366+00:00
-- url     : https://prove2.me/submissions/b241e6a8-6052-4d4c-9be9-612f042d4b67

import Definitions.Def_DetDLP_D4Plan
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
set_option autoImplicit false
-- Block, degree and logarithm estimates adapted from accepted submissions
-- 68bba6bc-95cc-4706-8762-1af3f04f70c1 and 923e02d6-1db3-405a-8654-3ee7aafd12a3.
namespace DetDLP.D4BRate
open D4Plan
noncomputable section
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
noncomputable def degree (G : BipartiteMultigraph) (β : ℕ) := max G.maxDeg (Nat.ceil ((β:ℝ)^((9:ℝ)/10)))
noncomputable def scale (G : BipartiteMultigraph) (β : ℕ) :=
  max 1 (Nat.floor (Real.logb 2 ((β:ℝ)/(degree G β:ℝ))))

theorem quartic (L : ℕ) (h : 32 ≤ L) : L^4 ≤ 2^(L-1) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction u with
  | zero => decide
  | succ u ih =>
    rw [show 32+(u+1)-1=(32+u-1)+1 by omega,pow_succ]
    apply le_trans _ (Nat.mul_le_mul_right 2 ih)
    nlinarith only [Nat.zero_le (u^4),Nat.zero_le (u^3),Nat.zero_le (u^2),Nat.zero_le u]
theorem ceiling (S b C m : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ S) (big : 32+2*C ≤ Nat.clog 2 S)
    (mass : b ≤ 2*C*S) (blocks : m ≤ C*blockCount b) (sum : S ≤ C*m*b) :
    Nat.ceil ((b:ℝ)^((9:ℝ)/10))*m ≤ 32*(C+1)^3*b := by
  let L := Nat.clog 2 S
  have hL : 32 ≤ L := by dsimp only [L]; omega
  have mb := DetDLP.D4BRate.blocks S b C m hs mass (by change 2*C+2 ≤ L; omega) blocks
  change (m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ) at mb
  have mL : m ≤ 4*C*L := by
    have gain : (L:ℝ)^(1/4:ℝ) ≤ L := Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ L)) (by norm_num)
    exact_mod_cast mb.trans (mul_le_mul_of_nonneg_left gain (by positivity))
  have poly : L^4 ≤ S := (quartic L hL).trans (Nat.pow_pred_clog_lt_self (by decide) hs).le
  have room : L^3 ≤ (4*(C+1)^2)*b := by
    apply Nat.le_of_mul_le_mul_left (c:=L) _ (by omega)
    calc
      L*L^3 = L^4 := by ring
      _ ≤ C*m*b := poly.trans sum
      _ ≤ C*(4*C*L)*b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ mL)
      _ ≤ _ := by nlinarith only [Nat.zero_le (L*b),Nat.zero_le (C*L*b)]
  let H := 4*((C:ℝ)+1)^2
  have hH : 1 ≤ H := by dsimp only [H]; nlinarith [(Nat.cast_nonneg C : (0:ℝ) ≤ C),sq_nonneg (C:ℝ)]
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  have root : (L:ℝ)^(1/4:ℝ) ≤ H*(b:ℝ)^(1/10:ℝ) := calc
    _ = ((L:ℝ)^3)^(1/12:ℝ) := by rw [←Real.rpow_natCast_mul (Nat.cast_nonneg _)]; norm_num
    _ ≤ (H*b)^(1/12:ℝ) := Real.rpow_le_rpow (by positivity) (by dsimp only [H]; exact_mod_cast room) (by norm_num)
    _ = H^(1/12:ℝ)*(b:ℝ)^(1/12:ℝ) := Real.mul_rpow (by linarith) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul (Real.rpow_le_self_of_one_le hH (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hb' (by norm_num)) (by positivity) (by linarith)
  have cap := Nat.ceil_lt_add_one (show 0 ≤ (b:ℝ)^((9:ℝ)/10) by positivity)
  have one := Real.one_le_rpow hb' (show (0:ℝ) ≤ 9/10 by norm_num)
  have bh : (Nat.ceil ((b:ℝ)^((9:ℝ)/10)):ℝ) ≤ 2*(b:ℝ)^(9/10:ℝ) := by linarith only [cap,one]
  have mh := mb.trans (mul_le_mul_of_nonneg_left root (by positivity))
  have eq : (b:ℝ)^(9/10:ℝ)*(b:ℝ)^(1/10:ℝ)=b := by rw [←Real.rpow_add' (Nat.cast_nonneg _) (by norm_num)]; norm_num
  have finish : (Nat.ceil ((b:ℝ)^((9:ℝ)/10)):ℝ)*m ≤ 32*((C:ℝ)+1)^3*b := calc
    _ ≤ (2*(b:ℝ)^(9/10:ℝ))*(4*C*(H*(b:ℝ)^(1/10:ℝ))) := mul_le_mul bh mh (Nat.cast_nonneg _) (by positivity)
    _ = 8*C*H*b := by calc
        _ = 8*C*H*((b:ℝ)^(9/10:ℝ)*(b:ℝ)^(1/10:ℝ)) := by ring
        _ = _ := by rw [eq]
    _ ≤ _ := by dsimp only [H]; nlinarith only [mul_nonneg (sq_nonneg ((C:ℝ)+1)) (Nat.cast_nonneg b)]
  exact_mod_cast finish

theorem logarithm (G : BipartiteMultigraph) (b m A : ℕ) (hb : 0 < b) (hm : 0 < m)
    (h : degree G b*m ≤ A*b) : logSafe m ≤ ((A:ℝ)+2)*(scale G b:ℝ) := by
  let D := degree G b
  let R := scale G b
  have hr : 1 ≤ R := le_max_left ..
  have hp : (0:ℝ) < b := by exact_mod_cast hb
  have hd : 0 < D := by
    have p := (Real.rpow_pos_of_pos hp ((9:ℝ)/10)).trans_le (Nat.le_ceil _)
    exact (by exact_mod_cast p : 0 < Nat.ceil ((b:ℝ)^((9:ℝ)/10))).trans_le (le_max_right ..)
  have dp : (0:ℝ) < D := by exact_mod_cast hd
  have rat : (b:ℝ)/D < (2:ℝ)^((R:ℝ)+1) := by
    apply (Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos hp dp)).mp
    calc
      _ < ((Nat.floor (Real.logb 2 ((b:ℝ)/D)):ℕ):ℝ)+1 := Nat.lt_floor_add_one _
      _ ≤ _ := by gcongr; exact_mod_cast (le_max_right 1 _ : Nat.floor (Real.logb 2 ((b:ℝ)/D)) ≤ R)
  have ar : (A:ℝ) ≤ (2:ℝ)^A := by exact_mod_cast (Nat.lt_two_pow_self : A<2^A).le
  have ms : (m:ℝ) ≤ (A:ℝ)*((b:ℝ)/D) := by
    rw [←mul_div_assoc,le_div_iff₀ dp,mul_comm (m:ℝ)]
    exact_mod_cast h
  have rate : (m:ℝ) ≤ (2:ℝ)^(((A:ℝ)+2)*R) := calc
    _ ≤ (2:ℝ)^A*((2:ℝ)^((R:ℝ)+1)) := ms.trans (mul_le_mul ar rat.le (by positivity) (by positivity))
    _ = (2:ℝ)^((A:ℝ)+(R:ℝ)+1) := by rw [add_assoc,Real.rpow_add (x:=2) (y:=(A:ℝ)) (by norm_num),Real.rpow_natCast]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have rr : (1:ℝ) ≤ R := by exact_mod_cast hr
      nlinarith [mul_nonneg (Nat.cast_nonneg A) (sub_nonneg.mpr rr)]
  have room : (1:ℝ) ≤ ((A:ℝ)+2)*R := by
    have rr : (1:ℝ) ≤ R := by exact_mod_cast hr
    nlinarith [mul_nonneg (Nat.cast_nonneg A : (0:ℝ) ≤ A) (Nat.cast_nonneg R)]
  apply max_le room
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (lt_max_of_lt_left (by norm_num : (0:ℝ)<2))).mpr
  exact max_le (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) room) rate
theorem exponent (K B b m rho : ℕ) (hr : 1 ≤ rho) (bound : logSafe m ≤ ((B:ℝ)+2)*rho) :
    (K:ℝ)*(b:ℝ)/Real.sqrt (rho:ℝ) ≤ (K:ℝ)*Real.sqrt ((B:ℝ)+2)*((b:ℝ)/Real.sqrt (logSafe m)) := by
  have pos : (0:ℝ)<rho := by exact_mod_cast (by omega : 0 < rho)
  have lm : 0 < logSafe m := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have h := Real.sqrt_le_sqrt bound
  rw [Real.sqrt_mul (by positivity)] at h
  apply (div_le_iff₀ (Real.sqrt_pos.mpr pos)).mpr
  rw [div_eq_mul_inv]
  calc
    _ = (K:ℝ)*b*((Real.sqrt (logSafe m))⁻¹*Real.sqrt (logSafe m)) := by rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr lm).ne',mul_one]
    _ ≤ (K:ℝ)*b*((Real.sqrt (logSafe m))⁻¹*(Real.sqrt ((B:ℝ)+2)*Real.sqrt (rho:ℝ))) := by gcongr
    _ = _ := by ring

variable {C c : ℕ} (x : Input C c)
private theorem log_le_nat {m : ℕ} (hm : 1 ≤ m) : logSafe m ≤ (m:ℝ) := by
  apply max_le (by exact_mod_cast hm)
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (lt_max_of_lt_left (by norm_num : (0:ℝ)<2))).mpr
  rw [Real.rpow_natCast]; apply max_le
  · exact_mod_cast (show 2 ≤ 2^m by exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) hm))
  · exact_mod_cast Nat.lt_two_pow_self.le

theorem params : 2 ≤ x.S ∧ x.b ≤ 2*C*x.S ∧ x.m ≤ x.S ∧ x.m ≤ C*x.b := by
  have he := (m14a_separator_edge_budget x.spec).1
  have hm := x.hm; have hk := x.hk; have hb := x.upper
  have hh := Nat.mul_le_mul_left (4*x.m) hk
  have hz := x.lower.trans (Nat.mul_le_mul_left C he)
  exact ⟨by omega,by nlinarith only [hz],by omega,by omega⟩

def rate := (x.b:ℝ)/x.m+(x.b:ℝ)/Real.sqrt (logSafe x.m)

theorem bounds (hC : 0<C) : ∃ A : ℕ, ∀ x : Input C c,
    ((x.b:ℝ)/(lam x.S:ℝ)^(7/40:ℝ) + (lam x.S:ℝ)^(13/10:ℝ)) ≤ A*rate x ∧
    (∀ (P : Plan x) (u : Fin P.N), (x.b:ℝ)/Real.sqrt (scale (P.R u) x.b) ≤ A*rate x) := by
  let lo := 32+2*C
  let F := 1217*(C+1)^3
  let G := (2^lo+1)^3
  let A := 4*(C+1)^2 + 16*(C+1)^3 + F+2 + G+G + 2
  refine ⟨A,?_⟩; intro x
  let L := lam x.S
  have hb : 0 < x.b := by have := x.hb; omega
  have hm := x.hm
  have pos : (0:ℝ) < x.m := by exact_mod_cast hm
  have B : (0:ℝ) ≤ x.b := Nat.cast_nonneg _
  have h1 : (1:ℝ) ≤ logSafe x.m := le_max_left ..
  have hsqrt := Real.sqrt_le_sqrt (log_le_nat hm)
  have hroot : (0:ℝ) < Real.sqrt (logSafe x.m) := Real.sqrt_pos.mpr (by linarith)
  have r₁ : (x.b:ℝ)/x.m ≤ rate x := by unfold rate; exact le_add_of_nonneg_right (by positivity)
  have r₂ : (x.b:ℝ)/Real.sqrt (logSafe x.m) ≤ rate x := by unfold rate; exact le_add_of_nonneg_left (by positivity)
  have rn : 0 ≤ rate x := (div_nonneg B pos.le).trans r₁
  obtain ⟨hs,hmass,hmS,hmb⟩ := params x
  have hL : 1 ≤ L := by exact Nat.clog_pos (by decide) hs
  have H1 : (1:ℝ) ≤ L := by exact_mod_cast hL
  have lr : (0:ℝ) < L := by linarith
  by_cases big : lo ≤ L
  · have mR := blocks x.S x.b C x.m hs hmass (by change 2*C+2 ≤ L; dsimp [lo] at big; omega) x.mb
    change (x.m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ) at mR
    have sq : Real.sqrt (logSafe x.m) ≤ (4*(C:ℝ)+4)*(L:ℝ)^(7/40:ℝ) := by
      apply hsqrt.trans
      rw [Real.sqrt_eq_rpow]; apply le_trans (Real.rpow_le_rpow pos.le mR (by norm_num : (0:ℝ) ≤ 1/2))
      rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul lr.le]
      apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le H1 (by norm_num)) (by positivity) (by positivity)
      have hc' : (1:ℝ) ≤ C := by exact_mod_cast hC
      exact le_trans (Real.rpow_le_self_of_one_le (by linarith : (1:ℝ) ≤ 4*C) (by norm_num)) (by linarith)
    have first : (x.b:ℝ)/(L:ℝ)^(7/40:ℝ) ≤ (4*(C:ℝ)+4)*rate x := by
      apply le_trans _ (mul_le_mul_of_nonneg_left r₂ (by positivity))
      rw [mul_div_assoc',div_le_div_iff₀ (by positivity) hroot]; nlinarith only [mul_le_mul_of_nonneg_left sq B]
    have mL : (x.m:ℝ) ≤ 4*C*L := mR.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le H1 (by norm_num)) (by positivity))
    have Q := (quartic L (by dsimp [lo] at big; omega)).trans (Nat.pow_pred_clog_lt_self (by decide) hs).le
    have q' : (L:ℝ)^4 ≤ C*x.m*x.b := by exact_mod_cast Q.trans x.hS
    have cb : (0:ℝ) ≤ C*x.b := by positivity
    have room : (L:ℝ)^3 ≤ 4*(C:ℝ)^2*x.b := by apply le_of_mul_le_mul_left (a:= (L:ℝ)) _ lr; nlinarith only [mul_le_mul_of_nonneg_left mL cb,q']
    have mprod : (L:ℝ)^(13/10:ℝ)*x.m ≤ 16*(C:ℝ)^3*x.b := calc
      _ ≤ (L:ℝ)^2*(4*C*L) := mul_le_mul (by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le H1 (by norm_num)) mL pos.le (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left room (by positivity : (0:ℝ) ≤ 4*C)]
    have second : (L:ℝ)^(13/10:ℝ) ≤ 16*(C:ℝ)^3*rate x := by
      apply le_trans _ (mul_le_mul_of_nonneg_left r₁ (by positivity)); rw [mul_div_assoc',le_div_iff₀ pos]; exact mprod
    constructor
    · apply (add_le_add first second).trans; rw [←add_mul]; apply mul_le_mul_of_nonneg_right _ rn
      dsimp only [A]; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) C,sq_nonneg (C:ℝ),Nat.cast_nonneg (α:=ℝ) F,Nat.cast_nonneg (α:=ℝ) G]
    · intro P u
      have hc := ceiling x.S x.b C x.m hb hs big hmass x.mb x.hS
      have hg : degree (P.R u) x.b * x.m ≤ F*x.b := by
        unfold degree; rcases max_choice (P.R u).maxDeg ⌈(x.b:ℝ)^(9/10:ℝ)⌉₊ with hh|hh <;> rw [hh]; exact P.degree _; exact hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 32 ≤ 1217)))
      have e := exponent 1 F x.b x.m (scale (P.R u) x.b) (le_max_left ..) (logarithm _ _ _ _ hb hm hg)
      simp only [Nat.cast_one,one_mul] at e
      apply e.trans; apply mul_le_mul _ r₂ (by positivity) (by positivity : (0:ℝ) ≤ A)
      rw [Real.sqrt_eq_rpow]; apply (Real.rpow_le_self_of_one_le (by linarith only [Nat.cast_nonneg (α:=ℝ) F] : (1:ℝ) ≤ F+2) (by norm_num)).trans; exact_mod_cast (show F+2 ≤ A by dsimp [A]; omega)
  · have lcap : L ≤ 2^lo := (Nat.lt_of_not_ge big).le.trans Nat.lt_two_pow_self.le
    have scap := (Nat.le_pow_clog (by decide : 1<2) x.S).trans (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_ge big))
    have mm : x.m ≤ 2^lo := hmS.trans scap
    have mG : (x.m:ℝ) ≤ G := by exact_mod_cast mm.trans (by dsimp [G]; nlinarith only [Nat.zero_le ((2:ℕ)^lo),Nat.zero_le (((2:ℕ)^lo)^2),Nat.zero_le (((2:ℕ)^lo)^3)])
    have bG : (x.b:ℝ) ≤ G*rate x := by
      apply le_trans _ (mul_le_mul_of_nonneg_left r₁ (by positivity)); rw [mul_div_assoc',le_div_iff₀ pos]; nlinarith only [mul_le_mul_of_nonneg_right mG B]
    have denom : 1 ≤ (L:ℝ)^(7/40:ℝ) := Real.one_le_rpow H1 (by norm_num)
    have l2 : (L:ℝ)^(13/10:ℝ) ≤ (L:ℝ)^2 := by rw [←Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_le H1; norm_num
    have lg : (L:ℝ)^(13/10:ℝ) ≤ G*rate x := by
      apply le_trans _ (mul_le_mul_of_nonneg_left r₁ (by positivity)); rw [mul_div_assoc',le_div_iff₀ pos]
      have lc : (L:ℝ) ≤ (2^lo:ℕ) := by exact_mod_cast lcap
      have mc : (x.m:ℝ) ≤ (2^lo:ℕ) := by exact_mod_cast mm
      apply (mul_le_mul (l2.trans (pow_le_pow_left₀ lr.le lc _)) mc pos.le (by positivity)).trans
      have bb : (1:ℝ) ≤ x.b := by exact_mod_cast hb
      apply le_trans _ (le_mul_of_one_le_right (by positivity) bb); dsimp [G]; push_cast; nlinarith only [sq_nonneg ((2:ℝ)^lo),pow_nonneg (by norm_num : (0:ℝ)≤2) lo]
    have fg : (G:ℝ) + G ≤ A := by exact_mod_cast (show G+G ≤ A by dsimp [A]; omega)
    constructor
    · exact (add_le_add ((div_le_self B denom).trans bG) lg).trans (by rw [←add_mul]; exact mul_le_mul_of_nonneg_right fg rn)
    · intro P u; have dd : (1:ℝ) ≤ Real.sqrt (scale (P.R u) x.b) := by apply Real.one_le_sqrt.mpr; exact_mod_cast (le_max_left .. : 1 ≤ scale _ _)
      exact ((div_le_self B dd).trans bG).trans (mul_le_mul_of_nonneg_right (by linarith only [fg,Nat.cast_nonneg (α:=ℝ) G]) rn)
end
end DetDLP.D4BRate

open DetDLP DetDLP.D4Plan
theorem solution (C c : ℕ) (hC : 0<C) : ∃ A : ℕ, ∀ x : Input C c,
    let L := Nat.clog 2 x.S; let rate := (x.b:ℝ)/x.m+(x.b:ℝ)/Real.sqrt (logSafe x.m)
    ((x.b:ℝ)/(L:ℝ)^(7/40:ℝ) + (L:ℝ)^(13/10:ℝ)) ≤ A*rate ∧
    ∀ (P : Plan x) (u : Fin P.N),
      let Δ := max (P.R u).maxDeg ⌈(x.b:ℝ)^(9/10:ℝ)⌉₊
      let ρ := max 1 ⌊Real.logb 2 ((x.b:ℝ)/Δ)⌋₊
      (x.b:ℝ)/Real.sqrt ρ ≤ A*rate := D4BRate.bounds hC
