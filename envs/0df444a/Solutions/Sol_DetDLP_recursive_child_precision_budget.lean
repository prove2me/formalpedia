-- Prove2me | solution 1 for DetDLP.recursive_child_precision_budget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:18:59.344991+00:00
-- url     : https://prove2.me/submissions/a51fbf92-b179-4247-8182-e49c2a19c700

import Mathlib

section
namespace DetDLP.ActiveDepthPrecision
open Filter Finset

theorem absorbs (A k : ℕ) : ∃ N : ℕ,∀ n≥N,A*(n+1)^k≤2^n := by
  let B := A*2^k+1
  have hB : (0:ℝ)<B := by exact_mod_cast (show 0<B by dsimp [B]; omega)
  have little := isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) k (r:=2) (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (little.bound (inv_pos.mpr hB))
  refine ⟨max N 1,fun n hn => ?_⟩
  have h := hN n ((le_max_left ..).trans hn)
  have realB : (n:ℝ)^k≤(B:ℝ)⁻¹*(2:ℝ)^n := by
    simpa only [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg n) _),Real.norm_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) _)] using h
  have aux : (B:ℝ)*(n:ℝ)^k≤(2:ℝ)^n := by
    have H := mul_le_mul_of_nonneg_left realB hB.le
    rwa [← mul_assoc,mul_inv_cancel₀ hB.ne',one_mul] at H
  have natB : B*n^k≤2^n := by exact_mod_cast aux
  have hstep : (n+1)^k≤(2*n)^k := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ A*((2*n)^k) := Nat.mul_le_mul_left _ hstep
    _ ≤ B*n^k := by rw [mul_pow,← mul_assoc]; exact Nat.mul_le_mul_right _ (by dsimp [B]; omega)
    _ ≤ _ := natB

theorem relevant (C B ρ d : ℕ) (hC : 0<C) (hB : 0<B)
    (depth : 2^d≤C*(ρ.sqrt+1)) :
    let u := ρ/(B*2^d)
    ρ+1≤((2*B*C+2)*(u+1))^2 := by
  intro u
  let v := ρ.sqrt
  let f := (u+1)*B*C
  have a : ρ<(u+1)*(B*2^d) := by
    rw [Nat.mul_comm (u+1)]; exact Nat.lt_mul_div_succ _ (by positivity)
  have b := Nat.mul_le_mul_left ((u+1)*B) depth
  have c : v*v<f*(v+1) := by
    calc
      v*v≤ρ := Nat.sqrt_le _
      _ < (u+1)*(B*2^d) := a
      _ ≤ f*(v+1) := by simpa only [f,v,Nat.mul_assoc] using b
  have small : v≤2*f := by
    by_cases hv : v=0
    · omega
    · have h : f*(v+1)≤f*(2*v) := Nat.mul_le_mul_left _ (by omega)
      have z : v*v<(2*f)*v := (c.trans_le h).trans_eq (by ring)
      exact (Nat.lt_of_mul_lt_mul_right z).le
  have sq := Nat.lt_succ_sqrt ρ
  have bound : v+1≤(2*B*C+2)*(u+1) := by dsimp [f] at small; nlinarith only [small,Nat.zero_le u]
  exact (Nat.succ_le_of_lt sq).trans (by simpa [pow_two] using Nat.mul_le_mul bound bound)

theorem active {C B : ℕ} (hC : 0<C) (hB : 0<B) (A j : ℕ) :
    ∃ R : ℕ,∀ (ρ β M d : ℕ),R≤ρ→0<M→β≤M*(ρ.sqrt+1)→M*8^d≤C*β →
      A*(ρ+1)^j≤2^(ρ/(B*2^d)) := by
  let K := 2*B*C+2
  obtain ⟨N,hN⟩ := absorbs (A*K^(2*j)) (2*j)
  refine ⟨(K*(N+1))^2,?_⟩
  intro ρ β M d hρ hm hb hd
  have power : 2^d≤8^d := Nat.pow_le_pow_left (by decide) _
  have depth : 2^d≤C*(ρ.sqrt+1) := by
    apply Nat.le_of_mul_le_mul_left (c:=M) _ hm
    calc
      _≤M*8^d := Nat.mul_le_mul_left _ power
      _≤C*β := hd
      _≤C*(M*(ρ.sqrt+1)) := Nat.mul_le_mul_left _ hb
      _=M*(C*(ρ.sqrt+1)) := by ring
  let u := ρ/(B*2^d)
  have bound : ρ+1≤(K*(u+1))^2 := relevant C B ρ d hC hB depth
  have hu : N≤u := by
    by_contra! h
    have small := Nat.pow_le_pow_left (Nat.mul_le_mul_left K (show u+1≤N+1 by omega)) 2
    omega
  calc
    A*(ρ+1)^j ≤ A*((K*(u+1))^2)^j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)
    _ = (A*K^(2*j))*(u+1)^(2*j) := by rw [← pow_mul,mul_pow]; ring
    _ ≤ _ := hN u hu
end DetDLP.ActiveDepthPrecision
end

section
namespace DetDLP.ContractionPathPrecision

def window (B ρ d : ℕ) := ρ/(B*2^d)
def widthBefore (B ρ : ℕ) : ℕ→ℕ
  | 0 => 0
  | d+1 => widthBefore B ρ d+2*window B ρ d
def mult (M u : ℕ) := (3*M+u-1)/u
def next (p M u a i : ℕ) := p+8*mult M u*2^(a-i)+8*M*(a+1)
theorem window_le (B ρ d : ℕ) : window B ρ d≤ρ := Nat.div_le_self _ _
theorem prefix_mono (B ρ : ℕ) : Monotone (widthBefore B ρ) := by
  apply monotone_nat_of_le_succ
  intro n; simp [widthBefore]
theorem prefix_le (B ρ d : ℕ) : widthBefore B ρ d≤2*d*ρ := by
  induction d with
  | zero => simp [widthBefore]
  | succ d ih =>
    simp only [widthBefore]; have h := window_le B ρ d
    rw [Nat.mul_succ,Nat.add_mul]; omega
theorem mult_total (M u : ℕ) : mult M u*u≤3*M+u := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
theorem mult_le (M u : ℕ) : mult M u≤3*M+1 := by
  by_cases h : u=0
  · simp [mult,h]
  · apply Nat.le_of_mul_le_mul_right (c:=u) _ (Nat.pos_of_ne_zero h)
    have H := mult_total M u
    have h' := Nat.mul_le_mul_left (3*M) (Nat.one_le_iff_ne_zero.mpr h)
    rw [Nat.add_mul]; simp only [one_mul]; omega

theorem add_cap {M X u a A i : ℕ} (hM : M≤X) (ha : a≤A) :
    next 0 M u a i≤64*(X+1)*(A+1)*2^A := by
  have hm : mult M u≤4*(X+1) := by have := mult_le M u; omega
  have hp : 2^(a-i)≤2^A := Nat.pow_le_pow_right (by decide) ((Nat.sub_le _ _).trans ha)
  have hq : 1≤2^A := Nat.one_le_pow _ _ (by decide)
  have hbig := Nat.mul_le_mul_right (4*(X+1)) (show 1≤A+1 by omega)
  have t1 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hm) hp
  have t2 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hM) (Nat.add_le_add_right ha 1)
  have up := Nat.mul_le_mul_left (8*X*(A+1)) hq
  unfold next
  nlinarith only [t1,t2,up,Nat.zero_le ((X+1)*A*2^A),Nat.zero_le ((X+1)*2^A),Nat.zero_le (X*(A+1)*2^A),Nat.zero_le (A*2^A)]

theorem path_cap (B ρ X d : ℕ) (p m i : ℕ→ℕ) (h0 : p 0≤X)
    (size : ∀ j<d,m j≤X)
    (step : ∀ j<d,p (j+1)≤next (p j) (m j) (window B ρ j) (widthBefore B ρ (j+1)) (i j)) :
    p d≤(X+d*(64*(X+1)*(widthBefore B ρ d+1)))*2^(widthBefore B ρ d) := by
  let A := widthBefore B ρ d
  let K := 64*(X+1)*(A+1)
  have aux (j : ℕ) (hj : j≤d) : p j≤X+j*(K*2^A) := by
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have cap := add_cap (i:=i j) (u:=window B ρ j) (size j hj) (prefix_mono B ρ hj)
      have s := step j hj
      have h := ih (by omega)
      change next 0 (m j) _ _ _≤K*2^A at cap
      simp only [next,zero_add] at cap s
      rw [Nat.succ_mul]; omega
  have h := aux d le_rfl
  have pow : 1≤2^A := Nat.one_le_pow _ _ (by decide)
  have hX := Nat.mul_le_mul_left X pow
  change p d≤(X+d*K)*2^A
  rw [Nat.add_mul,Nat.mul_assoc]; omega

theorem envelope {B C ρ β d : ℕ} (hβ : 0<β) (hd : d≤C*(ρ+1))
    (p m i : ℕ→ℕ) (h0 : p 0≤C*β) (size : ∀ j<d,m j≤C*β)
    (step : ∀ j<d,p (j+1)≤next (p j) (m j) (window B ρ j) (widthBefore B ρ (j+1)) (i j)) :
    p d≤(256*(C+1)^3)*β*(ρ+1)^3*2^(widthBefore B ρ d) := by
  apply (path_cap B ρ (C*β) d p m i h0 size step).trans
  apply Nat.mul_le_mul_right
  have x : C*β+1≤(C+1)*β := by nlinarith
  have hpr := prefix_le B ρ d
  have hr := Nat.mul_le_mul_right ρ (Nat.mul_le_mul_left 2 hd)
  have cap : widthBefore B ρ d+1≤3*(C+1)*(ρ+1)^2 := by nlinarith only [hpr,hr,Nat.zero_le C,Nat.zero_le ρ,Nat.zero_le (C*ρ),Nat.zero_le (C*ρ^2),Nat.zero_le (ρ^2)]
  have t := Nat.mul_le_mul hd (Nat.mul_le_mul (Nat.mul_le_mul_left 64 x) cap)
  have one : 1≤(ρ+1)^3 := Nat.one_le_pow _ _ (by omega)
  have rest : C*β≤(C+1)^3*β*(ρ+1)^3 := calc
    _≤(C+1)^3*β := Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le (C^2),Nat.zero_le (C^3)])
    _≤_ := by simpa using Nat.mul_le_mul_left ((C+1)^3*β) one
  calc
    _≤(C+1)^3*β*(ρ+1)^3 + (C*(ρ+1))*(64*((C+1)*β)*(3*(C+1)*(ρ+1)^2)) := Nat.add_le_add rest t
    _≤_ := by
      have h := Nat.mul_le_mul_right (192*(C+1)^2*β*(ρ+1)^3) (Nat.le_succ C)
      nlinarith only [h,Nat.zero_le ((C+1)^3*β*(ρ+1)^3)]

end DetDLP.ContractionPathPrecision
end

section
namespace DetDLP.ChildPrecisionBudget
open ContractionPathPrecision

theorem branch {C ρ β d M p u a i w : ℕ}
    (hd : d≤C*(ρ+1)) (hβ : β≤M*(ρ+1))
    (hp : p≤256*(C+1)^3*β*(ρ+1)^3*2^w)
    (hu : u≤ρ) (huM : u≤M) (hi : i<u) (ha : a=w+2*u)
    (hw : w≤2*d*ρ) (absorb : 256*(C+1)^3*(ρ+1)^5≤2^u) :
    next p M u a i*u≤41*M*2^(a-i) := by
  let s := ρ+1
  let A := 256*(C+1)^3
  let D := 2^(a-i)
  have pw : 2^w*2^u≤D := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have sm : 2^u≤D := Nat.pow_le_pow_right (by decide) (by omega)
  have capP : p*u≤M*D := calc
    _≤(A*(M*s)*s^3*2^w)*s := Nat.mul_le_mul (hp.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hβ)))) (by dsimp [s]; omega)
    _ = M*(2^w*(A*s^5)) := by ring
    _ ≤ M*(2^w*2^u) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ absorb)
    _ ≤ M*D := Nat.mul_le_mul_left _ pw
  have multU : mult M u*u≤4*M := by have h := mult_total M u; omega
  have hbig := Nat.mul_le_mul_right ρ (Nat.mul_le_mul_left 2 hd)
  have capA : a+1≤4*(C+1)*s^2 := by
    dsimp [s]
    nlinarith only [hw,hbig,hu,ha,Nat.zero_le C,Nat.zero_le (ρ^2),Nat.zero_le (C*ρ),Nat.zero_le (C*ρ^2)]
  have up : 4*(C+1)≤A := by dsimp [A]; nlinarith [Nat.zero_le (C^2),Nat.zero_le (C^3)]
  have capWeight : (a+1)*u≤D := calc
    _ ≤ (4*(C+1)*s^2)*s := Nat.mul_le_mul capA (by dsimp [s]; omega)
    _ = (4*(C+1))*s^3 := by ring
    _ ≤ A*s^5 := Nat.mul_le_mul up (Nat.pow_le_pow_right (by dsimp [s]; omega) (by decide))
    _ ≤ 2^u := absorb
    _ ≤ D := sm
  have t2 := Nat.mul_le_mul_left (8*D) multU
  have t3 := Nat.mul_le_mul_left (8*M) capWeight
  change (p+8*mult M u*D+8*M*(a+1))*u≤41*M*D
  nlinarith only [capP,t2,t3]

theorem depth_pow (d : ℕ) : d≤8^d := by
  induction d with
  | zero => decide
  | succ d ih => rw [pow_succ]; have := Nat.one_le_pow d 8 (by decide); omega

theorem full (C B : ℕ) (hc : 0<C) (hb : 0<B) :
    ∃ R : ℕ,∀ (ρ β d : ℕ) (p m i : ℕ→ℕ), R≤ρ→0<β→0< m d→
      β≤ m d*(ρ.sqrt+1)→m d*8^d≤C*β→p 0≤C*β→
      (∀ j<d,m j≤C*β)→
      (∀ j<d,p (j+1)≤next (p j) (m j) (window B ρ j) (widthBefore B ρ (j+1)) (i j))→
      window B ρ d≤ m d→i d<window B ρ d→
      next (p d) (m d) (window B ρ d) (widthBefore B ρ (d+1)) (i d)*window B ρ d≤
        41*m d*2^(widthBefore B ρ (d+1)-i d) := by
  obtain ⟨R,hR⟩ := ActiveDepthPrecision.active hc hb (256*(C+1)^3) 5
  refine ⟨R,?_⟩
  intro ρ β d p m i hρ hβ hm hroot hsize h0 hM hstep hu hi
  have scale := hroot.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sqrt_le_self ρ) 1))
  have pow := depth_pow d
  have H : m d*d≤ m d*(C*(ρ+1)) := calc
    _≤ m d*8^d := Nat.mul_le_mul_left _ pow
    _≤C*β := hsize
    _≤C*(m d*(ρ+1)) := Nat.mul_le_mul_left _ scale
    _=_ := by ring
  have hd := Nat.le_of_mul_le_mul_left H hm
  apply branch (d:=d) (C:=C) (w:=widthBefore B ρ d) hd scale
    (envelope hβ hd p m i h0 hM hstep) (window_le B ρ d) hu hi rfl (prefix_le B ρ d)
  exact hR ρ β (m d) d hρ hm hroot hsize

end DetDLP.ChildPrecisionBudget
end

open DetDLP

theorem solution (C B : ℕ) (hC : 0<C) (hB : 0<B) :
    ∃ R : ℕ,∀ (ρ β d : ℕ) (p m i : ℕ→ℕ),
      let u (j : ℕ) := ρ/(B*2^j)
      let a (j : ℕ) := 2*∑ k ∈ Finset.range (j+1),u k
      let h (j : ℕ) := (3*m j+u j-1)/u j
      let prec (j : ℕ) := p j+8*h j*2^(a j-i j)+8*m j*(a j+1)
      R≤ρ→0<β→0< m d→β≤ m d*(ρ.sqrt+1)→m d*8^d≤C*β→p 0≤C*β→
      (∀ j<d,m j≤C*β)→(∀ j<d,p (j+1)≤prec j)→u d≤ m d→i d<u d→
        prec d*u d≤41*m d*2^(a d-i d) := by
  obtain ⟨R,H⟩ := ChildPrecisionBudget.full C B hC hB
  refine ⟨R,?_⟩
  intro ρ β d p m i u a h prec
  have same (j : ℕ) : ContractionPathPrecision.widthBefore B ρ j=2*∑ k ∈ Finset.range j,u k := by
    induction j with
    | zero => simp [ContractionPathPrecision.widthBefore]
    | succ j ih => rw [ContractionPathPrecision.widthBefore,ih,Finset.sum_range_succ,Nat.mul_add]; rfl
  intro hρ hβ hm hroot hsize h0 hM hstep hu hi
  have eq (j : ℕ) : ContractionPathPrecision.next (p j) (m j) (ContractionPathPrecision.window B ρ j)
      (ContractionPathPrecision.widthBefore B ρ (j+1)) (i j)=prec j := by
    rw [same]; rfl
  have answer := H ρ β d p m i hρ hβ hm hroot hsize h0 hM (fun j hj => (eq j).symm ▸ hstep j hj) hu hi
  rwa [eq,same] at answer
