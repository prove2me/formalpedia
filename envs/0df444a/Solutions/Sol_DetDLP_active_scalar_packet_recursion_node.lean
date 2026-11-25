-- Prove2me | solution 1 for DetDLP.active_scalar_packet_recursion_node
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:34:22.95048+00:00
-- url     : https://prove2.me/submissions/ab52cb2b-b44d-4a2d-9c91-dd5db5c3757d

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_bounded_oriented_contraction_step
import Theorems.Thm_DetDLP_recursive_child_precision_budget

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
namespace DetDLP.ActivePackingGeometry
open ContractionPathPrecision

theorem nextWindow (B ρ d : ℕ) : window B ρ (d+1)=window B ρ d/2 := by
  simp [window,pow_succ,Nat.div_div_eq_div_mul,Nat.mul_assoc]
theorem telescopes (B ρ d : ℕ) :
    widthBefore B ρ d+4*window B ρ d≤4*window B ρ 0 := by
  induction d with
  | zero => simp [widthBefore]
  | succ d ih => rw [widthBefore,nextWindow]; omega
theorem width_bound (B ρ d : ℕ) : B*widthBefore B ρ d≤4*ρ := by
  have hh := telescopes B ρ d
  have h := Nat.mul_le_mul_left B (show widthBefore B ρ d≤4*window B ρ 0 by omega)
  have div : B*window B ρ 0≤ρ := by simpa [window] using Nat.mul_div_le ρ B
  calc
    _≤B*(4*window B ρ 0) := h
    _=4*(B*window B ρ 0) := by ring
    _≤_ := Nat.mul_le_mul_left _ div

theorem half_absorbs : ∃ R : ℕ,∀ ρ≥R,(ρ+2)^2≤2^(ρ/2) := by
  obtain ⟨N,hN⟩ := ActiveDepthPrecision.absorbs 16 2
  refine ⟨2*N,fun ρ h => ?_⟩
  have aux : ρ+2≤4*(ρ/2+1) := by omega
  calc
    _≤(4*(ρ/2+1))^2 := Nat.pow_le_pow_left aux _
    _=16*(ρ/2+1)^2 := by ring
    _≤_ := hN _ (by omega)

theorem fit {ρ β M Δ a u : ℕ} (hΔ : 0<Δ) (hM : 0<M)
    (hs : (ρ+2)^2≤2^(ρ/2)) (ha : 48*a≤ρ) (hu : u≤ρ)
    (hsep : 2^ρ*Δ≤β) (hroot : β≤M*(ρ.sqrt+1)) :
    (a+2)*(64^a)^4*Δ≤M ∧ 2^a*(64^a)^2≤M ∧ u≤M := by
  have small : (a+2)*(ρ.sqrt+1)≤2^(ρ/2) := calc
    _≤(ρ+2)*(ρ+2) := Nat.mul_le_mul (by omega) (by have := Nat.sqrt_le_self ρ; omega)
    _≤_ := by simpa [pow_two] using hs
  have pk : (64^a)^4=2^(24*a) := by
    rw [show 64=2^6 by decide,←pow_mul,←pow_mul]; congr 1; ring
  have geom := Nat.mul_le_mul_right (2^(24*a)) small
  have expo : 2^(ρ/2)*2^(24*a)≤2^ρ := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hg : (a+2)*(64^a)^4*Δ≤M := by
    apply Nat.le_of_mul_le_mul_right (c:=ρ.sqrt+1) _ (by omega)
    calc
      _=((a+2)*(ρ.sqrt+1)*2^(24*a))*Δ := by rw [pk]; ring
      _≤2^ρ*Δ := Nat.mul_le_mul_right _ (geom.trans expo)
      _≤_ := hsep.trans hroot
  refine ⟨hg,?_,?_⟩
  · have cap : 2^a*(64^a)^2≤(64^a)^4 := by
      rw [pk,show 64=2^6 by decide,← pow_mul,← pow_mul,← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : 1≤(a+2)*Δ := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have g := Nat.mul_le_mul_left ((64^a)^4) h1
    exact cap.trans ((by simpa only [one_mul,Nat.mul_one,mul_assoc,mul_left_comm,mul_comm] using g : (64^a)^4≤(a+2)*(64^a)^4*Δ).trans hg)
  · apply Nat.le_of_mul_le_mul_right (c:=ρ.sqrt+1) _ (by omega)
    calc
      _≤(ρ+2)*(ρ+2) := Nat.mul_le_mul (by omega) (by have := Nat.sqrt_le_self ρ; omega)
      _≤2^(ρ/2) := by simpa [pow_two] using hs
      _≤2^ρ := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
      _≤2^ρ*Δ := by simpa using Nat.mul_le_mul_left (2^ρ) hΔ
      _≤_ := hsep.trans hroot

theorem full {B : ℕ} (hB : 192≤B) :
    ∃ R : ℕ,∀ (ρ β M Δ d : ℕ),R≤ρ→0<Δ→0<M→2^ρ*Δ≤β→β≤M*(ρ.sqrt+1)→
    let a := widthBefore B ρ (d+1)
    let u := window B ρ d
    (a+2)*(64^a)^4*Δ≤M ∧ 2^a*(64^a)^2≤M ∧ u≤M := by
  obtain ⟨R,h⟩ := half_absorbs
  refine ⟨R,?_⟩; intro ρ β M Δ d hρ hΔ hM hsep hroot a u
  have pr := width_bound B ρ (d+1)
  have small := Nat.mul_le_mul_right a hB
  change B*a≤4*ρ at pr
  exact fit hΔ hM (h _ hρ) (by omega) (window_le B ρ d) hsep hroot
end DetDLP.ActivePackingGeometry
end

section
namespace DetDLP.ScalarPacketParameters
open ContractionPathPrecision

noncomputable def degree (G : BipartiteMultigraph) (β : ℕ) := max G.maxDeg (Nat.ceil ((β:ℝ)^((9:ℝ)/10)))
noncomputable def scale (G : BipartiteMultigraph) (β : ℕ) :=
  max 1 (Nat.floor (Real.logb 2 ((β:ℝ)/(degree G β:ℝ))))

theorem sep (G : BipartiteMultigraph) (β : ℕ) (hβ : 0<β) (hρ : 2≤ scale G β) :
    0<degree G β ∧ 2^(scale G β)*degree G β≤β := by
  let Δ := degree G β
  let y := Real.logb 2 ((β:ℝ)/(Δ:ℝ))
  have betaPos : (0:ℝ)<β := by exact_mod_cast hβ
  have Δreal : (0:ℝ)<(Δ:ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos betaPos ((9:ℝ)/10))
    ((Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil ((β:ℝ)^((9:ℝ)/10))≤Δ from le_max_right ..)))
  have hΔ : 0<Δ := by exact_mod_cast Δreal
  have hy : 0≤ y := by
    by_contra! H
    have fl := Nat.floor_of_nonpos H.le
    change 2≤ max 1 ⌊y⌋₊ at hρ; rw [fl] at hρ; omega
  have fl : (scale G β:ℝ)≤ y := by
    have eq : scale G β=⌊y⌋₊ := by change max 1 ⌊y⌋₊=_; change 2≤ max 1 ⌊y⌋₊ at hρ; omega
    rw [eq]; exact Nat.floor_le hy
  have l := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (div_pos betaPos Δreal)).mp fl
  rw [Real.rpow_natCast] at l
  exact ⟨hΔ,by exact_mod_cast ((le_div_iff₀ Δreal).mp l)⟩

theorem packet_degree (G : BipartiteMultigraph) (β a ρ : ℕ) (hβ : 2≤β)
    (hρ : 2^ρ≤β) (ha : 2*(a+1)≤ρ) : 2*2^a≤degree G β := by
  let n := 2^(a+1)
  have hsq : n^2≤β := calc
    _ = 2^((a+1)*2) := (pow_mul ..).symm
    _ ≤ 2^ρ := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ _ := hρ
  have hb : (1:ℝ)≤β := by exact_mod_cast (show 1≤β by omega)
  have sq : (n:ℝ)^2≤(β:ℝ) := by exact_mod_cast hsq
  have le : (n:ℝ)≤Real.sqrt β := (Real.le_sqrt (by positivity) (by positivity)).mpr sq
  rw [Real.sqrt_eq_rpow] at le
  have A := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1:ℝ)/2≤9/10)
  have hi := (le.trans A).trans (Nat.le_ceil _)
  have nat : n≤Nat.ceil ((β:ℝ)^((9:ℝ)/10)) := by exact_mod_cast hi
  calc
    _ = n := by dsimp [n]; rw [pow_succ,Nat.mul_comm]
    _ ≤ _ := nat.trans (le_max_right ..)

theorem full (C B : ℕ) (hb : 192≤B) :
    ∃ R : ℕ,∀ (G : BipartiteMultigraph) (β M d : ℕ),
    let Δ := degree G β
    let ρ := scale G β
    let a := widthBefore B ρ (d+1)
    let u := window B ρ d
    2≤β→R≤ρ→0<M→M≤C*β→β≤M*(ρ.sqrt+1)→
      (a+2)*(64^a)^4*Δ≤M ∧ 2^a*(64^a)^2≤M ∧ u≤M ∧ 2*2^a≤Δ ∧
        M*(2^(a+1)-1)+1≤2^(4*Nat.clog 2 β) := by
  obtain ⟨K,hK⟩ := ActivePackingGeometry.full hb
  refine ⟨max (max K C) 4,?_⟩
  intro G β M d Δ ρ a u hb' hρ hm hmax hroot
  obtain ⟨hΔ,space⟩ := sep G β (by omega) (by change 2≤ρ; omega)
  have pow : 2^ρ≤β := (Nat.le_mul_of_pos_right _ hΔ).trans space
  have fit := hK ρ β M Δ d (by omega) hΔ hm space hroot
  have pr := ActivePackingGeometry.width_bound B ρ (d+1)
  have left := Nat.mul_le_mul_right a hb
  change B*a≤4*ρ at pr
  have deg := packet_degree G β a ρ hb' pow (by omega)
  refine ⟨fit.1,fit.2.1,fit.2.2,deg,?_⟩
  have aux : ∀ j : ℕ,j≤2^j := by
    intro j; induction j with
    | zero => decide
    | succ j ih => rw [pow_succ]; have := @Nat.one_le_two_pow j; omega
  have small : C≤β := (show C≤ρ by omega).trans ((aux ρ).trans pow)
  have count : 2^(a+1)-1≤β := (Nat.sub_le _ _).trans
    ((Nat.pow_le_pow_right (by decide) (by omega : a+1≤ρ)).trans pow)
  have bounds := Nat.mul_le_mul (hmax.trans (Nat.mul_le_mul_right β small)) count
  have adv : M*(2^(a+1)-1)+1≤β^4 := by
    have grow := Nat.mul_le_mul_left (β^3) hb'
    have pos : 1≤β^3 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [bounds,grow,pos]
  have g := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) β) 4
  rw [← pow_mul,Nat.mul_comm (Nat.clog 2 β)] at g; exact adv.trans g
end DetDLP.ScalarPacketParameters
end

section
namespace DetDLP.ActiveScalarNode
open Finset Polynomial DetDLP.OrientedPacketInstance

theorem full (C : ℕ) (hc : 0<C) :
    ∃ R₀ : ℕ,∀ (root G : BipartiteMultigraph) (β d : ℕ) (pin m past : ℕ→ℕ)
      {b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ),
    let Δ := max root.maxDeg (Nat.ceil ((β:ℝ)^((9:ℝ)/10)))
    let ρ := max 1 (Nat.floor (Real.logb 2 ((β:ℝ)/(Δ:ℝ))))
    let u (j : ℕ) := ρ/(131072*2^j)
    let a (j : ℕ) := 2*∑ v ∈ range (j+1),u v
    let h (j : ℕ) := (3*m j+u j-1)/u j
    let precision (j z : ℕ) := pin j+8*h j*2^(a j-z)+8*m j*(a j+1)
    2≤β→R₀≤ρ→0<G.nE→m d=G.nE→β≤G.nE*(ρ.sqrt+1)→G.nE*8^d≤C*β→
    G.maxDeg≤Δ→pin 0≤C*β→(∀ j<d,m j≤C*β)→(∀ j<d,pin (j+1)≤precision j (past j))→
    (∀ x,(univ.filter fun y => host x=host y).card≤τ)→
    0<u d ∧ u d≤G.nE ∧ u d≤a d ∧ G.nE*(2^(a d+1)-1)+1≤2^(4*Nat.clog 2 β) ∧
    ∃ (N : ℕ) (active : Fin N→Finset (Pos (a d))) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin (a d)→Fin 64×Fin 64) (grp : Fin (a d)→Fin G.nV→Fin 64),
    N*2^(a d)≤3*G.nE ∧ (∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a d+2)*τ) ∧
    ∀ (i : Fin (a d)) (hi : i.val<u d) (t : ZMod (2^(a d+1))) (ht : t≠0) (hval : padicValNat 2 t.val=i.val),
    let p := precision d i.val
    let J := Mode i (fun q => tag q i) p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (246:ℝ)*G.nE/Real.sqrt (u d)) ∧
    ∃ U : ZMod (2^(a d+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp i v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg≤Δ) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp i v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp i v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by
  classical
  obtain ⟨K,hK⟩ := ScalarPacketParameters.full C 131072 (by decide)
  obtain ⟨D,hD⟩ := recursive_child_precision_budget C 131072 hc (by decide)
  obtain ⟨A,hA⟩ := ActiveDepthPrecision.active (B:=131072) hc (by decide) 2 0
  refine ⟨max (max K D) A,?_⟩
  intro root G β d pin m past b host τ Δ ρ u a h precision hβ hρ hM eq active shrink deg init masses steps legs
  have mmax : G.nE≤C*β := (Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0<8) d)).trans shrink
  have width (j : ℕ) : ContractionPathPrecision.widthBefore 131072 ρ j=2*∑ k ∈ range j,u k := by
    induction j with
    | zero => simp [ContractionPathPrecision.widthBefore]
    | succ j ih => rw [ContractionPathPrecision.widthBefore,ih,sum_range_succ,Nat.mul_add]; rfl
  have hk := hK root β G.nE d hβ (by change K≤ρ; omega) hM mmax active
  have wa : ContractionPathPrecision.widthBefore 131072 (ScalarPacketParameters.scale root β) (d+1)=a d := width _
  rw [wa] at hk
  change (a d+2)*(64^(a d))^4*Δ≤G.nE ∧ 2^(a d)*(64^(a d))^2≤G.nE ∧ u d≤G.nE ∧
    2*2^(a d)≤Δ ∧ G.nE*(2^(a d+1)-1)+1≤2^(4*Nat.clog 2 β) at hk
  obtain ⟨geom,pad,fit,dmax,grid⟩ := hk
  have pos : 0<u d := by
    have hh := hA ρ β G.nE d (by omega) hM active shrink
    simp only [pow_zero,Nat.mul_one] at hh
    change 2≤2^u d at hh
    by_contra! no
    rw [Nat.eq_zero_of_le_zero no] at hh; omega
  have aw : u d≤a d := by dsimp [a]; rw [sum_range_succ]; omega
  have degpos : 0<G.maxDeg := by
    let e : Fin G.nE := ⟨0,hM⟩
    let v := (G.endpoints e).1
    have mem : e∈G.ports v := by simp [BipartiteMultigraph.ports,v]
    exact (List.length_pos_of_mem mem).trans_le (show G.deg v≤G.maxDeg from Finset.le_sup (mem_univ v))
  have geo := (Nat.mul_le_mul_left ((a d+2)*(64^(a d))^4) deg).trans geom
  obtain ⟨N,slots,L,tag,grp,pack,terminal,sample⟩ := bounded_oriented_contraction_step G host τ legs (Nat.mul_pos hM degpos) geo pad
  refine ⟨pos,fit,aw,grid,N,slots,L,tag,grp,pack,terminal,?_⟩
  intro i hi t ht hval p
  let idx (j : ℕ) := if j=d then i.val else past j
  have hs : ∀ j<d,pin (j+1)≤precision j (idx j) := by
    intro j hj; simpa [idx,Nat.ne_of_lt hj] using steps j hj
  have prev := hD ρ β d pin m idx (by omega) (by omega) (eq ▸ hM) (eq ▸ active)
    (eq ▸ shrink) init masses hs (eq ▸ fit) (by simpa [idx] using hi)
  change precision d (idx d)*u d≤41*m d*2^(a d-idx d) at prev
  simp only [idx,if_pos rfl,eq] at prev
  have up : (0:ℝ)<u d := by exact_mod_cast pos
  have small : (p:ℝ)≤41*G.nE*(2:ℝ)^(a d-i.val)/(u d:ℝ) := by
    apply (le_div_iff₀ up).mpr; exact_mod_cast prev
  have hp : 0<p := by
    have prod : 0<8*m d*(a d+1) := by rw [eq]; positivity
    dsimp [p,precision]; omega
  obtain ⟨count,U,rep,H⟩ := sample i p hp t ht hval 41 (u d) (by norm_num) up small
  refine ⟨by simpa only [show (6:ℝ)*41=246 by norm_num] using count,U,rep,?_⟩
  intro R _ _ T V z
  obtain ⟨G',child,shrink',total,bdeg,nv,formula⟩ := H R T V z
  exact ⟨G',child,shrink',total,fun g => (bdeg g).trans (max_le deg dmax),nv,formula⟩
end DetDLP.ActiveScalarNode
end

open DetDLP Finset Polynomial DetDLP.OrientedPacketInstance

theorem solution (C : ℕ) (hc : 0<C) :
    ∃ R₀ : ℕ,∀ (root G : BipartiteMultigraph) (β d : ℕ) (pin m past : ℕ→ℕ)
      {b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ),
    let Δ := max root.maxDeg (Nat.ceil ((β:ℝ)^((9:ℝ)/10)))
    let ρ := max 1 (Nat.floor (Real.logb 2 ((β:ℝ)/(Δ:ℝ))))
    let u (j : ℕ) := ρ/(131072*2^j)
    let a (j : ℕ) := 2*∑ v ∈ range (j+1),u v
    let h (j : ℕ) := (3*m j+u j-1)/u j
    let precision (j z : ℕ) := pin j+8*h j*2^(a j-z)+8*m j*(a j+1)
    2≤β→R₀≤ρ→0<G.nE→m d=G.nE→β≤G.nE*(ρ.sqrt+1)→G.nE*8^d≤C*β→
    G.maxDeg≤Δ→pin 0≤C*β→(∀ j<d,m j≤C*β)→(∀ j<d,pin (j+1)≤precision j (past j))→
    (∀ x,(univ.filter fun y => host x=host y).card≤τ)→
    0<u d ∧ u d≤G.nE ∧ u d≤a d ∧ G.nE*(2^(a d+1)-1)+1≤2^(4*Nat.clog 2 β) ∧
    ∃ (N : ℕ) (active : Fin N→Finset (Pos (a d))) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin (a d)→Fin 64×Fin 64) (grp : Fin (a d)→Fin G.nV→Fin 64),
    N*2^(a d)≤3*G.nE ∧ (∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a d+2)*τ) ∧
    ∀ (i : Fin (a d)) (hi : i.val<u d) (t : ZMod (2^(a d+1))) (ht : t≠0) (hval : padicValNat 2 t.val=i.val),
    let p := precision d i.val
    let J := Mode i (fun q => tag q i) p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (246:ℝ)*G.nE/Real.sqrt (u d)) ∧
    ∃ U : ZMod (2^(a d+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp i v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg≤Δ) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp i v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp i v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by
  exact ActiveScalarNode.full C hc
