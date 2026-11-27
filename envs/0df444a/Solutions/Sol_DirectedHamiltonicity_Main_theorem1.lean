-- Prove2me | solution 1 for DirectedHamiltonicity.Main.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:12:29.550875+00:00
-- url     : https://prove2.me/submissions/f37934d0-ca39-4324-9e96-b1fa901ab789

import Mathlib
import Theorems.Thm_DirectedHamiltonicity_Main_finite_coin_cycle_search
import Theorems.Thm_DirectedHamiltonicity_Main_execute_cycle_search

namespace DirectedHamiltonicity.Main.CycleReduction

theorem exponent_budget (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    (n+1 : ℝ)^k * ((50/49 : ℝ)^n * (15/8 : ℝ)^n) ≤ C * (19133/10000 : ℝ)^n := by
  have asym := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) k
    (r₁ := 375/196) (r₂ := 19133/10000) (by rw [Real.norm_eq_abs,abs_of_pos (by norm_num)]; norm_num)
  obtain ⟨K,hK,all⟩ := Asymptotics.bound_of_isBigO_nat_atTop asym.isBigO
  refine ⟨K * (19133/10000), by positivity, fun n => ?_⟩
  have h := all (x := n+1) (by dsimp; positivity)
  simp only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] at h
  rw [abs_of_nonneg (by positivity : 0 ≤ ((n:ℝ)+1)^k * (375/196:ℝ)^(n+1)),
    abs_of_nonneg (by positivity : 0 ≤ (19133/10000:ℝ)^(n+1))] at h
  rw [← mul_pow, show (50 / 49 : ℝ) * (15/8) = 375/196 by norm_num]
  calc
    _ ≤ (n+1 : ℝ)^k * (375/196 : ℝ)^(n+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) (by positivity)
    _ ≤ K*(19133/10000 : ℝ)^(n+1) := h
    _ = _ := by rw [pow_succ]; ring

end DirectedHamiltonicity.Main.CycleReduction

namespace DirectedHamiltonicity.Main.CycleReduction
theorem ceil_bounds {q : ℚ} (hq : 1 ≤ q) (n : ℕ) :
    (q : ℝ)^n ≤ (⌈q^n⌉₊ : ℕ) ∧ ((⌈q^n⌉₊ : ℕ):ℝ) ≤ 2*(q : ℝ)^n := by
  have one := one_le_pow₀ hq (n := n)
  have lo := Nat.le_ceil (q^n)
  have hi := Nat.ceil_lt_add_one (show 0 ≤ q^n by linarith)
  constructor
  · exact_mod_cast lo
  · exact_mod_cast (show (⌈q^n⌉₊ : ℚ) ≤ 2*q^n by linarith)
end DirectedHamiltonicity.Main.CycleReduction

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling Classical

theorem tape_le_searchWork (A k n : ℕ) : coinCount n (coinSpan A k n) ≤ searchWork A k n := by
  unfold coinCount searchWork
  let M := trials n
  let r := 2*majorityHalf n
  let w := seedWidth n
  let L := coinSpan A k n
  change M*w+r*L ≤ (n*n+1)*(M+1)*(r+1)*(w+L+1)
  nlinarith only [Nat.zero_le (n*n*(M+1)*(r+1)*(w+L+1)),Nat.zero_le (M*r*(w+L+1)),
    Nat.zero_le (M*L),Nat.zero_le (r*w),Nat.zero_le M,Nat.zero_le r,Nat.zero_le w,Nat.zero_le L]

private def cap (n : ℕ) := 64*(n+1)^2

private theorem size_mul (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (Nat.two_pow_pos _))

private theorem size_le (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem size_pow_bound (a b : ℕ) : (a^b).size ≤ a.size*b+1 := by
  have le := Nat.pow_le_pow_left (Nat.lt_size_self a).le b
  rw [←pow_mul] at le
  exact (Nat.size_le_size le).trans_eq Nat.size_pow

private theorem cap_facts (n : ℕ) :
    64 ≤ cap n ∧ n*n ≤ cap n ∧ Bmax n+1 ≤ cap n ∧ Wmax n ≤ cap n ∧
    outerBlocks n ≤ cap n ∧ n+n*n*3+6*(n-1)+1 ≤ cap n := by
  have sub := Nat.sub_le n 1
  have sq := Nat.mul_le_mul sub sub
  unfold cap Bmax Wmax outerBlocks
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [sub,sq,Nat.zero_le n,Nat.zero_le (n*n)]

theorem seedWidth_bound (n : ℕ) : seedWidth n ≤ (cap n)^3 := by
  obtain ⟨lo,nn,bw,ww,_,_⟩ := cap_facts n
  apply Nat.clog_le_of_le_pow
  rw [Fintype.card_congr (rankDraw n),Fintype.card_fin]
  refine (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) ?_)
  let S := cap n
  change (n*n*((50^(n*n)*(Wmax n)^(n*3))*(Bmax n+1))).size ≤ S^3
  have s1 := size_mul (n*n) ((50^(n*n)*Wmax n^(n*3))*(Bmax n+1))
  have s2 := size_mul (50^(n*n)*Wmax n^(n*3)) (Bmax n+1)
  have s3 := size_mul (50^(n*n)) (Wmax n^(n*3))
  have s4 := size_pow_bound 50 (n*n)
  have s5 := size_pow_bound (Wmax n) (n*3)
  have s50 : (50:ℕ).size=6 := by decide
  have nle : n ≤ S := by dsimp [S,cap];nlinarith
  have ww' : (Wmax n).size*(n*3) ≤ S*(S*3) := Nat.mul_le_mul ((size_le _).trans ww) (by omega)
  have cubic : 3*S^2+8*S+2 ≤ S^3 := by
    have t : 64 ≤ S := lo
    nlinarith [Nat.mul_le_mul_right (S*S) t,Nat.mul_le_mul_right S t]
  rw [s50] at s4
  exact (by nlinarith only [s1,s2,s3,s4,s5,ww', (size_le (n*n)).trans nn,(size_le _).trans bw,nn,cubic] :
    (n*n*((50^(n*n)*Wmax n^(n*3))*(Bmax n+1))).size ≤ S^3)

private theorem trial_bounds (n : ℕ) : (trials n : ℝ) ≤ (cap n:ℝ)^4*(50/49:ℝ)^n ∧
    majorityHalf n ≤ (cap n)^4 := by
  obtain ⟨lo,nn,bw,_,blocks,_⟩ := cap_facts n
  let S := cap n
  have nS : n ≤ S := by dsimp [S,cap];nlinarith
  have prod : n*n*(Bmax n+1) ≤ S*S := Nat.mul_le_mul nn bw
  have coef : 4*(n*n*(Bmax n+1))*outerBlocks n ≤ 4*S^3 := by
    calc
      _ ≤ 4*(S*S)*S := Nat.mul_le_mul (Nat.mul_le_mul_left _ prod) blocks
      _ = _ := by ring
  have eq : trials n = (4*(n*n*(Bmax n+1))*outerBlocks n)*outerCeil n := by
    unfold trials trialBlock;ring
  have c := (ceil_bounds (q := 50/49) (by norm_num) n).2
  rw [show ((50/49:ℚ):ℝ)=50/49 by norm_num] at c
  change (outerCeil n:ℝ) ≤ _ at c
  have c2 : outerCeil n ≤ 2^n := by
    apply Nat.ceil_le.mpr
    push_cast
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have loS : 64 ≤ S := lo
  have extra : 8*S^3 ≤ S^4 := by nlinarith only [Nat.mul_le_mul_right (S^3) loS,Nat.zero_le (S^3)]
  constructor
  · rw [eq,Nat.cast_mul]
    have q := mul_le_mul (Nat.cast_le (α := ℝ).mpr coef) c (by positivity) (by positivity)
    calc
      _ ≤ _ := q
      _ = (8*S^3:ℕ)*(50/49:ℝ)^n := by push_cast;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast extra) (by positivity)
  · have wid := size_mul (4*(n*n*(Bmax n+1))*outerBlocks n) (outerCeil n)
    have small := (Nat.size_le_size c2).trans_eq Nat.size_pow
    unfold majorityHalf
    rw [eq]
    have more : 8*S^3+4*S+2 ≤ S^4 := by
      have h : S ≤ S^3 := by simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 1≤S) (show 1≤3 by omega))
      nlinarith only [Nat.mul_le_mul_right (S^3) loS,h,loS]
    nlinarith only [wid,small,(size_le _).trans coef,nS,blocks,more]

private theorem prod_four {a b c d : ℕ} {x y z t : ℝ} (A : (a:ℝ)≤x) (B : (b:ℝ)≤y)
    (C : (c:ℝ)≤z) (D : (d:ℝ)≤t) : ((a*b*c*d:ℕ):ℝ) ≤ x*y*z*t := by
  simp only [Nat.cast_mul]
  have hx := (Nat.cast_nonneg (α:=ℝ) a).trans A
  have hy := (Nat.cast_nonneg (α:=ℝ) b).trans B
  have hz := (Nat.cast_nonneg (α:=ℝ) c).trans C
  exact mul_le_mul (mul_le_mul (mul_le_mul A B (Nat.cast_nonneg _) hx) C (Nat.cast_nonneg _)
    (mul_nonneg hx hy)) D (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hx hy) hz)

theorem work_absorbed (A k j : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
    (searchWork A k n:ℝ)*((n:ℝ)+1)^j ≤ C*(19133/10000:ℝ)^n := by
  let e := 2*(k+13)+j
  obtain ⟨R,pos,rate⟩ := exponent_budget e
  let K : ℝ := 24*(A+1:ℝ)*64^(k+13)
  refine ⟨K*R,by dsimp [K];positivity,fun n => ?_⟩
  let S : ℝ := cap n
  let x := (50/49:ℝ)^n
  let y := (15/8:ℝ)^n
  obtain ⟨lo,nn,_,_,_,dim⟩ := cap_facts n
  obtain ⟨mt,mr⟩ := trial_bounds n
  have one : 1 ≤ S := by dsimp [S];exact_mod_cast (show 1≤cap n by omega)
  have x1 : 1 ≤ x := one_le_pow₀ (by norm_num) 
  have y1 : 1 ≤ y := one_le_pow₀ (by norm_num)
  have c := (ceil_bounds (q := 15/8) (by norm_num) n).2
  rw [show ((15/8:ℚ):ℝ)=15/8 by norm_num] at c
  have span : (coinSpan A k n:ℝ) ≤ (A:ℝ)*(2*y)*S^k := by
    unfold coinSpan
    simp only [Nat.cast_mul,Nat.cast_pow]
    exact mul_le_mul (mul_le_mul_of_nonneg_left c (by positivity)) (pow_le_pow_left₀ (by positivity) (by dsimp only [S]; exact_mod_cast dim) _)
      (by positivity) (by positivity)
  have nCap : ((n*n+1:ℕ):ℝ) ≤ 2*S := by
    have h : ((n*n:ℕ):ℝ) ≤ S := by dsimp only [S];exact_mod_cast nn
    push_cast at h ⊢;linarith
  have mCap : ((trials n+1:ℕ):ℝ) ≤ 2*S^4*x := by
    have b : 1 ≤ S^4*x := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one) x1
    push_cast;change (trials n:ℝ) ≤ S^4*x at mt;linarith
  have rCap : ((2*majorityHalf n+1:ℕ):ℝ) ≤ 3*S^4 := by
    have m : (majorityHalf n:ℝ)≤S^4 := by dsimp only [S];exact_mod_cast mr
    push_cast;linarith [one_le_pow₀ one (n:=4)]
  have poly : S^k ≤ S^(k+4) := pow_le_pow_right₀ one (by omega)
  have upper : 1 ≤ S^(k+4)*y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one) y1
  have seed : (seedWidth n:ℝ) ≤ S^3 := by dsimp only [S];exact_mod_cast seedWidth_bound n
  have wCap : ((seedWidth n+coinSpan A k n+1:ℕ):ℝ) ≤ 2*((A:ℝ)+1)*S^(k+4)*y := by
    have se : (seedWidth n:ℝ) ≤ S^(k+4)*y :=
      (seed.trans (pow_le_pow_right₀ one (by omega))).trans (le_mul_of_one_le_right (by positivity) y1)
    have sp := span.trans (mul_le_mul_of_nonneg_left poly (by positivity : 0 ≤ (A:ℝ)*(2*y)))
    push_cast; nlinarith only [se,sp,upper]
  have all := prod_four nCap mCap rCap wCap
  unfold searchWork
  calc
    _ ≤ (2*S*(2*S^4*x)*(3*S^4)*(2*((A:ℝ)+1)*S^(k+4)*y))*((n:ℝ)+1)^j := mul_le_mul_of_nonneg_right all (by positivity)
    _ = K*(((n:ℝ)+1)^e * (x*y)) := by
      have eqS : S = 64*((n:ℝ)+1)^2 := by dsimp [S,cap];push_cast;rfl
      dsimp [K,e]
      rw [eqS]
      generalize (n:ℝ)+1 = u
      simp only [pow_add,pow_mul,mul_pow]
      ring
    _ ≤ K*(R*(19133/10000:ℝ)^n) := mul_le_mul_of_nonneg_left (rate n) (by dsimp [K];positivity)
    _ = _ := by ring

end DirectedHamiltonicity.Main.CycleReduction

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction

theorem solution :
    ∃ (P : TargetedSamplers.Program) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
        (∀ coins : List Bool, ∃ (cost : ℕ) (b : Bool),
          P.RunsIn (runTapes (encodeDigraph n adj) coins) cost (some [b]) ∧
          (cost : ℝ) ≤ C * (19133 / 10000 : ℝ) ^ n) ∧
        (n ≤ 1 → ∀ coins : List Bool,
          P.Outputs (runTapes (encodeDigraph n adj) coins) (some [smallCycleAnswer n adj])) ∧
        (¬ HasHamCycle n adj →
          ∀ coins : List Bool, ¬ P.Outputs (runTapes (encodeDigraph n adj) coins) (some [true])) ∧
        (HasHamCycle n adj → ∀ L : ℕ, C * (19133 / 10000 : ℝ) ^ n ≤ L →
          (2 / 3 : ℝ) ≤ outputProb P (encodeDigraph n adj) L [true]) := by
  classical
  obtain ⟨Q,A,k,bounded,correct⟩ := finite_coin_cycle_search
  obtain ⟨P,D,j,dpos,run⟩ := execute_cycle_search Q A k bounded
  obtain ⟨K,kpos,work⟩ := work_absorbed A k j
  refine ⟨P,(D+1)*K,by positivity,fun n adj => ?_⟩
  obtain ⟨small,sound,success⟩ := correct n adj
  let R := (19133/10000:ℝ)^n
  have nonneg : 0 ≤ R := by dsimp [R]; positivity
  have span : ((coinCount n (coinSpan A k n)):ℝ) ≤ (D+1)*K*R := by
    have c : (coinCount n (coinSpan A k n):ℝ) ≤ (searchWork A k n:ℝ) := by
      exact_mod_cast tape_le_searchWork A k n
    have one : (1:ℝ) ≤ ((n:ℝ)+1)^j := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    calc
      _ ≤ _ := c
      _ ≤ (searchWork A k n:ℝ)*((n:ℝ)+1)^j := le_mul_of_one_le_right (by positivity) one
      _ ≤ K*R := work n
      _ ≤ (D+1)*K*R := by nlinarith only [mul_nonneg (mul_nonneg dpos.le kpos.le) nonneg]
  have prints (c : List Bool) : P.Outputs (runTapes (encodeDigraph n adj) c) (some [answer Q A k adj c]) := by
    obtain ⟨_,⟨s,h,_,v⟩,_⟩ := run n adj c
    exact ⟨s,h,v⟩
  have prints_iff (c : List Bool) :
      P.Outputs (runTapes (encodeDigraph n adj) c) (some [true]) ↔ answer Q A k adj c = true := by
    obtain ⟨s,hs,sv⟩ := prints c
    constructor
    · rintro ⟨t,ht,tv⟩
      have st := Option.some.inj (hs.symm.trans ht)
      subst t
      simpa using sv.symm.trans tv
    · intro h
      exact ⟨s,hs,h ▸ sv⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro c
    obtain ⟨cost,exec,le⟩ := run n adj c
    refine ⟨cost,_,exec,le.trans ?_⟩
    calc
      _ = D*((searchWork A k n:ℝ)*((n:ℝ)+1)^j) := by ring
      _ ≤ D*(K*R) := mul_le_mul_of_nonneg_left (work n) dpos.le
      _ ≤ (D+1)*K*R := by nlinarith only [mul_nonneg kpos.le nonneg]
  · intro hn c
    rw [←small hn c]
    exact prints c
  · intro no c out
    exact no (sound c ((prints_iff c).1 out))
  · intro yes L large
    have long : coinCount n (coinSpan A k n) ≤ L := by exact_mod_cast span.trans large
    refine (success yes L long).trans_eq ?_
    unfold acceptsFraction outputProb
    apply congrArg (fun z : ℕ => (z:ℝ)/2^L)
    apply congrArg Finset.card
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (prints_iff _).symm
