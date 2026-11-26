-- Prove2me | solution 1 for GRH.dirichlet_quartic_twenty_nine_first_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:46:54.408205+00:00
-- url     : https://prove2.me/submissions/694faf9d-76b2-48eb-91bc-987da89941b8

import Theorems.Thm_GRH_dirichlet_rectangle_of_individual_prefix_table
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Complex GRH.CharacterMoment

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private abbrev GPair := ℤ × ℤ
private def zval (u : GPair) : ℂ := ⟨u.1,u.2⟩
private def phase (n : ℕ) : GPair :=
  match n%4 with
  | 0 => (1,0)
  | 1 => (0,1)
  | 2 => (-1,0)
  | _ => (0,-1)

private lemma phase_eq (n : ℕ) : zval (phase n)=Complex.I^n := by
  rw [Complex.I_pow_eq_pow_mod]
  have hm := Nat.mod_lt n (by decide : 0<4)
  have al : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases al with h|h|h|h <;> apply Complex.ext <;> norm_num [zval,phase,h,pow_succ,Complex.mul_re,Complex.mul_im]

private lemma zadd (a b : GPair) : zval (a+b)=zval a+zval b := by
  apply Complex.ext <;> simp [zval]

private def exps : Array ℕ := #[0, 0, 1, 5, 2, 22, 6, 12, 3, 10, 23, 25,
  7, 18, 13, 27, 4, 21, 11, 9, 24, 17, 26, 20,
  8, 16, 19, 15, 14]
private def exponent (r : ℕ) := read exps (r%29)
private def valueTable : Array GPair := #[⟨-1,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨-1,0⟩, ⟨-1,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,1⟩,
  ⟨0,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,2⟩, ⟨-1,2⟩, ⟨-1,3⟩, ⟨-1,3⟩, ⟨-1,3⟩, ⟨-1,3⟩, ⟨0,3⟩,
  ⟨0,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,4⟩, ⟨1,4⟩, ⟨1,4⟩, ⟨0,4⟩,
  ⟨0,4⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,2⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,2⟩,
  ⟨0,2⟩, ⟨1,2⟩, ⟨1,2⟩, ⟨1,2⟩, ⟨1,2⟩, ⟨2,2⟩, ⟨2,2⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨3,1⟩,
  ⟨3,1⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨4,2⟩, ⟨4,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨2,2⟩,
  ⟨2,2⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,2⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨2,3⟩, ⟨2,3⟩, ⟨2,3⟩, ⟨3,3⟩,
  ⟨3,3⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,3⟩, ⟨2,3⟩, ⟨2,3⟩, ⟨2,3⟩, ⟨2,3⟩, ⟨2,2⟩,
  ⟨2,2⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,2⟩, ⟨2,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨4,2⟩,
  ⟨4,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,2⟩, ⟨3,1⟩, ⟨3,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,1⟩, ⟨2,2⟩,
  ⟨2,2⟩, ⟨1,2⟩, ⟨1,2⟩, ⟨1,2⟩, ⟨1,2⟩, ⟨0,2⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,2⟩,
  ⟨0,2⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨0,4⟩, ⟨0,4⟩, ⟨1,4⟩, ⟨1,4⟩, ⟨1,4⟩, ⟨1,4⟩, ⟨1,3⟩,
  ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨1,3⟩, ⟨0,3⟩, ⟨0,3⟩, ⟨-1,3⟩, ⟨-1,3⟩, ⟨-1,3⟩, ⟨-1,3⟩, ⟨-1,2⟩,
  ⟨-1,2⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨0,1⟩, ⟨0,1⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨-1,0⟩,
  ⟨-1,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨-1,0⟩]
private def centeredValue (r : ℕ) : GPair := (valueTable[r]?).getD 0
private def radii : Array ℕ := #[16, 0, 0, 0, 0, 16, 16, 0, 0, 0, 0, 16,
  16, 23, 23, 23, 23, 36, 36, 51, 51, 51, 51, 48,
  48, 51, 51, 51, 51, 51, 51, 66, 66, 66, 66, 64,
  64, 48, 48, 48, 48, 32, 32, 48, 48, 48, 48, 32,
  32, 36, 36, 36, 36, 46, 46, 36, 36, 36, 36, 51,
  51, 58, 58, 58, 58, 72, 72, 58, 58, 58, 58, 46,
  46, 36, 36, 36, 36, 46, 46, 58, 58, 58, 58, 68,
  68, 58, 58, 58, 58, 68, 68, 58, 58, 58, 58, 46,
  46, 36, 36, 36, 36, 46, 46, 58, 58, 58, 58, 72,
  72, 58, 58, 58, 58, 51, 51, 36, 36, 36, 36, 46,
  46, 36, 36, 36, 36, 32, 32, 48, 48, 48, 48, 32,
  32, 48, 48, 48, 48, 64, 64, 66, 66, 66, 66, 51,
  51, 51, 51, 51, 51, 48, 48, 51, 51, 51, 51, 36,
  36, 23, 23, 23, 23, 16, 16, 0, 0, 0, 0, 16,
  16, 0, 0, 0, 0, 16]
private def radius (r : ℕ) := read radii r

private def upper3Data : Array ℕ := #[0, 65536, 38968, 28751, 23171, 19600, 17095, 15229, 13778, 12613, 11655, 10851,
  10165, 9573, 9055, 8599, 8192, 7828, 7500, 7202, 6930, 6681, 6452, 6240,
  6044, 5862, 5692, 5533, 5385, 5245, 5113, 4989, 4871, 4760, 4655, 4555,
  4460, 4369, 4282, 4200, 4121, 4045, 3973, 3903, 3837, 3772, 3711, 3651,
  3594, 3539, 3486, 3435, 3385, 3337, 3290, 3245, 3202, 3160, 3119, 3079,
  3040, 3003, 2967, 2931, 2897, 2863, 2831, 2799, 2768, 2738, 2709, 2680,
  2652, 2625, 2598, 2572, 2547, 2522, 2497, 2474, 2450]
private def upper3 (n : ℕ) := read upper3Data n

private def upper5Data : Array ℕ := #[0, 65536, 36781, 26235, 20643, 17140, 14724, 12949, 11586, 10503, 9620, 8885,
  8264, 7731, 7268, 6862, 6502, 6182, 5895, 5635, 5399, 5184, 4987, 4806,
  4638, 4483, 4339, 4205, 4079, 3962, 3851, 3747, 3650, 3557, 3470, 3387,
  3308, 3234, 3163, 3095, 3030, 2969, 2910, 2853, 2799, 2747, 2697, 2649,
  2603]
private def upper5 (n : ℕ) := read upper5Data n

private def upper6Data : Array ℕ := #[0, 65536, 36179, 25558, 19973, 16496, 14109, 12363, 11026, 9967, 9107, 8392,
  7789, 7273, 6825, 6433, 6087, 5779, 5503, 5253, 5028, 4822, 4633, 4460,
  4300, 4152, 4015, 3887, 3768, 3656, 3552, 3453, 3361, 3273, 3190, 3112,
  3038, 2967, 2900, 2837, 2776, 2718, 2662, 2609, 2558, 2509, 2462, 2417,
  2374, 2333, 2293, 2254, 2217, 2181, 2146, 2113, 2080, 2049, 2019, 1989,
  1961, 1933, 1907, 1881, 1855]
private def upper6 (n : ℕ) := read upper6Data n

private def coeff (r : ℕ) : GPair := if r.Coprime 174 then phase (exponent r) else 0

private theorem logs : ∀ r : Fin 174, r.val.Coprime 174 →
    (2:ZMod 29)^(exponent r.val)=(r.val:ZMod 29) := by decide +kernel

private theorem steps : ∀ r : Fin 174, centeredValue ((r.val+1)%174) =
    centeredValue r.val + coeff ((r.val+1)%174) := by decide +kernel

private theorem squares : ∀ r : Fin 174,
    256*((centeredValue r.val).1^2+(centeredValue r.val).2^2)≤(radius r.val:ℤ)^2 := by decide +kernel

private theorem dvdLevel : 29∣174 := by decide

private lemma eval (χ : DirichletCharacter ℂ 29) (hχ : χ 2=I) (r : ℕ) (hr : r<174) :
    (DirichletCharacter.changeLevel dvdLevel χ) (r:ZMod 174)=zval (coeff r) := by
  by_cases hu : r.Coprime 174
  · have cast := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dvdLevel (ZMod.unitOfCoprime r hu)
    simp only [ZMod.coe_unitOfCoprime,ZMod.cast_natCast dvdLevel] at cast
    rw [cast,coeff,if_pos hu,phase_eq,← logs ⟨r,hr⟩ hu,map_pow,hχ]
  · rw [coeff,if_neg hu,show zval (0:GPair)=0 by apply Complex.ext <;> simp [zval]]
    exact MulChar.map_nonunit _ (fun u => hu ((ZMod.isUnit_iff_coprime _ _).1 u))

private lemma prefix_eq (χ : DirichletCharacter ℂ 29) (hχ : χ 2=I) (n : ℕ) :
    (∑ k ∈ Finset.range n, (DirichletCharacter.changeLevel dvdLevel χ) ((k+1:ℕ):ZMod 174))-1 =
      zval (centeredValue (n%174)) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero,zero_sub]
    change -(1:ℂ)=zval (-1,0)
    apply Complex.ext <;> norm_num [zval]
  | succ n ih =>
    have st := steps ⟨n%174,Nat.mod_lt _ (by decide)⟩
    change centeredValue ((n%174+1)%174)=centeredValue (n%174)+coeff ((n%174+1)%174) at st
    simp only [Nat.mod_add_mod] at st
    have hval := eval χ hχ ((n+1)%174) (Nat.mod_lt _ (by decide))
    rw [ZMod.natCast_mod] at hval
    rw [Finset.sum_range_succ,add_sub_right_comm,ih,st,zadd,hval]

private lemma disk (χ : DirichletCharacter ℂ 29) (hχ : χ 2=I) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n,(DirichletCharacter.changeLevel dvdLevel χ) ((k+1:ℕ):ZMod 174))-1‖ ≤
      (radius (n%174):ℝ)/16 := by
  rw [prefix_eq χ hχ]
  let r := n%174
  let a := centeredValue r
  let z : ℂ := zval a
  have nrm : ‖z‖^2=(a.1:ℝ)^2+(a.2:ℝ)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    change (a.1:ℝ)*(a.1:ℝ)+(a.2:ℝ)*(a.2:ℝ)=_
    ring
  have bd : (256:ℝ)*((a.1:ℝ)^2+(a.2:ℝ)^2)≤(radius r:ℝ)^2 := by
    exact_mod_cast squares ⟨r,Nat.mod_lt _ (by decide)⟩
  change ‖z‖≤(radius r:ℝ)/16
  nlinarith [sq_nonneg (‖z‖+(radius r:ℝ)/16),norm_nonneg z,Nat.cast_nonneg (α:=ℝ) (radius r)]

/-- The quartic character taking two to i is zero-free in three closed
rectangles extending leftward and upward from the first target grid. -/
theorem solution (χ : DirichletCharacter ℂ 29) (hχ : χ 2=Complex.I) (s : ℂ) (hb : s.re≤7/8)
    (h : ((3/4:ℝ)≤s.re ∧ |s.im|≤1) ∨ ((5/6:ℝ)≤s.re ∧ |s.im|≤3/2) ∨
      ((6/7:ℝ)≤s.re ∧ |s.im|≤7/4)) : χ.LFunction s≠0 := by
  have hne : χ≠1 := by
    intro he
    rw [he,MulChar.one_apply (x:=(2:ZMod 29)) ((ZMod.isUnit_iff_coprime 2 29).2 (by decide))] at hχ
    simpa using congrArg Complex.im hχ
  let ψ := DirichletCharacter.changeLevel dvdLevel χ
  have hn : ψ≠1 := fun he => hne ((DirichletCharacter.changeLevel_eq_one_iff dvdLevel).1 he)
  have hrad : ∀ r : Fin 174, radius r.val≤72 := by decide +kernel
  suffices ht : ψ.LFunction s≠0 by
    intro hz
    have lift := DirichletCharacter.LFunction_changeLevel dvdLevel χ (s:=s) (.inl hne)
    rw [hz,zero_mul] at lift
    exact ht lift
  rcases h with h|h|h
  · apply GRH.dirichlet_rectangle_of_individual_prefix_table 174 79 72 65536 16 3 4 178 100 ψ hn
      radius upper3 (3/4) (7/8) (1/1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by norm_num) (by norm_num) (disk χ hχ) hrad ?_ ?_ s h.1 hb (by simpa using h.2)
    · unfold GRH.DirichletPrefix.Table
      decide +kernel
    · decide +kernel
  · apply GRH.dirichlet_rectangle_of_individual_prefix_table 174 47 72 65536 16 5 6 209 100 ψ hn
      radius upper5 (5/6) (7/8) (3/2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by norm_num) (by norm_num) (disk χ hχ) hrad ?_ ?_ s h.1 hb (by simpa using h.2)
    · unfold GRH.DirichletPrefix.Table
      decide +kernel
    · decide +kernel
  · apply GRH.dirichlet_rectangle_of_individual_prefix_table 174 63 72 65536 16 6 7 229 100 ψ hn
      radius upper6 (6/7) (7/8) (7/4) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by norm_num) (by norm_num) (disk χ hχ) hrad ?_ ?_ s h.1 hb (by simpa using h.2)
    · unfold GRH.DirichletPrefix.Table
      decide +kernel
    · decide +kernel
