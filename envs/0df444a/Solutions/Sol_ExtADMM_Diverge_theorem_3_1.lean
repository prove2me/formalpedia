-- Prove2me | solution 1 for ExtADMM.Diverge.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-28T03:07:58.333995+00:00
-- url     : https://prove2.me/submissions/d1425a3a-eaff-4d91-83ab-9826ce222878

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting




noncomputable section
namespace ExtADMM.Diverge.EAFresh
open Matrix

def normalLag (u v w : ℝ) (m : Fin 3 → ℝ) : ℝ :=
  -(m 0 * (u+v+w) + m 1 * (u+v+2*w) + m 2 * (u+2*v+2*w)) +
    ((u+v+w)^2 + (u+v+2*w)^2 + (u+2*v+2*w)^2)/2

def step1 (v w : ℝ) (m : Fin 3 → ℝ) : ℝ :=
  (-4*v-5*w+m 0+m 1+m 2)/3

def step2 (u w : ℝ) (m : Fin 3 → ℝ) : ℝ :=
  (-4*u-7*w+m 0+m 1+2*m 2)/6

def step3 (u v : ℝ) (m : Fin 3 → ℝ) : ℝ :=
  (-5*u-7*v+m 0+2*m 1+2*m 2)/9

lemma normalLag_gap1 (u v w : ℝ) (m : Fin 3 → ℝ) :
    normalLag u v w m - normalLag (step1 v w m) v w m =
      (3/2:ℝ)*(u-step1 v w m)^2 := by
  unfold normalLag step1
  ring

lemma normalLag_gap2 (u v w : ℝ) (m : Fin 3 → ℝ) :
    normalLag u v w m - normalLag u (step2 u w m) w m =
      (6/2:ℝ)*(v-step2 u w m)^2 := by
  unfold normalLag step2
  ring

lemma normalLag_gap3 (u v w : ℝ) (m : Fin 3 → ℝ) :
    normalLag u v w m - normalLag u v (step3 u v m) m =
      (9/2:ℝ)*(w-step3 u v m)^2 := by
  unfold normalLag step3
  ring

lemma square_minimum {f : ℝ → ℝ} {a c : ℝ} (hc : 0 < c)
    (h : ∀ x, f x - f a = c*(x-a)^2) (x : ℝ) :
    (∀ y, f x ≤ f y) ↔ x = a := by
  constructor
  · intro hm
    have hx := hm a
    have hh := h x
    have hs := sq_nonneg (x-a)
    have he : (x-a)^2=0 := by nlinarith
    nlinarith
  · rintro rfl y
    have hh := h y
    have hs := mul_nonneg hc.le (sq_nonneg (y-x))
    linarith

lemma normalLag_min1 (u v w : ℝ) (m : Fin 3 → ℝ) :
    (∀ y, normalLag u v w m ≤ normalLag y v w m) ↔ u=step1 v w m :=
  square_minimum (by norm_num : (0:ℝ)<3/2) (fun y => normalLag_gap1 y v w m) u

lemma normalLag_min2 (u v w : ℝ) (m : Fin 3 → ℝ) :
    (∀ y, normalLag u v w m ≤ normalLag u y w m) ↔ v=step2 u w m :=
  square_minimum (by norm_num : (0:ℝ)<6/2) (fun y => normalLag_gap2 u y w m) v

lemma normalLag_min3 (u v w : ℝ) (m : Fin 3 → ℝ) :
    (∀ y, normalLag u v w m ≤ normalLag u v y m) ↔ w=step3 u v m :=
  square_minimum (by norm_num : (0:ℝ)<9/2) (fun y => normalLag_gap3 u v y m) w

lemma native_lag (β : ℝ) (hβ : β ≠ 0) (u v w : Fin 1 → ℝ) (lam : Fin 3 → ℝ) :
    example310.augLag β u v w lam =
      β * normalLag (u 0) (v 0) (w 0) (fun i => lam i/β) := by
  simp [Problem.augLag, Problem.objective, Problem.residual, example310, instance31,
    col, a310_1, a310_2, a310_3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    normalLag]
  field_simp
  ring

end ExtADMM.Diverge.EAFresh



noncomputable section
namespace ExtADMM.Diverge.EAFresh
open Matrix

def stateMu (z : Fin 5 → ℝ) : Fin 3 → ℝ := ![z 2,z 3,z 4]
def first (z : Fin 5 → ℝ) : ℝ := step1 (z 0) (z 1) (stateMu z)
def second (z : Fin 5 → ℝ) : ℝ := step2 (first z) (z 1) (stateMu z)
def third (z : Fin 5 → ℝ) : ℝ := step3 (first z) (second z) (stateMu z)
def updateMu (z : Fin 5 → ℝ) : Fin 3 → ℝ :=
  stateMu z - first z • a310_1 - second z • a310_2 - third z • a310_3

def stateStep (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![second z, third z, updateMu z 0, updateMu z 1, updateMu z 2]

lemma stateStep_eq (z : Fin 5 → ℝ) : stateStep z = M310 *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [stateStep, updateMu, first, second, third, stateMu, step1, step2, step3,
      M310, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, a310_1,a310_2,a310_3] <;> ring

lemma stateMu_state (β : ℝ) (v w : Fin 1 → ℝ) (lam : Fin 3 → ℝ) :
    stateMu (stateVec β v w lam) = fun i => lam i/β := by
  ext i
  fin_cases i <;> rfl

lemma native_residual (u v w : Fin 1 → ℝ) :
    example310.residual u v w = u 0 • a310_1 + v 0 • a310_2 + w 0 • a310_3 := by
  ext i
  fin_cases i <;> simp [Problem.residual, example310, instance31, col,
    Matrix.mulVec, dotProduct, a310_1,a310_2,a310_3] <;> ring

lemma native_standing : example310.Standing := by
  refine ⟨convex_univ, isClosed_univ, convex_univ, isClosed_univ,
    convex_univ, isClosed_univ, convexOn_const 0 convex_univ, convexOn_const 0 convex_univ,
    convexOn_const 0 convex_univ, 0, Set.mem_univ _, 0, Set.mem_univ _, 0, Set.mem_univ _, ?_, ?_⟩
  · simp [Problem.residual, example310, instance31]
  · intro y1 _ y2 _ y3 _ _
    rfl

end ExtADMM.Diverge.EAFresh



noncomputable section
namespace ExtADMM.Diverge.EAFresh
open Matrix

lemma every_run_coordinates (β : ℝ) (hβ : 0 < β)
    (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ)
    (hr : example310.IsRun15 β x1 x2 x3 lam) (k : ℕ) :
    let z := stateVec β (x2 k) (x3 k) (lam k)
    x1 (k+1) 0 = first z ∧ x2 (k+1) 0 = second z ∧ x3 (k+1) 0 = third z := by
  let m : Fin 3 → ℝ := fun i => lam k i / β
  have h1 : x1 (k+1) 0 = step1 (x2 k 0) (x3 k 0) m := by
    apply (normalLag_min1 _ _ _ _).mp
    intro y
    have h := (hr k).1.2 (fun _ => y) (Set.mem_univ _)
    rw [native_lag β hβ.ne', native_lag β hβ.ne'] at h
    exact (mul_le_mul_iff_right₀ hβ).mp h
  have h2 : x2 (k+1) 0 = step2 (x1 (k+1) 0) (x3 k 0) m := by
    apply (normalLag_min2 _ _ _ _).mp
    intro y
    have h := (hr k).2.1.2 (fun _ => y) (Set.mem_univ _)
    rw [native_lag β hβ.ne', native_lag β hβ.ne'] at h
    exact (mul_le_mul_iff_right₀ hβ).mp h
  have h3 : x3 (k+1) 0 = step3 (x1 (k+1) 0) (x2 (k+1) 0) m := by
    apply (normalLag_min3 _ _ _ _).mp
    intro y
    have h := (hr k).2.2.1.2 (fun _ => y) (Set.mem_univ _)
    rw [native_lag β hβ.ne', native_lag β hβ.ne'] at h
    exact (mul_le_mul_iff_right₀ hβ).mp h
  dsimp only
  dsimp only [first, second, third]
  rw [stateMu_state]
  change x1 (k+1) 0 = step1 (x2 k 0) (x3 k 0) m ∧
    x2 (k+1) 0 = step2 (step1 (x2 k 0) (x3 k 0) m) (x3 k 0) m ∧
    x3 (k+1) 0 = step3 (step1 (x2 k 0) (x3 k 0) m)
      (step2 (step1 (x2 k 0) (x3 k 0) m) (x3 k 0) m) m
  exact ⟨h1, by simpa only [h1] using h2, by simpa only [h1, h2] using h3⟩

lemma every_run_state (β : ℝ) (hβ : 0 < β)
    (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ)
    (hr : example310.IsRun15 β x1 x2 x3 lam) (k : ℕ) :
    stateVec β (x2 (k+1)) (x3 (k+1)) (lam (k+1)) =
      M310 *ᵥ stateVec β (x2 k) (x3 k) (lam k) := by
  rw [← stateStep_eq]
  obtain ⟨h1,h2,h3⟩ := every_run_coordinates β hβ x1 x2 x3 lam hr k
  have hl := (hr k).2.2.2
  rw [native_residual] at hl
  have hmu : ∀ j, lam (k+1) j / β =
      updateMu (stateVec β (x2 k) (x3 k) (lam k)) j := by
    intro j
    have he := congrFun hl j
    change lam (k+1) j = lam k j - β *
      (x1 (k+1) 0 * a310_1 j + x2 (k+1) 0 * a310_2 j + x3 (k+1) 0 * a310_3 j) at he
    change lam (k+1) j / β = stateMu (stateVec β (x2 k) (x3 k) (lam k)) j -
      first (stateVec β (x2 k) (x3 k) (lam k)) * a310_1 j -
      second (stateVec β (x2 k) (x3 k) (lam k)) * a310_2 j -
      third (stateVec β (x2 k) (x3 k) (lam k)) * a310_3 j
    rw [stateMu_state, he, h1, h2, h3]
    field_simp
    ring
  ext i
  fin_cases i
  · exact h2
  · exact h3
  · exact hmu 0
  · exact hmu 1
  · exact hmu 2

end ExtADMM.Diverge.EAFresh



noncomputable section
namespace ExtADMM.Diverge.EAFresh
open Matrix

lemma stateMu_step (z : Fin 5 → ℝ) : stateMu (stateStep z) = updateMu z := by
  ext i
  fin_cases i <;> rfl

lemma run_exists (β : ℝ) (hβ : 0 < β) (v w : Fin 1 → ℝ) (l : Fin 3 → ℝ) :
    ∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
      example310.IsRun15 β x1 x2 x3 lam ∧ x2 0=v ∧ x3 0=w ∧ lam 0=l := by
  let z : ℕ → Fin 5 → ℝ := Nat.rec (stateVec β v w l) (fun _ p => stateStep p)
  have hz : ∀ n, z (n+1)=stateStep (z n) := fun _ => rfl
  let x1 : ℕ → Fin 1 → ℝ := fun n => match n with
    | 0 => 0
    | n+1 => fun _ => first (z n)
  let x2 : ℕ → Fin 1 → ℝ := fun n _ => z n 0
  let x3 : ℕ → Fin 1 → ℝ := fun n _ => z n 1
  let lam : ℕ → Fin 3 → ℝ := fun n => β • stateMu (z n)
  have hm : ∀ n, (fun i => lam n i / β) = stateMu (z n) := by
    intro n
    ext i
    simp [lam, hβ.ne']
  refine ⟨x1,x2,x3,lam,?_,?_,?_,?_⟩
  · intro k
    refine ⟨⟨Set.mem_univ _, ?_⟩, ⟨Set.mem_univ _, ?_⟩,
      ⟨Set.mem_univ _, ?_⟩, ?_⟩
    · intro y _
      rw [native_lag β hβ.ne', native_lag β hβ.ne', hm]
      apply mul_le_mul_of_nonneg_left _ hβ.le
      exact (normalLag_min1 (first (z k)) (z k 0) (z k 1) (stateMu (z k))).mpr rfl (y 0)
    · intro y _
      rw [native_lag β hβ.ne', native_lag β hβ.ne', hm]
      apply mul_le_mul_of_nonneg_left _ hβ.le
      change normalLag (first (z k)) (z (k+1) 0) (z k 1) (stateMu (z k)) ≤
        normalLag (first (z k)) (y 0) (z k 1) (stateMu (z k))
      rw [hz]
      exact (normalLag_min2 (first (z k)) (second (z k)) (z k 1) (stateMu (z k))).mpr rfl (y 0)
    · intro y _
      rw [native_lag β hβ.ne', native_lag β hβ.ne', hm]
      apply mul_le_mul_of_nonneg_left _ hβ.le
      change normalLag (first (z k)) (z (k+1) 0) (z (k+1) 1) (stateMu (z k)) ≤
        normalLag (first (z k)) (z (k+1) 0) (y 0) (stateMu (z k))
      rw [hz]
      exact (normalLag_min3 (first (z k)) (second (z k)) (third (z k))
        (stateMu (z k))).mpr rfl (y 0)
    · rw [native_residual]
      change β • stateMu (z (k+1)) = β • stateMu (z k) -
        β • (first (z k) • a310_1 + z (k+1) 0 • a310_2 + z (k+1) 1 • a310_3)
      rw [hz, stateMu_step]
      change β • updateMu (z k) = β • stateMu (z k) -
        β • (first (z k) • a310_1 + second (z k) • a310_2 + third (z k) • a310_3)
      ext i
      simp [updateMu]
      ring
  · ext i
    fin_cases i
    rfl
  · ext i
    fin_cases i
    rfl
  · change β • stateMu (stateVec β v w l) = l
    rw [stateMu_state]
    ext i
    change β * (l i / β) = l i
    field_simp

end ExtADMM.Diverge.EAFresh



namespace ExtADMM.Diverge.EAFresh
open Filter Topology

lemma state_convergence (β : ℝ) (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ)
    (h : ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w)) :
    ∃ w, Tendsto (fun k => stateVec β (x2 k) (x3 k) (lam k)) atTop (𝓝 w) := by
  obtain ⟨w,hw⟩ := h
  refine ⟨stateVec β w.2.1 w.2.2.1 w.2.2.2, tendsto_pi_nhds.mpr ?_⟩
  intro i
  fin_cases i
  · exact tendsto_pi_nhds.mp hw.snd_nhds.fst_nhds 0
  · exact tendsto_pi_nhds.mp hw.snd_nhds.snd_nhds.fst_nhds 0
  · exact (tendsto_pi_nhds.mp hw.snd_nhds.snd_nhds.snd_nhds 0).div_const β
  · exact (tendsto_pi_nhds.mp hw.snd_nhds.snd_nhds.snd_nhds 1).div_const β
  · exact (tendsto_pi_nhds.mp hw.snd_nhds.snd_nhds.snd_nhds 2).div_const β

end ExtADMM.Diverge.EAFresh



noncomputable section
open ComplexConjugate
namespace ExtADMM.Diverge.EAFresh

lemma schur_two_roots (r s : ℂ) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    ‖(r+s)-(r*s)*conj (r+s)‖ ≤ 1-‖r*s‖^2 := by
  have hr0 := norm_nonneg r
  have hs0 := norm_nonneg s
  have hr2 : 0 ≤ 1-‖r‖^2 := by nlinarith
  have hs2 : 0 ≤ 1-‖s‖^2 := by nlinarith
  have he : (r+s)-(r*s)*conj (r+s) =
      r*((1-‖s‖^2 : ℝ):ℂ)+s*((1-‖r‖^2 : ℝ):ℂ) := by
    simp only [map_add, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
    rw [← Complex.mul_conj' s, ← Complex.mul_conj' r]
    ring
  have hn (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  have hab : 0 ≤ 1-‖r‖*‖s‖ := by nlinarith
  have hsum : ‖r‖+‖s‖ ≤ 1+‖r‖*‖s‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs)]
  calc
    _ ≤ ‖r‖*(1-‖s‖^2)+‖s‖*(1-‖r‖^2) := by
      rw [he]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul, hn _ hs2, hn _ hr2])
    _ = (‖r‖+‖s‖)*(1-‖r‖*‖s‖) := by ring
    _ ≤ (1+‖r‖*‖s‖)*(1-‖r‖*‖s‖) := mul_le_mul_of_nonneg_right hsum hab
    _ = 1-‖r*s‖^2 := by rw [norm_mul]; ring

lemma exterior_quadratic {B C : ℂ}
    (h : (1-‖C‖^2)^2 < ‖B-C*conj B‖^2) (_hC : ‖C‖ ≤ 1) :
    ∃ z : ℂ, z^2-B*z+C = 0 ∧ 1 < ‖z‖ := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (B^2-4*C) (n := 2) (by norm_num)
  let r : ℂ := (B+d)/2
  let s : ℂ := (B-d)/2
  have hrs : r+s = B := by dsimp [r,s]; ring
  have hprod : r*s = C := by
    dsimp [r,s]
    linear_combination -hd / 4
  have hrootr : r^2-B*r+C = 0 := by rw [← hrs, ← hprod]; ring
  have hroots : s^2-B*s+C = 0 := by rw [← hrs, ← hprod]; ring
  by_cases hr : 1 < ‖r‖
  · exact ⟨r,hrootr,hr⟩
  by_cases hs : 1 < ‖s‖
  · exact ⟨s,hroots,hs⟩
  have hh := schur_two_roots r s (le_of_not_gt hr) (le_of_not_gt hs)
  rw [hrs,hprod] at hh
  have hc0 := norm_nonneg C
  have hb0 := norm_nonneg (B-C*conj B)
  have hc2 : 0 ≤ 1-‖C‖^2 := by nlinarith
  nlinarith

end ExtADMM.Diverge.EAFresh



noncomputable section
open ComplexConjugate
namespace ExtADMM.Diverge.EAFresh

def coefB : ℂ := (301+Complex.I*(Real.sqrt 119 : ℂ))/162

def coefC : ℂ := coefB/2

def quartic (z : ℂ) : ℂ := 162*z^4-602*z^3+861*z^2-560*z+140

lemma coef_sum : coefB+conj coefB = (301:ℂ)/81 := by
  apply Complex.ext <;> norm_num [coefB, Complex.div_re, Complex.div_im]
  ring

lemma coef_product : coefB*conj coefB = (280:ℂ)/81 := by
  apply Complex.ext
  · norm_num [coefB, Complex.div_re, Complex.div_im]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 119 by norm_num)]
  · norm_num [coefB, Complex.div_re, Complex.div_im]
    ring

lemma coefC_norm_sq : ‖coefC‖^2 = (70:ℝ)/81 := by
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [coefC, coefB, Complex.normSq_apply, Complex.div_re, Complex.div_im]

lemma coef_gap_norm_sq : ‖coefB-coefC*conj coefB‖^2 = (140:ℝ)/6561 := by
  have he : coefB-coefC*conj coefB = coefB-(140:ℂ)/81 := by
    unfold coefC
    linear_combination -coef_product / 2
  rw [he, ← Complex.normSq_eq_norm_sq]
  norm_num [coefB, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 119 by norm_num)]

lemma quartic_factor (z : ℂ) :
    quartic z = 162*(z^2-coefB*z+coefC)*(z^2-conj coefB*z+conj coefC) := by
  have hs := coef_sum
  have hp := coef_product
  simp only [coefC, map_div₀, map_ofNat]
  unfold quartic
  linear_combination (162*z^3-81*z^2)*hs + (-162*z^2+162*z-81/2)*hp

lemma exists_exterior_root : ∃ z : ℂ, quartic z = 0 ∧ 1 < ‖z‖ := by
  have hc : ‖coefC‖ ≤ 1 := by
    have := coefC_norm_sq
    have := norm_nonneg coefC
    nlinarith
  have hg : (1-‖coefC‖^2)^2 < ‖coefB-coefC*conj coefB‖^2 := by
    rw [coefC_norm_sq, coef_gap_norm_sq]
    norm_num
  obtain ⟨z,hz,hn⟩ := exterior_quadratic hg hc
  refine ⟨z, ?_, hn⟩
  rw [quartic_factor, hz]
  ring

end ExtADMM.Diverge.EAFresh



noncomputable section
open Matrix
open scoped BigOperators
namespace ExtADMM.Diverge.EAFresh

def leftRow (z : ℂ) : Fin 5 → ℂ :=
  ![162*z^3-458*z^2+437*z-140, -9*z*(z-1), -9*(z-1)^2,
    -9*z^2+16*z-8, 18*z^2-34*z+17]

lemma left_row_identity (z : ℂ) (j : Fin 5) :
    (∑ i, leftRow z i*(M310 i j : ℂ)) =
      z*leftRow z j - if j=0 then quartic z else 0 := by
  fin_cases j <;> norm_num [leftRow, M310, Fin.sum_univ_succ, quartic] <;> ring

lemma left_row_eigen {z : ℂ} (hz : quartic z = 0) (j : Fin 5) :
    (∑ i, leftRow z i*(M310 i j : ℂ)) = z*leftRow z j := by
  rw [left_row_identity, hz]
  simp

lemma left_row_two_ne_zero {z : ℂ} (hz : 1 < ‖z‖) : leftRow z 2 ≠ 0 := by
  have h1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hz
  change -9*(z-1)^2 ≠ 0
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (sub_ne_zero.mpr h1))

def leftFunctional (z : ℂ) : (Fin 5 → ℝ) →ₗ[ℝ] ℂ where
  toFun x := ∑ i, leftRow z i*(x i : ℂ)
  map_add' x y := by
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i, leftRow z i*((c*x i : ℝ):ℂ)) = c • (∑ i, leftRow z i*(x i : ℂ))
    simp only [Complex.ofReal_mul, Complex.real_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma leftFunctional_step {z : ℂ} (hz : quartic z = 0) (x : Fin 5 → ℝ) :
    leftFunctional z (M310 *ᵥ x) = z*leftFunctional z x := by
  simp only [leftFunctional, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
    dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, (∑ i, leftRow z i*(M310 i j : ℂ))*(x j : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [left_row_eigen hz, mul_assoc]

lemma leftFunctional_single (z : ℂ) (i : Fin 5) :
    leftFunctional z (Pi.single i 1) = leftRow z i := by
  classical
  simp [leftFunctional, Pi.single_apply, apply_ite]

end ExtADMM.Diverge.EAFresh



noncomputable section
open Matrix
open Filter
open scoped Topology
namespace ExtADMM.Diverge.EAFresh

lemma leftFunctional_iterate {zeta : ℂ} (hzeta : quartic zeta = 0)
    (z : ℕ → Fin 5 → ℝ) (hz : ∀ n, z (n+1) = M310 *ᵥ z n) (n : ℕ) :
    leftFunctional zeta (z n) = zeta^n*leftFunctional zeta (z 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [hz n, leftFunctional_step hzeta, ih, pow_succ]; ring

lemma sequence_not_convergent {zeta : ℂ} (hzeta : quartic zeta = 0) (hn : 1 < ‖zeta‖)
    (z : ℕ → Fin 5 → ℝ) (hz : ∀ n, z (n+1) = M310 *ᵥ z n)
    (h0 : leftFunctional zeta (z 0) ≠ 0) :
    ¬ ∃ w, Tendsto z atTop (𝓝 w) := by
  rintro ⟨w, hw⟩
  have he := ((leftFunctional zeta).continuous_of_finiteDimensional.tendsto w).comp hw
  have hp : Tendsto (fun n : ℕ => ‖zeta‖^n*‖leftFunctional zeta (z 0)‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hn).atTop_mul_const (norm_pos_iff.mpr h0)
  have hnorm : Tendsto (fun n => ‖leftFunctional zeta (z n)‖) atTop atTop := by
    convert hp using 1
    ext n
    rw [leftFunctional_iterate hzeta z hz n, norm_mul, norm_pow]
  exact not_tendsto_nhds_of_tendsto_atTop hnorm _ he.norm

end ExtADMM.Diverge.EAFresh



noncomputable section
open Matrix
open Filter
open scoped Topology
namespace ExtADMM.Diverge.EAFresh

def coordinateSpace : Submodule ℝ (Fin 5 → ℝ) := Pi.spanSubset ℝ {0,1,2}

lemma coordinateSpace_dimension : Module.finrank ℝ coordinateSpace = 3 := by
  rw [coordinateSpace, Pi.dim_spanSubset]
  have he : ({0,1,2} : Set (Fin 5)) = (({0,1,2} : Finset (Fin 5)) : Set (Fin 5)) := by
    ext i
    simp
  rw [he, Set.ncard_coe_finset]
  decide

lemma single_two_mem : (Pi.single 2 1 : Fin 5 → ℝ) ∈ coordinateSpace := by
  apply Pi.mem_spanSubset_iff.mpr
  intro i hi
  have h : i ≠ 2 := by
    intro he
    subst i
    exact hi (by simp)
  simp [h]

lemma detecting_functional (ell : (Fin 5 → ℝ) →ₗ[ℝ] ℂ)
    (he : ell (Pi.single 2 1) ≠ 0) :
    ∃ φ : coordinateSpace →ₗ[ℝ] ℝ, φ ≠ 0 ∧
      ∀ z : coordinateSpace, 0 < φ z → ell (z : Fin 5 → ℝ) ≠ 0 := by
  let e : coordinateSpace := ⟨Pi.single 2 1, single_two_mem⟩
  by_cases hr : (ell (Pi.single 2 1)).re = 0
  · have hi : (ell (Pi.single 2 1)).im ≠ 0 := by
      intro h
      apply he
      exact Complex.ext hr h
    let φ := (Complex.imLm.comp ell).comp coordinateSpace.subtype
    refine ⟨φ, ?_, ?_⟩
    · intro h
      have hh := LinearMap.congr_fun h e
      exact hi hh
    · intro z hz hzero
      change 0 < (ell (z : Fin 5 → ℝ)).im at hz
      rw [hzero] at hz
      norm_num at hz
  · let φ := (Complex.reLm.comp ell).comp coordinateSpace.subtype
    refine ⟨φ, ?_, ?_⟩
    · intro h
      have hh := LinearMap.congr_fun h e
      exact hr hh
    · intro z hz hzero
      change 0 < (ell (z : Fin 5 → ℝ)).re at hz
      rw [hzero] at hz
      norm_num at hz

lemma unstable_halfspace :
    ∃ S : Submodule ℝ (Fin 5 → ℝ), Module.finrank ℝ S = 3 ∧
      ∃ φ : S →ₗ[ℝ] ℝ, φ ≠ 0 ∧
        ∀ (z : ℕ → Fin 5 → ℝ) (hmem : z 0 ∈ S), 0 < φ ⟨z 0,hmem⟩ →
          (∀ n, z (n+1) = M310 *ᵥ z n) → ¬ ∃ w, Tendsto z atTop (𝓝 w) := by
  obtain ⟨zeta,hzeta,hn⟩ := exists_exterior_root
  have he : leftFunctional zeta (Pi.single 2 1) ≠ 0 := by
    rw [leftFunctional_single]
    exact left_row_two_ne_zero hn
  obtain ⟨φ,hφ,hdetect⟩ := detecting_functional (leftFunctional zeta) he
  refine ⟨coordinateSpace,coordinateSpace_dimension,φ,hφ,?_⟩
  intro z hmem hz hrec
  exact sequence_not_convergent hzeta hn z hrec (hdetect ⟨z 0,hmem⟩ hz)

end ExtADMM.Diverge.EAFresh



namespace ExtADMM.Diverge.EAFresh
open Matrix Filter Topology

theorem native_theorem_3_1 :
    example310.Standing ∧
    ∃ S : Submodule ℝ (Fin 5 → ℝ), Module.finrank ℝ S = 3 ∧ ∃ φ : S →ₗ[ℝ] ℝ, φ ≠ 0 ∧
      ∀ β : ℝ, 0 < β → ∀ (x20 x30 : Fin 1 → ℝ) (lam0 : Fin 3 → ℝ)
        (hz : stateVec β x20 x30 lam0 ∈ S), 0 < φ ⟨_, hz⟩ →
          (∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
              example310.IsRun15 β x1 x2 x3 lam ∧ x2 0 = x20 ∧ x3 0 = x30 ∧ lam 0 = lam0) ∧
          ∀ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
            example310.IsRun15 β x1 x2 x3 lam → x2 0 = x20 → x3 0 = x30 → lam 0 = lam0 →
              ¬ ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w) := by
  obtain ⟨S,hS,φ,hφ,hd⟩ := unstable_halfspace
  refine ⟨native_standing,S,hS,φ,hφ,?_⟩
  intro β hβ v w l hz hp
  refine ⟨run_exists β hβ v w l, ?_⟩
  intro x1 x2 x3 lam hr h2 h3 hl ht
  let z := fun k => stateVec β (x2 k) (x3 k) (lam k)
  have hz0 : z 0 = stateVec β v w l := by simp only [z,h2,h3,hl]
  have hmem : z 0 ∈ S := hz0.symm ▸ hz
  have hpos : 0 < φ ⟨z 0,hmem⟩ := by simpa only [hz0] using hp
  exact hd z hmem hpos (every_run_state β hβ x1 x2 x3 lam hr)
    (state_convergence β x1 x2 x3 lam ht)

end ExtADMM.Diverge.EAFresh



namespace ExtADMM.Diverge
open Matrix Filter Topology

theorem theorem_3_1 :
    example310.Standing ∧
    ∃ S : Submodule ℝ (Fin 5 → ℝ), Module.finrank ℝ S = 3 ∧ ∃ φ : S →ₗ[ℝ] ℝ, φ ≠ 0 ∧
      ∀ β : ℝ, 0 < β → ∀ (x20 x30 : Fin 1 → ℝ) (lam0 : Fin 3 → ℝ)
        (hz : stateVec β x20 x30 lam0 ∈ S), 0 < φ ⟨_, hz⟩ →
          (∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
              example310.IsRun15 β x1 x2 x3 lam ∧ x2 0 = x20 ∧ x3 0 = x30 ∧ lam 0 = lam0) ∧
          ∀ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
            example310.IsRun15 β x1 x2 x3 lam → x2 0 = x20 → x3 0 = x30 → lam 0 = lam0 →
              ¬ ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w) := by
  exact EAFresh.native_theorem_3_1

end ExtADMM.Diverge


open Matrix Filter Topology ExtADMM.Diverge
theorem solution :
    example310.Standing ∧
    ∃ S : Submodule ℝ (Fin 5 → ℝ), Module.finrank ℝ S = 3 ∧ ∃ φ : S →ₗ[ℝ] ℝ, φ ≠ 0 ∧
      ∀ β : ℝ, 0 < β → ∀ (x20 x30 : Fin 1 → ℝ) (lam0 : Fin 3 → ℝ)
        (hz : stateVec β x20 x30 lam0 ∈ S), 0 < φ ⟨_, hz⟩ →
          (∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
              example310.IsRun15 β x1 x2 x3 lam ∧ x2 0 = x20 ∧ x3 0 = x30 ∧ lam 0 = lam0) ∧
          ∀ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
            example310.IsRun15 β x1 x2 x3 lam → x2 0 = x20 → x3 0 = x30 → lam 0 = lam0 →
              ¬ ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w) := by
  exact ExtADMM.Diverge.theorem_3_1 
