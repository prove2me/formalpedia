-- Prove2me | solution 1 for DefaultContagion.FinalSize.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:09:03.918249+00:00
-- url     : https://prove2.me/submissions/11ff19fc-344d-4c74-95f6-d862093df305

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DCFSA4
open DefaultContagion.FinalSize

/-- `z^a (1-z)^b`. -/
noncomputable def phi (a b : ℕ) (z : ℝ) : ℝ := z ^ a * (1 - z) ^ b

lemma phi_contDiff (a b : ℕ) (n : ℕ) : ContDiff ℝ n (phi a b) := by
  unfold phi; fun_prop

lemma deriv_phi (a b : ℕ) :
    deriv (phi a b) = fun z => (a : ℝ) * phi (a - 1) b z - (b : ℝ) * phi a (b - 1) z := by
  funext z
  have h1 : HasDerivAt (fun z : ℝ => z ^ a) ((a : ℝ) * z ^ (a - 1)) z := by
    simpa using hasDerivAt_pow a z
  have h2 : HasDerivAt (fun z : ℝ => (1 - z) ^ b) ((b : ℝ) * (1 - z) ^ (b - 1) * (-1)) z := by
    have := ((hasDerivAt_id z).const_sub 1).fun_pow b
    simpa using this
  have := h1.fun_mul h2
  unfold phi
  rw [this.deriv]
  ring

/-- Main derivative bound for `phi`. -/
lemma phi_bound (k : ℕ) : ∀ (a b : ℕ) (z M : ℝ), 1 ≤ M → |z| ≤ M → |1 - z| ≤ M →
    |iteratedDeriv k (phi a b) z| ≤ (2 * ((a + b : ℕ) : ℝ)) ^ k * M ^ (a + b) := by
  induction k with
  | zero =>
    intro a b z M hM hz h1z
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    unfold phi
    rw [abs_mul, abs_pow, abs_pow, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hz _)
      (pow_le_pow_left₀ (abs_nonneg _) h1z _) (by positivity) (by positivity)
  | succ k ih =>
    intro a b z M hM hz h1z
    rw [iteratedDeriv_succ', deriv_phi]
    have e : (fun z => (a : ℝ) * phi (a - 1) b z - (b : ℝ) * phi a (b - 1) z) =
        (fun z => (a : ℝ) * phi (a - 1) b z) - (fun z => (b : ℝ) * phi a (b - 1) z) := rfl
    rw [e, iteratedDeriv_sub, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    rotate_left
    · exact ((phi_contDiff _ _ k).const_smul (a : ℝ)).contDiffAt
    · exact ((phi_contDiff _ _ k).const_smul (b : ℝ)).contDiffAt
    have hA := ih (a - 1) b z M hM hz h1z
    have hB := ih a (b - 1) z M hM hz h1z
    have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
    have mono1 : (2 * (((a - 1) + b : ℕ) : ℝ)) ^ k * M ^ ((a - 1) + b) ≤
        (2 * ((a + b : ℕ) : ℝ)) ^ k * M ^ (a + b) := by
      apply mul_le_mul
      · apply pow_le_pow_left₀ (by positivity)
        have : ((a - 1 + b : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega)
        linarith
      · exact pow_le_pow_right₀ hM (by omega)
      · positivity
      · positivity
    have mono2 : (2 * ((a + (b - 1) : ℕ) : ℝ)) ^ k * M ^ (a + (b - 1)) ≤
        (2 * ((a + b : ℕ) : ℝ)) ^ k * M ^ (a + b) := by
      apply mul_le_mul
      · apply pow_le_pow_left₀ (by positivity)
        have : ((a + (b - 1) : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega)
        linarith
      · exact pow_le_pow_right₀ hM (by omega)
      · positivity
      · positivity
    set T := (2 * ((a + b : ℕ) : ℝ)) ^ k * M ^ (a + b) with hT
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hb0 : (0 : ℝ) ≤ b := by positivity
    calc |(a : ℝ) * iteratedDeriv k (phi (a - 1) b) z - (b : ℝ) * iteratedDeriv k (phi a (b - 1)) z|
        ≤ (a : ℝ) * T + (b : ℝ) * T := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_nonneg ha0]; exact mul_le_mul_of_nonneg_left (hA.trans mono1) ha0
          · rw [abs_mul, abs_of_nonneg hb0]; exact mul_le_mul_of_nonneg_left (hB.trans mono2) hb0
      _ ≤ (2 * ((a + b : ℕ) : ℝ)) ^ (k + 1) * M ^ (a + b) := by
          have hT0 : 0 ≤ T := by positivity
          have : (2 * ((a + b : ℕ) : ℝ)) ^ (k + 1) * M ^ (a + b) = T * (2 * ((a : ℝ) + b)) := by
            rw [hT]; push_cast; ring
          rw [this]
          nlinarith [hT0]

/-- Smooth with derivative bounds of the given degree. -/
def Good (f : ℝ → ℝ) (d : ℕ) (β : ℝ) : Prop :=
  (∀ n : ℕ, ContDiff ℝ n f) ∧ ∀ (k : ℕ) (z M : ℝ), 1 ≤ M → |z| ≤ M → |1 - z| ≤ M →
    |iteratedDeriv k f z| ≤ β * ((2 * (d : ℝ)) ^ k * M ^ d)

lemma Good.congr {f g : ℝ → ℝ} {d : ℕ} {β : ℝ} (h : Good f d β) (e : ∀ z, f z = g z) :
    Good g d β := by
  have : f = g := funext e
  subst this; exact h

lemma Good.mono {f : ℝ → ℝ} {d : ℕ} {β β' : ℝ} (h : Good f d β) (hb : β ≤ β') : Good f d β' := by
  refine ⟨h.1, fun k z M hM hz h1z => (h.2 k z M hM hz h1z).trans ?_⟩
  have : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  exact mul_le_mul_of_nonneg_right hb (by positivity)

lemma Good.mono_d {f : ℝ → ℝ} {d d' : ℕ} {β : ℝ} (h : Good f d β) (hd : d ≤ d') (hβ : 0 ≤ β) :
    Good f d' β := by
  refine ⟨h.1, fun k z M hM hz h1z => (h.2 k z M hM hz h1z).trans ?_⟩
  have : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  apply mul_le_mul_of_nonneg_left _ hβ
  apply mul_le_mul _ (pow_le_pow_right₀ hM hd) (by positivity) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have : (d : ℝ) ≤ d' := by exact_mod_cast hd
  linarith

lemma good_zero (d : ℕ) : Good (fun _ => 0) d 0 := by
  refine ⟨fun n => contDiff_const, fun k z M _ _ _ => ?_⟩
  rw [iteratedDeriv_const]; split_ifs <;> simp

lemma Good.add {f g : ℝ → ℝ} {d : ℕ} {β₁ β₂ : ℝ} (hf : Good f d β₁) (hg : Good g d β₂) :
    Good (fun z => f z + g z) d (β₁ + β₂) := by
  refine ⟨fun n => (hf.1 n).add (hg.1 n), fun k z M hM hz h1z => ?_⟩
  have e : (fun z => f z + g z) = f + g := rfl
  rw [e, iteratedDeriv_add ((hf.1 k).contDiffAt) ((hg.1 k).contDiffAt), add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hf.2 k z M hM hz h1z) (hg.2 k z M hM hz h1z))

lemma Good.smul {f : ℝ → ℝ} {d : ℕ} {β : ℝ} (hf : Good f d β) (c : ℝ) :
    Good (fun z => c * f z) d (|c| * β) := by
  refine ⟨fun n => (hf.1 n).const_smul c, fun k z M hM hz h1z => ?_⟩
  rw [iteratedDeriv_const_mul_field, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.2 k z M hM hz h1z) (abs_nonneg c)

lemma Good.sub {f g : ℝ → ℝ} {d : ℕ} {β₁ β₂ : ℝ} (hf : Good f d β₁) (hg : Good g d β₂) :
    Good (fun z => f z - g z) d (β₁ + β₂) := by
  have := hf.add (hg.smul (-1))
  simp only [abs_neg, abs_one, one_mul] at this
  exact this.congr (fun z => by ring)

lemma good_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (d : ℕ) (β : ι → ℝ)
    (h : ∀ i ∈ s, Good (f i) d (β i)) : Good (fun z => ∑ i ∈ s, f i z) d (∑ i ∈ s, β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero d
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    exact (h1.add h2).congr (fun z => by rw [Finset.sum_insert ha])

lemma good_phi (a b : ℕ) : Good (phi a b) (a + b) 1 := by
  refine ⟨phi_contDiff a b, fun k z M hM hz h1z => ?_⟩
  rw [one_mul]
  have := phi_bound k a b z M hM hz h1z
  simpa using this

lemma good_binPmf {d l : ℕ} (hl : l ≤ d) : Good (fun z => binPmf d z l) d (d.choose l) := by
  have h := (good_phi l (d - l)).smul (d.choose l : ℝ)
  rw [Nat.add_sub_cancel' hl] at h
  have h' : Good (fun z => binPmf d z l) d (|(d.choose l : ℝ)| * 1) :=
    h.congr (fun z => by unfold phi binPmf; ring)
  simpa using h'

lemma good_binTail (d l : ℕ) : Good (fun z => binTail d z l) d (2 ^ d) := by
  have h := good_sum (Finset.Icc l d) (fun r z => binPmf d z r) d (fun r => (d.choose r : ℝ))
    (fun r hr => good_binPmf (Finset.mem_Icc.1 hr).2)
  refine (h.congr (fun z => by rfl)).mono ?_
  have : ∑ r ∈ Finset.Icc l d, (d.choose r : ℝ) ≤ ∑ r ∈ Finset.range (d + 1), (d.choose r : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr; simp [Finset.mem_Icc] at hr; simp; omega
    · intros; positivity
  have h2 : ∑ r ∈ Finset.range (d + 1), (d.choose r : ℝ) = 2 ^ d := by
    exact_mod_cast Nat.sum_range_choose d
  linarith

lemma good_binMean (d l : ℕ) :
    Good (fun z => ∑ r ∈ Finset.Icc l d, (r : ℝ) * binPmf d z r) d (d * 2 ^ d) := by
  have h := good_sum (Finset.Icc l d) (fun r z => (r : ℝ) * binPmf d z r) d
    (fun r => (r : ℝ) * (d.choose r : ℝ))
    (fun r hr => by
      have := (good_binPmf (d := d) (l := r) (Finset.mem_Icc.1 hr).2).smul (r : ℝ)
      simpa using this)
  refine h.mono ?_
  have h1 : ∑ r ∈ Finset.Icc l d, (r : ℝ) * (d.choose r : ℝ) ≤
      ∑ r ∈ Finset.Icc l d, (d : ℝ) * (d.choose r : ℝ) :=
    Finset.sum_le_sum fun r hr => by
      have : (r : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.1 hr).2
      exact mul_le_mul_of_nonneg_right this (by positivity)
  have : ∑ r ∈ Finset.Icc l d, (d : ℝ) * (d.choose r : ℝ) ≤
      ∑ r ∈ Finset.range (d + 1), (d : ℝ) * (d.choose r : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr; simp [Finset.mem_Icc] at hr; simp; omega
    · intros; positivity
  have h2 : ∑ r ∈ Finset.range (d + 1), (d : ℝ) * (d.choose r : ℝ) = d * 2 ^ d := by
    rw [← Finset.mul_sum]; congr 1; exact_mod_cast Nat.sum_range_choose d
  linarith

/-- Per-type solvent function. -/
noncomputable def PS (d : ℕ) (r : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ θ ∈ Finset.Icc 1 d, r θ * binTail d z (d - θ + 1)

/-- Per-type healthy-ball function. -/
noncomputable def PH (d : ℕ) (r : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ θ ∈ Finset.Icc 1 d, r θ * ∑ l ∈ Finset.Icc (d - θ + 1) d, (l : ℝ) * binPmf d z l

noncomputable def rho (d : ℕ) (r : ℕ → ℝ) : ℝ := ∑ θ ∈ Finset.Icc 1 d, |r θ|

lemma rho_nonneg (d : ℕ) (r : ℕ → ℝ) : 0 ≤ rho d r := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma good_PS (d : ℕ) (r : ℕ → ℝ) : Good (PS d r) d (rho d r * 2 ^ d) := by
  have h := good_sum (Finset.Icc 1 d) (fun θ z => r θ * binTail d z (d - θ + 1)) d
    (fun θ => |r θ| * 2 ^ d) (fun θ _ => (good_binTail d _).smul (r θ))
  rw [← Finset.sum_mul] at h
  exact h.congr (fun z => rfl)

lemma good_PH (d : ℕ) (r : ℕ → ℝ) : Good (PH d r) d (rho d r * (d * 2 ^ d)) := by
  have h := good_sum (Finset.Icc 1 d)
    (fun θ z => r θ * ∑ l ∈ Finset.Icc (d - θ + 1) d, (l : ℝ) * binPmf d z l) d
    (fun θ => |r θ| * (d * 2 ^ d)) (fun θ _ => (good_binMean d _).smul (r θ))
  rw [← Finset.sum_mul] at h
  exact h.congr (fun z => rfl)

lemma good_one : Good (fun _ => 1) 0 1 := by
  have := good_binPmf (d := 0) (l := 0) le_rfl
  refine this.congr (fun z => by simp [binPmf]) |>.mono (by simp)

lemma good_linear (d : ℕ) : Good (fun z => (d : ℝ) * z) d d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simpa using good_zero 0
  · have h1 := good_binPmf (d := 1) (l := 1) le_rfl
    have h2 := (h1.mono_d hd (by simp)).smul (d : ℝ)
    refine (h2.congr (fun z => by simp [binPmf])).mono (by simp)

/-- Per-type contribution to the five fluid coordinates. -/
noncomputable def F (c : Fin 5) (d m : ℕ) (r : ℕ → ℝ) (z : ℝ) : ℝ :=
  ![PS d r z, 1 - PS d r z, PH d r z, (d : ℝ) * z - PH d r z, (d : ℝ) * z - (m : ℝ) * PS d r z] c

noncomputable def betaF (d m : ℕ) (ρ : ℝ) : ℝ := (1 + d + (1 + m + d) * ρ) * 2 ^ d

lemma good_F (c : Fin 5) (d m : ℕ) (r : ℕ → ℝ) : Good (F c d m r) d (betaF d m (rho d r)) := by
  have hρ := rho_nonneg d r
  have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hd : (0 : ℝ) ≤ d := by positivity
  have hm : (0 : ℝ) ≤ m := by positivity
  unfold betaF
  fin_cases c
  · refine ((good_PS d r).congr (fun z => by simp [F])).mono ?_
    nlinarith [mul_nonneg hρ (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg (mul_nonneg hρ (add_nonneg hm hd)) (by positivity : (0:ℝ) ≤ 2 ^ d)]
  · refine (((good_one.mono_d (Nat.zero_le d) zero_le_one).sub (good_PS d r)).congr
      (fun z => by simp [F])).mono ?_
    nlinarith [mul_nonneg hρ (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg (mul_nonneg hρ (add_nonneg hm hd)) (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg hd (by positivity : (0:ℝ) ≤ 2 ^ d)]
  · refine ((good_PH d r).congr (fun z => by simp [F])).mono ?_
    nlinarith [mul_nonneg hρ (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg (mul_nonneg hρ hm) (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg hd (by positivity : (0:ℝ) ≤ 2 ^ d)]
  · refine (((good_linear d).sub (good_PH d r)).congr (fun z => by simp [F])).mono ?_
    nlinarith [mul_nonneg hρ (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg (mul_nonneg hρ hm) (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg hd (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg hd (sub_nonneg.2 h2)]
  · refine (((good_linear d).sub ((good_PS d r).smul (m : ℝ))).congr
      (fun z => by simp [F])).mono ?_
    rw [abs_of_nonneg hm]
    nlinarith [mul_nonneg hρ (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg (mul_nonneg hρ hd) (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg hd (by positivity : (0:ℝ) ≤ 2 ^ d), mul_nonneg hd (sub_nonneg.2 h2)]

lemma PS_sub (d : ℕ) (r r' : ℕ → ℝ) (z : ℝ) :
    PS d r z - PS d r' z = PS d (fun θ => r θ - r' θ) z := by
  unfold PS; rw [← Finset.sum_sub_distrib]; congr 1; ext θ; ring

lemma PH_sub (d : ℕ) (r r' : ℕ → ℝ) (z : ℝ) :
    PH d r z - PH d r' z = PH d (fun θ => r θ - r' θ) z := by
  unfold PH; rw [← Finset.sum_sub_distrib]; congr 1; ext θ; ring

lemma good_Fdiff (c : Fin 5) (d m : ℕ) (r r' : ℕ → ℝ) :
    Good (fun z => F c d m r z - F c d m r' z) d
      ((1 + m + d) * rho d (fun θ => r θ - r' θ) * 2 ^ d) := by
  set ρ := rho d (fun θ => r θ - r' θ)
  have hρ : 0 ≤ ρ := rho_nonneg d _
  have hd : (0 : ℝ) ≤ d := by positivity
  have hm : (0 : ℝ) ≤ m := by positivity
  have hp : (0 : ℝ) ≤ 2 ^ d := by positivity
  fin_cases c
  · refine ((good_PS d (fun θ => r θ - r' θ)).congr (fun z => by simp [F, PS_sub])).mono ?_
    nlinarith [mul_nonneg (mul_nonneg hρ (add_nonneg hm hd)) hp]
  · refine (((good_PS d (fun θ => r θ - r' θ)).smul (-1)).congr (fun z => by
      simp only [F]; simp [← PS_sub])).mono ?_
    simp only [abs_neg, abs_one, one_mul]
    nlinarith [mul_nonneg (mul_nonneg hρ (add_nonneg hm hd)) hp]
  · refine ((good_PH d (fun θ => r θ - r' θ)).congr (fun z => by simp [F, PH_sub])).mono ?_
    nlinarith [mul_nonneg (mul_nonneg hρ hm) hp, mul_nonneg hρ hp]
  · refine (((good_PH d (fun θ => r θ - r' θ)).smul (-1)).congr (fun z => by
      simp only [F]; simp [← PH_sub])).mono ?_
    simp only [abs_neg, abs_one, one_mul]
    nlinarith [mul_nonneg (mul_nonneg hρ hm) hp, mul_nonneg hρ hp]
  · refine (((good_PS d (fun θ => r θ - r' θ)).smul (-(m : ℝ))).congr (fun z => by
      simp only [F]; simp [← PS_sub]; ring)).mono ?_
    rw [abs_neg, abs_of_nonneg hm]
    nlinarith [mul_nonneg (mul_nonneg hρ hd) hp, mul_nonneg hρ hp]

lemma iteratedDeriv_F_sub (c : Fin 5) (d m : ℕ) (r r' : ℕ → ℝ) (k : ℕ) (z : ℝ) :
    iteratedDeriv k (F c d m r) z - iteratedDeriv k (F c d m r') z =
      iteratedDeriv k (fun z => F c d m r z - F c d m r' z) z := by
  rw [← iteratedDeriv_sub ((good_F c d m r).1 k).contDiffAt ((good_F c d m r').1 k).contDiffAt]
  rfl

lemma rho_le_one {d : ℕ} {r : ℕ → ℝ} (h0 : ∀ θ, 0 ≤ r θ)
    (h1 : ∑ θ ∈ Finset.range (d + 1), r θ = 1) : rho d r ≤ 1 := by
  unfold rho
  rw [← h1]
  calc ∑ θ ∈ Finset.Icc 1 d, |r θ| = ∑ θ ∈ Finset.Icc 1 d, r θ :=
        Finset.sum_congr rfl fun θ _ => abs_of_nonneg (h0 θ)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro θ hθ; simp [Finset.mem_Icc] at hθ; simp; omega
      · intros; exact h0 _

/-! ### Elementary growth estimates -/

lemma poly_le_exp (j N : ℕ) : ((N : ℝ) + 1) ^ j ≤ 3 * (j.factorial : ℝ) * 3 ^ N := by
  have h := Real.pow_div_factorial_le_exp (x := (N : ℝ) + 1) (by positivity) j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h
  have he : Real.exp ((N : ℝ) + 1) ≤ 3 ^ (N + 1) := by
    have : Real.exp ((N : ℝ) + 1) = Real.exp 1 ^ (N + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith) _
  calc ((N : ℝ) + 1) ^ j ≤ Real.exp ((N : ℝ) + 1) * j.factorial := h
    _ ≤ 3 ^ (N + 1) * j.factorial := mul_le_mul_of_nonneg_right he hf.le
    _ = 3 * (j.factorial : ℝ) * 3 ^ N := by ring

lemma pow_eps (K0 a ε : ℝ) (hK0 : 0 ≤ K0) (ha : 0 < a) (hε : 0 < ε) :
    ∃ K, ∀ N : ℕ, K0 * a ^ N ≤ ε * (2 * a) ^ N + K := by
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt (K0 / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨K0 * a ^ N0 + K0 * 1, fun N => ?_⟩
  rcases le_or_gt N0 N with h | h
  · have h1 : K0 ≤ ε * 2 ^ N := by
      have : K0 / ε < 2 ^ N := hN0.trans_le (pow_le_pow_right₀ (by norm_num) h)
      rw [div_lt_iff₀ hε] at this; linarith
    have : K0 * a ^ N ≤ ε * (2 * a) ^ N := by
      rw [mul_pow]; nlinarith [pow_pos ha N]
    nlinarith [pow_pos ha N0, pow_pos ha N, pow_pos (by linarith : (0:ℝ) < 2 * a) N]
  · rcases le_or_gt a 1 with ha1 | ha1
    · have : a ^ N ≤ 1 := pow_le_one₀ ha.le ha1
      nlinarith [pow_pos ha N0, pow_pos (by linarith : (0:ℝ) < 2 * a) N, mul_le_mul_of_nonneg_left this hK0]
    · have : a ^ N ≤ a ^ N0 := pow_le_pow_right₀ ha1.le h.le
      nlinarith [pow_pos ha N0, pow_pos (by linarith : (0:ℝ) < 2 * a) N, mul_le_mul_of_nonneg_left this hK0]

lemma betaF_mono (d m : ℕ) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : betaF d m ρ ≤ betaF d m ρ' := by
  unfold betaF
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have : (0 : ℝ) ≤ 1 + m + d := by positivity
  nlinarith

/-- The key polynomial–exponential bound. -/
lemma beta_bound (k : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ K, 0 ≤ K ∧ ∀ d m : ℕ,
      betaF d m 2 * ((2 * (d : ℝ)) ^ k * M ^ d) ≤ K * ((6 * M) ^ (2 * d) + (6 * M) ^ (2 * m)) := by
  refine ⟨2 ^ (k + 2) * (3 * ((k + 1).factorial : ℝ)), by positivity, fun d m => ?_⟩
  set N := d + m
  have hM0 : 0 ≤ M := by linarith
  have hd : (d : ℝ) ≤ N + 1 := by simp [N]; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hb : betaF d m 2 ≤ 4 * ((N : ℝ) + 1) * 2 ^ d := by
    unfold betaF
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simp [N]; nlinarith [(m.cast_nonneg : (0:ℝ) ≤ m), (d.cast_nonneg : (0:ℝ) ≤ d)]
  have h2d : (2 * (d : ℝ)) ^ k ≤ 2 ^ k * ((N : ℝ) + 1) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hP := poly_le_exp (k + 1) N
  have hMd : (2 : ℝ) ^ d * M ^ d ≤ (2 * M) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_right₀ (by linarith) (by simp [N])
  have hsq : (6 * M) ^ N ≤ (6 * M) ^ (2 * d) + (6 * M) ^ (2 * m) := by
    have e : (6 * M) ^ N = (6 * M) ^ d * (6 * M) ^ m := by rw [← pow_add]
    have e1 : (6 * M) ^ (2 * d) = ((6 * M) ^ d) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    have e2 : (6 * M) ^ (2 * m) = ((6 * M) ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    rw [e, e1, e2]
    nlinarith [sq_nonneg ((6 * M) ^ d - (6 * M) ^ m), pow_nonneg (by linarith : (0:ℝ) ≤ 6 * M) d,
      pow_nonneg (by linarith : (0:ℝ) ≤ 6 * M) m]
  have hP' : ((N : ℝ) + 1) ^ (k + 1) * (2 * M) ^ N ≤ 3 * ((k + 1).factorial : ℝ) * (6 * M) ^ N := by
    have : (6 * M) ^ N = 3 ^ N * (2 * M) ^ N := by rw [← mul_pow]; ring_nf
    rw [this]
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 2 * M) N]
  have hN1 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  calc betaF d m 2 * ((2 * (d : ℝ)) ^ k * M ^ d)
      ≤ (4 * ((N : ℝ) + 1) * 2 ^ d) * (2 ^ k * ((N : ℝ) + 1) ^ k * M ^ d) := by
        apply mul_le_mul hb (mul_le_mul_of_nonneg_right h2d (by positivity)) (by positivity)
          (by positivity)
    _ = 2 ^ (k + 2) * (((N : ℝ) + 1) ^ (k + 1) * (2 ^ d * M ^ d)) := by ring
    _ ≤ 2 ^ (k + 2) * (((N : ℝ) + 1) ^ (k + 1) * (2 * M) ^ N) := by gcongr
    _ ≤ 2 ^ (k + 2) * (3 * ((k + 1).factorial : ℝ) * (6 * M) ^ N) := by gcongr
    _ ≤ 2 ^ (k + 2) * (3 * ((k + 1).factorial : ℝ)) * ((6 * M) ^ (2 * d) + (6 * M) ^ (2 * m)) := by
        rw [← mul_assoc]; gcongr

/-! ### Termwise differentiation -/

lemma iteratedDeriv_tsum_of_bound {ι : Type*} (f : ι → ℝ → ℝ) (hf : ∀ i (n : ℕ), ContDiff ℝ n (f i))
    (hb : ∀ (k : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i z, |z| ≤ R → |iteratedDeriv k (f i) z| ≤ u i)
    (k : ℕ) (z : ℝ) :
    iteratedDeriv k (fun z => ∑' i, f i z) z = ∑' i, iteratedDeriv k (f i) z := by
  rw [← iteratedDerivWithin_univ]
  rw [iteratedDerivWithin_tsum k isOpen_univ (Set.mem_univ z)]
  · simp [iteratedDerivWithin_univ]
  · intro t _
    obtain ⟨u, hu, hle⟩ := hb 0 |t|
    exact Summable.of_norm_bounded hu (fun i => by simpa using hle i t le_rfl)
  · intro j _ _
    apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
    intro K _ hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨u, hu, hle⟩ := hb j R
    refine ⟨u, hu, fun i y hy => ?_⟩
    have : |y| ≤ R := by simpa using hR hy
    simpa [iteratedDerivWithin_univ] using hle i y this
  · intro i j r _ _
    simp only [iteratedDerivWithin_univ]
    exact ((hf i (j + 1)).differentiable_iteratedDeriv' j).differentiableAt

/-! ### Weighted series over types -/

section Weighted
variable {X : Type*}

def Mom (dp dm : X → ℕ) (w : X → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ ∀ A : ℝ, 1 ≤ A →
    Summable (fun x => w x * A ^ (dp x)) ∧ Summable (fun x => w x * A ^ (dm x))

lemma Mom.summable_G {dp dm : X → ℕ} {w : X → ℝ} (h : Mom dp dm w) (M : ℝ) (hM : 1 ≤ M) :
    Summable (fun x => w x * ((6 * M) ^ (2 * dp x) + (6 * M) ^ (2 * dm x))) := by
  have hA : (1 : ℝ) ≤ (6 * M) ^ 2 := by nlinarith
  obtain ⟨h1, h2⟩ := h.2 ((6 * M) ^ 2) hA
  refine (h1.add h2).congr (fun x => ?_)
  rw [pow_mul, pow_mul]; ring

/-- Uniform bound on the `k`-th derivative of a weighted per-type term. -/
lemma Mom.bound {dp dm : X → ℕ} {w : X → ℝ} (h : Mom dp dm w) (c : Fin 5) (r : X → ℕ → ℝ)
    (hr : ∀ x, rho (dp x) (r x) ≤ 2) (k : ℕ) (R : ℝ) :
    ∃ u : X → ℝ, Summable u ∧ ∀ x z, |z| ≤ R →
      |iteratedDeriv k (fun z => w x * F c (dp x) (dm x) (r x) z) z| ≤ u x := by
  set M := |R| + 1
  have hM : 1 ≤ M := by simp [M]
  obtain ⟨K, hK0, hK⟩ := beta_bound k M hM
  refine ⟨fun x => K * (w x * ((6 * M) ^ (2 * dp x) + (6 * M) ^ (2 * dm x))),
    (h.summable_G M hM).mul_left K, fun x z hz => ?_⟩
  rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_nonneg (h.1 x)]
  have hzM : |z| ≤ M := by simp [M]; linarith [le_abs_self R]
  have h1z : |1 - z| ≤ M := by
    calc |1 - z| ≤ |(1 : ℝ)| + |z| := abs_sub _ _
      _ ≤ M := by simp [M]; linarith [le_abs_self R]
  have hg := (good_F c (dp x) (dm x) (r x)).2 k z M hM hzM h1z
  have hb := betaF_mono (dp x) (dm x) (hr x)
  have hpos : 0 ≤ (2 * (dp x : ℝ)) ^ k * M ^ dp x := by positivity
  calc w x * |iteratedDeriv k (F c (dp x) (dm x) (r x)) z|
      ≤ w x * (betaF (dp x) (dm x) 2 * ((2 * (dp x : ℝ)) ^ k * M ^ dp x)) := by
        apply mul_le_mul_of_nonneg_left _ (h.1 x)
        exact hg.trans (mul_le_mul_of_nonneg_right hb hpos)
    _ ≤ w x * (K * ((6 * M) ^ (2 * dp x) + (6 * M) ^ (2 * dm x))) :=
        mul_le_mul_of_nonneg_left (hK _ _) (h.1 x)
    _ = _ := by ring

lemma Mom.summable_F {dp dm : X → ℕ} {w : X → ℝ} (h : Mom dp dm w) (c : Fin 5) (r : X → ℕ → ℝ)
    (hr : ∀ x, rho (dp x) (r x) ≤ 2) (z : ℝ) :
    Summable (fun x => w x * F c (dp x) (dm x) (r x) z) := by
  obtain ⟨u, hu, hle⟩ := h.bound c r hr 0 |z|
  exact Summable.of_norm_bounded hu (fun x => by simpa using hle x z le_rfl)

lemma fVec_eq_tsum {dp dm : X → ℕ} {w : X → ℝ} (h : Mom dp dm w) (hw : HasSum w 1)
    (r : X → ℕ → ℝ) (hr : ∀ x, rho (dp x) (r x) ≤ 2) (c : Fin 5) (z : ℝ) :
    fVec dp dm (∑' x, w x * (dp x : ℝ)) w r z c = ∑' x, w x * F c (dp x) (dm x) (r x) z := by
  have hS := h.summable_F 0 r hr z
  have hH := h.summable_F 2 r hr z
  have hW := h.summable_F 4 r hr z
  have hd : Summable (fun x => w x * (dp x : ℝ) * z) := by
    have := (h.2 2 (by norm_num)).1
    refine (Summable.of_nonneg_of_le (fun x => mul_nonneg (h.1 x) (Nat.cast_nonneg _))
      (fun x => mul_le_mul_of_nonneg_left ?_ (h.1 x)) this).mul_right z
    have : (dp x : ℝ) < 2 ^ dp x := by exact_mod_cast Nat.lt_two_pow_self
    exact this.le
  fin_cases c
  · simp [fVec, F, fS, PS]
  · simp only [fVec, F, Fin.reduceFinMk, Matrix.cons_val]
    have e : ∑' x, w x * (1 - PS (dp x) (r x) z) = ∑' x, (w x - w x * PS (dp x) (r x) z) :=
      tsum_congr fun x => by ring
    rw [e, Summable.tsum_sub hw.summable (by simpa [F] using hS), hw.tsum_eq]
    rfl
  · simp [fVec, F, fH, PH]
  · simp only [fVec, F, Fin.reduceFinMk, Matrix.cons_val]
    have e : ∑' x, w x * ((dp x : ℝ) * z - PH (dp x) (r x) z) =
        ∑' x, (w x * (dp x : ℝ) * z - w x * PH (dp x) (r x) z) :=
      tsum_congr fun x => by ring
    rw [e, Summable.tsum_sub hd (by simpa [F] using hH), tsum_mul_right]
    rfl
  · simp only [fVec, F, Fin.reduceFinMk, Matrix.cons_val]
    have hm : Summable (fun x => w x * (dm x : ℝ) * PS (dp x) (r x) z) := by
      refine (hd.sub (by simpa [F] using hW)).congr (fun x => ?_)
      ring
    have e : ∑' x, w x * ((dp x : ℝ) * z - (dm x : ℝ) * PS (dp x) (r x) z) =
        ∑' x, (w x * (dp x : ℝ) * z - w x * (dm x : ℝ) * PS (dp x) (r x) z) :=
      tsum_congr fun x => by ring
    rw [e, Summable.tsum_sub hd hm, tsum_mul_right]
    rfl

lemma D_fVec {dp dm : X → ℕ} {w : X → ℝ} (h : Mom dp dm w) (hw : HasSum w 1)
    (r : X → ℕ → ℝ) (hr : ∀ x, rho (dp x) (r x) ≤ 2) (c : Fin 5) (k : ℕ) (z : ℝ) :
    iteratedDeriv k (fun z => fVec dp dm (∑' x, w x * (dp x : ℝ)) w r z c) z =
      ∑' x, w x * iteratedDeriv k (F c (dp x) (dm x) (r x)) z := by
  have e : (fun z => fVec dp dm (∑' x, w x * (dp x : ℝ)) w r z c) =
      fun z => ∑' x, w x * F c (dp x) (dm x) (r x) z :=
    funext fun z => fVec_eq_tsum h hw r hr c z
  rw [e, iteratedDeriv_tsum_of_bound (fun x z => w x * F c (dp x) (dm x) (r x) z)
    (fun x n => ((good_F c _ _ _).1 n).const_smul (w x)) (fun k R => h.bound c r hr k R)]
  exact tsum_congr fun x => iteratedDeriv_const_mul_field _ _

end Weighted

/-! ### Uniform convergence of weighted series -/

section Unif
variable {X : Type*}

lemma tail_bound (v f B G : X → ℝ) (F : Finset X) (C K η : ℝ)
    (hv : ∀ x, 0 ≤ v x) (hvs : HasSum v 1) (hvG : Summable (fun x => v x * G x))
    (hCG : ∑' x, v x * G x ≤ C) (hG0 : ∀ x, 0 ≤ G x)
    (hfB : ∀ x, |f x| ≤ B x) (hB : ∀ x, B x ≤ η * G x + K) (hη : 0 ≤ η) :
    Summable (fun x => v x * f x) ∧
    |∑' x : ↑((F : Set X)ᶜ), v x * f x| ≤ η * C + K * (1 - ∑ x ∈ F, v x) := by
  have hU : Summable (fun x => v x * (η * G x + K)) :=
    ((hvG.mul_left η).add (hvs.summable.mul_right K)).congr (fun x => by ring)
  have hle : ∀ x, ‖v x * f x‖ ≤ v x * (η * G x + K) := fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv x)]
    exact mul_le_mul_of_nonneg_left ((hfB x).trans (hB x)) (hv x)
  have hS : Summable (fun x => v x * f x) := Summable.of_norm_bounded hU hle
  refine ⟨hS, ?_⟩
  have hvc : ∑' x : ↑((F : Set X)ᶜ), v x = 1 - ∑ x ∈ F, v x := by
    have := hvs.summable.sum_add_tsum_compl (s := F)
    rw [hvs.tsum_eq] at this; linarith
  have hGc : ∑' x : ↑((F : Set X)ᶜ), v x * G x ≤ C :=
    (hvG.tsum_subtype_le _ _ (fun x => mul_nonneg (hv x) (hG0 x))).trans hCG
  have hSn : Summable (fun x : ↑((F : Set X)ᶜ) => ‖v x * f x‖) := by
    have h1 : Summable (fun x => ‖v x * f x‖) := Summable.of_nonneg_of_le
      (fun x => norm_nonneg _) hle hU
    exact h1.subtype _
  calc |∑' x : ↑((F : Set X)ᶜ), v x * f x|
      ≤ ∑' x : ↑((F : Set X)ᶜ), ‖v x * f x‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hSn
    _ ≤ ∑' x : ↑((F : Set X)ᶜ), v x * (η * G x + K) :=
        hSn.tsum_le_tsum (fun x => hle x) (hU.subtype _)
    _ = η * ∑' x : ↑((F : Set X)ᶜ), v x * G x + K * ∑' x : ↑((F : Set X)ᶜ), v x := by
        rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add]
        · exact tsum_congr fun x => by ring
        · exact (hvG.subtype _).mul_left η
        · exact (hvs.summable.subtype _).mul_left K
    _ ≤ η * C + K * (1 - ∑ x ∈ F, v x) := by
        rw [hvc]; nlinarith [mul_le_mul_of_nonneg_left hGc hη]

lemma unif_tsum (w : ℕ → X → ℝ) (w0 : X → ℝ) (a : ℕ → X → ℝ → ℝ) (a0 : X → ℝ → ℝ)
    (S : Set ℝ) (B G : X → ℝ) (C : ℝ)
    (hw : ∀ n x, 0 ≤ w n x) (hw0 : ∀ x, 0 ≤ w0 x)
    (hconv : ∀ x, Tendsto (fun n => w n x) atTop (𝓝 (w0 x)))
    (hsum : ∀ᶠ n in atTop, HasSum (w n) 1) (hsum0 : HasSum w0 1)
    (hG0 : ∀ x, 0 ≤ G x)
    (hGs : ∀ᶠ n in atTop, Summable (fun x => w n x * G x) ∧ ∑' x, w n x * G x ≤ C)
    (hGs0 : Summable (fun x => w0 x * G x) ∧ ∑' x, w0 x * G x ≤ C)
    (hB : ∀ ε > 0, ∃ K, ∀ x, B x ≤ ε * G x + K)
    (hab : ∀ n x z, z ∈ S → |a n x z| ≤ B x) (ha0b : ∀ x z, z ∈ S → |a0 x z| ≤ B x)
    (haconv : ∀ x, TendstoUniformlyOn (fun n z => a n x z) (a0 x) atTop S) :
    TendstoUniformlyOn (fun n z => ∑' x, w n x * a n x z) (fun z => ∑' x, w0 x * a0 x z)
      atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set η := ε / (8 * (|C| + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨K0, hK0⟩ := hB η hη
  set K := |K0| + 1 with hK_def
  have hKpos : 0 < K := by positivity
  have hBK : ∀ x, B x ≤ η * G x + K := fun x => (hK0 x).trans (by linarith [le_abs_self K0])
  set δ := ε / (16 * K) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨F, hF⟩ : ∃ F : Finset X, 1 - δ < ∑ x ∈ F, w0 x :=
    (hsum0.eventually (lt_mem_nhds (by linarith : 1 - δ < 1))).exists
  have hFn : ∀ᶠ n in atTop, 1 - 2 * δ < ∑ x ∈ F, w n x :=
    (tendsto_finsetSum F (fun x _ => hconv x)).eventually
      (lt_mem_nhds (by linarith : 1 - 2 * δ < ∑ x ∈ F, w0 x))
  set t := ε / (4 * ((F.card : ℝ) + 1)) with ht_def
  have ht : 0 < t := by positivity
  have hloc : ∀ x ∈ F, ∀ᶠ n in atTop, ∀ z ∈ S, |w0 x * a0 x z - w n x * a n x z| < t := by
    intro x _
    have h1 := (Metric.tendsto_nhds.1 (hconv x)) (t / (2 * (|B x| + 1))) (by positivity)
    have h3 := (Metric.tendsto_nhds.1 (hconv x)) 1 one_pos
    have h2 := (Metric.tendstoUniformlyOn_iff.1 (haconv x)) (t / (2 * (w0 x + 2)))
      (by have := hw0 x; positivity)
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3 z hz
    rw [Real.dist_eq] at hn1 hn3
    have hn2' := hn2 z hz
    rw [Real.dist_eq] at hn2'
    have hwn : w n x ≤ w0 x + 1 := by linarith [le_abs_self (w n x - w0 x)]
    have hab0 := ha0b x z hz
    have eq : w0 x * a0 x z - w n x * a n x z =
        (w0 x - w n x) * a0 x z + w n x * (a0 x z - a n x z) := by ring
    have hBx : 0 ≤ B x := (abs_nonneg _).trans hab0
    have e1 : |(w0 x - w n x) * a0 x z| ≤ t / 2 := by
      rw [abs_mul, abs_sub_comm]
      have : |w n x - w0 x| * B x ≤ t / (2 * (|B x| + 1)) * B x :=
        mul_le_mul_of_nonneg_right hn1.le hBx
      have h' : t / (2 * (|B x| + 1)) * B x ≤ t / 2 := by
        rw [abs_of_nonneg hBx, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc |w n x - w0 x| * |a0 x z| ≤ |w n x - w0 x| * B x :=
            mul_le_mul_of_nonneg_left hab0 (abs_nonneg _)
        _ ≤ t / 2 := this.trans h'
    have e2 : |w n x * (a0 x z - a n x z)| < t / 2 := by
      rw [abs_mul, abs_of_nonneg (hw n x)]
      have hw0x := hw0 x
      calc w n x * |a0 x z - a n x z| ≤ (w0 x + 1) * |a0 x z - a n x z| :=
            mul_le_mul_of_nonneg_right hwn (abs_nonneg _)
        _ ≤ (w0 x + 1) * (t / (2 * (w0 x + 2))) :=
            mul_le_mul_of_nonneg_left hn2'.le (by linarith)
        _ < t / 2 := by
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    rw [eq]
    exact (abs_add_le _ _).trans_lt (by linarith)
  have hall := (Filter.eventually_all_finset F).2 hloc
  filter_upwards [hsum, hGs, hFn, hall] with n hsn hGn hFn' hall' z hz
  obtain ⟨hS0, ht0⟩ := tail_bound w0 (fun x => a0 x z) B G F C K η hw0 hsum0 hGs0.1 hGs0.2 hG0
    (fun x => ha0b x z hz) hBK hη.le
  obtain ⟨hSn, htn⟩ := tail_bound (w n) (fun x => a n x z) B G F C K η (hw n) hsn hGn.1 hGn.2
    hG0 (fun x => hab n x z hz) hBK hη.le
  rw [Real.dist_eq, ← hS0.sum_add_tsum_compl (s := F), ← hSn.sum_add_tsum_compl (s := F)]
  have hfin : |∑ x ∈ F, w0 x * a0 x z - ∑ x ∈ F, w n x * a n x z| ≤ F.card * t := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ F, |w0 x * a0 x z - w n x * a n x z| ≤ ∑ x ∈ F, t :=
          Finset.sum_le_sum fun x hx => (hall' x hx z hz).le
      _ = F.card * t := by simp
  have hct : (F.card : ℝ) * t ≤ ε / 4 := by
    rw [ht_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hηC : η * C ≤ ε / 8 := by
    have : η * C ≤ η * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hη.le
    have h2 : η * |C| ≤ ε / 8 := by
      rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg C]
    linarith
  have hKδ : K * δ = ε / 16 := by rw [hδ_def]; field_simp
  have e : ∑ x ∈ F, w0 x * a0 x z + ∑' x : ↑((F : Set X)ᶜ), w0 x * a0 x z -
      (∑ x ∈ F, w n x * a n x z + ∑' x : ↑((F : Set X)ᶜ), w n x * a n x z) =
      (∑ x ∈ F, w0 x * a0 x z - ∑ x ∈ F, w n x * a n x z) +
      ∑' x : ↑((F : Set X)ᶜ), w0 x * a0 x z - ∑' x : ↑((F : Set X)ᶜ), w n x * a n x z := by ring
  rw [e]
  have k1 : K * (1 - ∑ x ∈ F, w0 x) ≤ K * δ := mul_le_mul_of_nonneg_left (by linarith) hKpos.le
  have k2 : K * (1 - ∑ x ∈ F, w n x) ≤ K * (2 * δ) := mul_le_mul_of_nonneg_left (by linarith) hKpos.le
  calc |(∑ x ∈ F, w0 x * a0 x z - ∑ x ∈ F, w n x * a n x z) +
        ∑' x : ↑((F : Set X)ᶜ), w0 x * a0 x z - ∑' x : ↑((F : Set X)ᶜ), w n x * a n x z|
      ≤ |∑ x ∈ F, w0 x * a0 x z - ∑ x ∈ F, w n x * a n x z| +
        |∑' x : ↑((F : Set X)ᶜ), w0 x * a0 x z| + |∑' x : ↑((F : Set X)ᶜ), w n x * a n x z| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by nlinarith

end Unif

/-! ### The finite-economy type weights -/

section Model
variable {X : Type*} [DecidableEq X]

lemma hasSum_muN (typ : (n : ℕ) → Fin n → X) (n : ℕ) (g : X → ℝ) :
    HasSum (fun x => muN typ n x * g x) ((∑ i : Fin n, g (typ n i)) / n) := by
  set s := Finset.univ.image (typ n)
  have h0 : ∀ x ∉ s, muN typ n x * g x = 0 := by
    intro x hx
    have : (Finset.univ.filter fun i : Fin n => typ n i = x) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro h; exact hx (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simp [muN, this]
  convert hasSum_sum_of_ne_finset_zero h0 using 1
  swap; · infer_instance
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s) (g := typ n)
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i)), Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const,
    nsmul_eq_mul, muN]
  ring

lemma muN_nonneg (typ : (n : ℕ) → Fin n → X) (n : ℕ) (x : X) : 0 ≤ muN typ n x := by
  unfold muN; positivity

lemma hasSum_muN_one (typ : (n : ℕ) → Fin n → X) {n : ℕ} (hn : 1 ≤ n) :
    HasSum (muN typ n) 1 := by
  have := hasSum_muN typ n (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rwa [div_self hn'] at this

lemma lamN_eq (dp : X → ℕ) (typ : (n : ℕ) → Fin n → X) (n : ℕ) :
    lamN dp typ n = ∑' x, muN typ n x * (dp x : ℝ) :=
  ((hasSum_muN typ n (fun x => (dp x : ℝ))).tsum_eq).symm

/-- Uniform exponential moments of the empirical type law. -/
lemma muN_mom (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X) (h3b : Assumption3b dp dm typ)
    (A : ℝ) (hA : 1 ≤ A) : ∃ C, ∀ n, 1 ≤ n →
      ∑' x, muN typ n x * A ^ (dp x) ≤ C ∧ ∑' x, muN typ n x * A ^ (dm x) ≤ C := by
  obtain ⟨C, hC⟩ := h3b (A + 1) (by linarith)
  refine ⟨C, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [(hasSum_muN typ n (fun x => A ^ (dp x))).tsum_eq, div_le_iff₀ hn']
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hC n).1
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  · rw [(hasSum_muN typ n (fun x => A ^ (dm x))).tsum_eq, div_le_iff₀ hn']
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hC n).2
    exact pow_le_pow_left₀ (by linarith) (by linarith) _

lemma muN_Mom (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X) (n : ℕ) :
    Mom dp dm (muN typ n) :=
  ⟨muN_nonneg typ n, fun A _ => ⟨(hasSum_muN typ n _).summable, (hasSum_muN typ n _).summable⟩⟩

/-- Fatou: the limit law inherits the exponential moments. -/
lemma fatou (w : ℕ → X → ℝ) (w0 : X → ℝ) (g : X → ℝ) (C : ℝ)
    (hw : ∀ n x, 0 ≤ w n x) (hg : ∀ x, 0 ≤ g x)
    (hconv : ∀ x, Tendsto (fun n => w n x) atTop (𝓝 (w0 x)))
    (hs : ∀ n, Summable (fun x => w n x * g x))
    (hC : ∀ᶠ n in atTop, ∑' x, w n x * g x ≤ C) :
    Summable (fun x => w0 x * g x) ∧ ∑' x, w0 x * g x ≤ C := by
  have hw0 : ∀ x, 0 ≤ w0 x := fun x =>
    ge_of_tendsto (hconv x) (Eventually.of_forall fun n => hw n x)
  have hF : ∀ F : Finset X, ∑ x ∈ F, w0 x * g x ≤ C := by
    intro F
    have ht : Tendsto (fun n => ∑ x ∈ F, w n x * g x) atTop (𝓝 (∑ x ∈ F, w0 x * g x)) :=
      tendsto_finsetSum F (fun x _ => (hconv x).mul_const (g x))
    refine le_of_tendsto ht ?_
    filter_upwards [hC] with n hn
    exact ((hs n).sum_le_tsum F (fun x _ => mul_nonneg (hw n x) (hg x))).trans hn
  have hsum : Summable (fun x => w0 x * g x) :=
    summable_of_sum_le (fun x => mul_nonneg (hw0 x) (hg x)) hF
  exact ⟨hsum, hsum.tsum_le_of_sum_le hF⟩

end Model

/-- Lemma A.4 in the form used below. -/
theorem lemmaA4_main {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3b : Assumption3b dp dm typ) (c : Fin 5) (k : ℕ) :
    TendstoUniformlyOn
        (fun n z => iteratedDeriv k
          (fun w => fVec dp dm (lamN dp typ n) (muN typ n) (qn n) w c) z)
        (fun z => iteratedDeriv k
          (fun w => fVec dp dm (∑' x, mu x * (dp x : ℝ)) mu q w c) z)
        atTop (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨hmu0, hmu1, hq, hqn, hmuconv, hqconv⟩ := h2
  have hMomMu : Mom dp dm mu := by
    refine ⟨hmu0, fun A hA => ?_⟩
    obtain ⟨C, hC⟩ := muN_mom dp dm typ h3b A hA
    refine ⟨(fatou (fun n => muN typ n) mu (fun x => A ^ (dp x)) C (muN_nonneg typ)
      (fun x => by positivity) hmuconv (fun n => (hasSum_muN typ n _).summable)
      (eventually_atTop.2 ⟨1, fun n hn => (hC n hn).1⟩)).1,
      (fatou (fun n => muN typ n) mu (fun x => A ^ (dm x)) C (muN_nonneg typ)
      (fun x => by positivity) hmuconv (fun n => (hasSum_muN typ n _).summable)
      (eventually_atTop.2 ⟨1, fun n hn => (hC n hn).2⟩)).1⟩
  have hrq : ∀ x, rho (dp x) (q x) ≤ 2 := fun x =>
    (rho_le_one (hq x).1 (hq x).2.2).trans (by norm_num)
  have hrqn : ∀ n x, rho (dp x) (qn n x) ≤ 2 := fun n x =>
    (rho_le_one ((hqn n) x).1 ((hqn n) x).2.2).trans (by norm_num)
  obtain ⟨C1, hC1⟩ := muN_mom dp dm typ h3b 72 (by norm_num)
  set G : X → ℝ := fun x => (72 : ℝ) ^ (dp x) + 72 ^ (dm x) with hG_def
  have hG0 : ∀ x, 0 ≤ G x := fun x => by positivity
  have hGn : ∀ n, 1 ≤ n → Summable (fun x => muN typ n x * G x) ∧
      ∑' x, muN typ n x * G x ≤ 2 * C1 := by
    intro n hn
    have s1 := (hasSum_muN typ n (fun x => (72 : ℝ) ^ (dp x))).summable
    have s2 := (hasSum_muN typ n (fun x => (72 : ℝ) ^ (dm x))).summable
    have e : (fun x => muN typ n x * G x) =
        fun x => muN typ n x * (72 : ℝ) ^ (dp x) + muN typ n x * 72 ^ (dm x) := by
      funext x; simp only [hG_def]; ring
    refine ⟨e ▸ s1.add s2, ?_⟩
    rw [e, Summable.tsum_add s1 s2]
    linarith [(hC1 n hn).1, (hC1 n hn).2]
  have hGs : ∀ᶠ n in atTop, Summable (fun x => muN typ n x * G x) ∧
      ∑' x, muN typ n x * G x ≤ 2 * C1 := eventually_atTop.2 ⟨1, hGn⟩
  have hGs0 := fatou (fun n => muN typ n) mu G (2 * C1) (muN_nonneg typ) hG0 hmuconv
    (fun n => (hasSum_muN typ n _).summable) (hGs.mono fun n h => h.2)
  set B : X → ℝ := fun x => betaF (dp x) (dm x) 2 * ((2 * (dp x : ℝ)) ^ k * 1 ^ (dp x))
    with hB_def
  obtain ⟨K1, hK1, hK1b⟩ := beta_bound k 1 le_rfl
  have hB : ∀ ε > 0, ∃ K, ∀ x, B x ≤ ε * G x + K := by
    intro ε hε
    obtain ⟨K, hK⟩ := pow_eps K1 36 ε hK1 (by norm_num) hε
    refine ⟨2 * K, fun x => (hK1b (dp x) (dm x)).trans ?_⟩
    have e1 : ((6 : ℝ) * 1) ^ (2 * dp x) = 36 ^ (dp x) := by rw [pow_mul]; norm_num
    have e2 : ((6 : ℝ) * 1) ^ (2 * dm x) = 36 ^ (dm x) := by rw [pow_mul]; norm_num
    rw [e1, e2]
    have h1 := hK (dp x)
    have h2 := hK (dm x)
    norm_num at h1 h2
    simp only [hG_def]
    nlinarith
  have hmem : ∀ z ∈ Set.Icc (0 : ℝ) 1, |z| ≤ 1 ∧ |1 - z| ≤ 1 := by
    intro z hz
    obtain ⟨h0, h1⟩ := hz
    exact ⟨abs_le.2 ⟨by linarith, h1⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  have hbd : ∀ (r : X → ℕ → ℝ), (∀ x, rho (dp x) (r x) ≤ 2) → ∀ x z, z ∈ Set.Icc (0 : ℝ) 1 →
      |iteratedDeriv k (F c (dp x) (dm x) (r x)) z| ≤ B x := by
    intro r hr x z hz
    obtain ⟨hz1, hz2⟩ := hmem z hz
    refine ((good_F c (dp x) (dm x) (r x)).2 k z 1 le_rfl hz1 hz2).trans ?_
    exact mul_le_mul_of_nonneg_right (betaF_mono _ _ (hr x)) (by positivity)
  have haconv : ∀ x, TendstoUniformlyOn
      (fun n z => iteratedDeriv k (F c (dp x) (dm x) (qn n x)) z)
      (fun z => iteratedDeriv k (F c (dp x) (dm x) (q x)) z) atTop (Set.Icc (0 : ℝ) 1) := by
    intro x
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set L : ℝ := (1 + dm x + dp x) * 2 ^ (dp x) * ((2 * (dp x : ℝ)) ^ k * 1 ^ (dp x)) with hL
    have hL0 : 0 ≤ L := by positivity
    have hrho : Tendsto (fun n => rho (dp x) (fun θ => q x θ - qn n x θ)) atTop (𝓝 0) := by
      have : Tendsto (fun n => ∑ θ ∈ Finset.Icc 1 (dp x), |q x θ - qn n x θ|) atTop
          (𝓝 (∑ θ ∈ Finset.Icc 1 (dp x), |q x θ - q x θ|)) :=
        tendsto_finsetSum _ (fun θ _ => ((tendsto_const_nhds.sub (hqconv x θ)).abs))
      simpa [rho] using this
    have hev := (Metric.tendsto_nhds.1 hrho) (ε / (L + 1)) (by positivity)
    filter_upwards [hev] with n hn z hz
    rw [Real.dist_eq, iteratedDeriv_F_sub]
    obtain ⟨hz1, hz2⟩ := hmem z hz
    have hb := (good_Fdiff c (dp x) (dm x) (q x) (qn n x)).2 k z 1 le_rfl hz1 hz2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (rho_nonneg _ _)] at hn
    have hρ0 := rho_nonneg (dp x) (fun θ => q x θ - qn n x θ)
    have : (1 + (dm x : ℝ) + dp x) * rho (dp x) (fun θ => q x θ - qn n x θ) * 2 ^ (dp x) *
        ((2 * (dp x : ℝ)) ^ k * 1 ^ (dp x)) = L * rho (dp x) (fun θ => q x θ - qn n x θ) := by
      rw [hL]; ring
    rw [this] at hb
    refine hb.trans_lt ?_
    have h1 : L * rho (dp x) (fun θ => q x θ - qn n x θ) ≤ L * (ε / (L + 1)) :=
      mul_le_mul_of_nonneg_left hn.le hL0
    have h2 : L * (ε / (L + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have key := unif_tsum (fun n => muN typ n) mu
    (fun n x z => iteratedDeriv k (F c (dp x) (dm x) (qn n x)) z)
    (fun x z => iteratedDeriv k (F c (dp x) (dm x) (q x)) z) (Set.Icc 0 1) B G (2 * C1)
    (fun n => muN_nonneg typ n) hmu0 hmuconv
    (eventually_atTop.2 ⟨1, fun n hn => hasSum_muN_one typ hn⟩) hmu1 hG0 hGs hGs0 hB
    (fun n x z hz => hbd (qn n) (hrqn n) x z hz) (fun x z hz => hbd q hrq x z hz) haconv
  refine (key.congr ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn z _
    simp only
    rw [lamN_eq]
    exact (D_fVec (muN_Mom dp dm typ n) (hasSum_muN_one typ hn) (qn n) (hrqn n) c k z).symm
  · intro z _
    exact (D_fVec hMomMu hmu1 q hrq c k z).symm

end DCFSA4

open DefaultContagion.FinalSize in
theorem solution {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3a : Assumption3a dp dm typ mu)
    (h3b : Assumption3b dp dm typ) :
    let lam : ℝ := ∑' x, mu x * (dp x : ℝ)
    ∀ c : Fin 5, ∀ k : ℕ,
      TendstoUniformlyOn
        (fun n z => iteratedDeriv k
          (fun w => fVec dp dm (lamN dp typ n) (muN typ n) (qn n) w c) z)
        (fun z => iteratedDeriv k (fun w => fVec dp dm lam mu q w c) z)
        atTop (Set.Icc (0 : ℝ) 1) := by
  intro lam c k
  exact DCFSA4.lemmaA4_main dp dm typ qn mu q h2 h3b c k
