-- Prove2me | solution 1 for Formalism.HermitianLattices.WeakMeanSquareEstimates.prime_pair_of_box_and_weak_mean_square_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:47.775523+00:00
-- url     : https://prove2.me/submissions/f2dbc963-c306-47fd-b3a1-7c1a49b96d9e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_class_admissible
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_class_splits
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_finite_splitting_of_group
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_markov_discard_bound
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_bound_unit_modulus
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_zero_density_bound
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_primorial_upper_bound
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_twist_evaluation_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
private lemma exp_scale_pos (ε x : ℝ) : 0 < X1 ε x := Real.exp_pos _
private lemma double_exp_scale_pos (ε x : ℝ) : 0 < X2 ε x := Real.exp_pos _
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := Real.log_exp _
private lemma log_double_exp_scale (ε x : ℝ) : Real.log (X2 ε x) = x ^ (ε / 5) * Real.log x ^ 2 := Real.log_exp _
open DirichletCharacter in
private lemma cond_mul_coprime {n : ℕ} [NeZero n] (A B : DirichletCharacter ℂ n)
    (h : A.conductor.Coprime B.conductor) : A.conductor * B.conductor ∣ (A * B).conductor := by
  have hA : A.conductor ∣ (A * B).conductor := by
    have h1 : A.conductor ∣ ((A * B).conductor).lcm (B⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
      rwa [mul_inv_cancel_right] at this
    rw [conductor_inv] at h1
    have h2 : A.conductor ∣ (A * B).conductor * B.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.dvd_of_dvd_mul_right h2
  have hB : B.conductor ∣ (A * B).conductor := by
    have h1 : B.conductor ∣ ((A * B).conductor).lcm (A⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) A⁻¹
      rwa [mul_comm A B, mul_inv_cancel_right, mul_comm B A] at this
    rw [conductor_inv] at h1
    have h2 : B.conductor ∣ (A * B).conductor * A.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.symm.dvd_of_dvd_mul_right h2
  exact h.mul_dvd_of_dvd_of_dvd hA hB
private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : qc q ≠ 1 := by
  intro h
  have h1 : quadraticChar (ZMod q) ≠ 1 := quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n])
  apply h1
  ext a
  have := congrArg (fun χ : DirichletCharacter ℂ q => χ a) h
  simp only [qc, MulChar.ringHomComp_apply, MulChar.one_apply_coe] at this
  have h2 : ((quadraticChar (ZMod q) (a : ZMod q) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by simpa using this
  rw [MulChar.one_apply_coe]
  exact_mod_cast h2
private lemma qc_prim (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : (qc q).IsPrimitive := by
  have hp : q.Prime := Fact.out
  have : NeZero q := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level (qc q)) with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q hq)
  · exact h
private lemma qc_sq (q : ℕ) [Fact q.Prime] : qc q ^ 2 = 1 :=
  ((quadraticChar_isQuadratic (ZMod q)).comp _).sq_eq_one
private lemma chi_eight_sq : chi8 ^ 2 = 1 := (ZMod.isQuadratic_χ₈.comp _).sq_eq_one
private lemma chi_eight_primitive : chi8.IsPrimitive := by
  have hd : chi8.conductor ∣ 2 ^ 3 := DirichletCharacter.conductor_dvd_level chi8
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  by_cases h3 : k = 3
  · subst h3; exact hk'
  · exfalso
    have h4 : chi8.conductor ∣ 4 := by
      rw [hk', show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have hmem := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi8 (show 4 ∣ 8 by norm_num)).2 h4
    obtain ⟨h, χ₀, hχ⟩ := hmem
    have h5 : chi8 ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) := by
      rw [hχ]
      exact DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ h (by
        rw [Int.isCoprime_iff_gcd_eq_one]; decide)
    have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
    have h7 : chi8 ((5 : ℤ) : ZMod 8) = -1 := by
      simp [chi8, MulChar.ringHomComp_apply]
    rw [h6, map_one, h7] at h5
    norm_num at h5
private theorem twist_is_primitive : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ hq hc
  have hp : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hc
    exact hp.one_lt.ne' hc
  have : NeZero t := ⟨ht⟩
  have hprim : (tw θ q).IsPrimitive := by
    have h1 : (DirichletCharacter.changeLevel (Dvd.intro q rfl : t ∣ t * q) θ).conductor = t := by
      rw [DirichletCharacter.conductor_changeLevel]; exact hθ
    have h2 : (DirichletCharacter.changeLevel (Dvd.intro_left t rfl : q ∣ t * q) (qc q)).conductor = q := by
      rw [DirichletCharacter.conductor_changeLevel]; exact qc_prim q hq
    have h3 := cond_mul_coprime (DirichletCharacter.changeLevel (Dvd.intro q rfl : t ∣ t * q) θ)
      (DirichletCharacter.changeLevel (Dvd.intro_left t rfl : q ∣ t * q) (qc q)) (by rw [h1, h2]; exact hc.symm)
    rw [h1, h2] at h3
    exact Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) h3
  refine ⟨hprim, ?_, ?_⟩
  · intro h
    have h1 := DirichletCharacter.eq_one_iff_conductor_eq_one.1 h
    rw [(DirichletCharacter.isPrimitive_def _).1 hprim] at h1
    exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_left h1)
  · intro h2
    unfold tw
    rw [mul_pow, ← map_pow, ← map_pow, h2, qc_sq, map_one, map_one, one_mul]
open Classical in
private lemma mem_badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ) :
    q ∈ p2m_PrimePair_badSet θ Q P ↔ q ∈ P ∧ ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h) := by
  unfold p2m_PrimePair_badSet; exact Finset.mem_filter
private lemma mem_PP {m a q : ℕ} {X : ℝ} (hX : 0 ≤ X) (h : q ∈ PPset m a X) :
    q.Prime ∧ q % m = a % m ∧ X ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X := by
  unfold PPset at h
  rw [Finset.mem_filter, Finset.mem_Icc] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2, (Nat.le_floor_iff hX).1 h.1.2⟩
private lemma badCard {C : ℝ} (hBC : BoxCountHyp C) {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ)
    (P : Finset ℕ) (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1)
    (hP : ∀ q ∈ P, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q) :
    ((p2m_PrimePair_badSet θ Q P).card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  apply hBC t θ Q _ h1 h2
  intro q hq
  rw [mem_badSet] at hq
  obtain ⟨hqP, hF, hz⟩ := hq
  obtain ⟨a, b, c⟩ := hP q hqP
  exact ⟨hF, a, b, c, hz⟩
private lemma goodOf {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ)
    [hF : Fact q.Prime] (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1) (hq2 : q ≠ 2) (hc : q.Coprime t)
    (hQ : ((t * q : ℕ) : ℝ) ≤ Q) (hqP : q ∈ P) (hb : q ∉ p2m_PrimePair_badSet θ Q P) :
    GoodFor Q (tw θ q) ∧ tw θ q ≠ 1 := by
  obtain ⟨p1, p2, p3⟩ := twist_is_primitive.2 t θ q h1 hq2 hc
  refine ⟨⟨p1, p3 h2, hQ, ?_⟩, p2⟩
  by_contra hz
  exact hb ((mem_badSet θ Q P q).2 ⟨hqP, hF, hz⟩)
private lemma gBound {ε C x₂ x Q : ℝ} (hBT : BoxTailHyp ε C x₂) (hx2 : x₂ ≤ x) (hx1 : 1 ≤ x)
    (hw1 : x ^ (ε / 6) ≤ Real.log Q) (hw2 : Real.log Q ≤ x ^ (ε / 4))
    (hlast : x ^ (1 / 2 + ε) / 2 + x ^ ε ≤ x ^ (1 / 2 + ε))
    {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime]
    (hg : GoodFor Q (tw θ q) ∧ tw θ q ≠ 1) (hS : p2m_PrimePair_SS θ x q ≤ x ^ (1 / 2 + ε) / 2) :
    ‖Gchi (tw θ q) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw θ q)‖ ≤ C * Real.log x := by
  obtain ⟨t1, t2⟩ := hBT x Q (t * q) (tw θ q) hx2 hw1 hw2 hg.2 hg.1
  refine ⟨?_, t2⟩
  have hxz : x ≤ x ^ 400 := le_self_pow₀ hx1 (by norm_num)
  rw [finite_splitting_of_group (t * q) (tw θ q) x (x ^ 400) (by linarith) hxz]
  have hSz : ‖Sz (tw θ q) x (x ^ 400)‖ = p2m_PrimePair_SS θ x q := by
    unfold Sz p2m_PrimePair_SS
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [twist_evaluation_formula t θ q n, mul_assoc]
  calc ‖- Sz (tw θ q) x (x ^ 400) - (x : ℂ) * tailL (tw θ q) (x ^ 400)‖
      ≤ ‖- Sz (tw θ q) x (x ^ 400)‖ + ‖(x : ℂ) * tailL (tw θ q) (x ^ 400)‖ := norm_sub_le _ _
    _ ≤ x ^ (1 / 2 + ε) := by rw [norm_neg, hSz]; linarith
private lemma kappa_norm {t : ℕ} (θ : DirichletCharacter ℂ t) (n : ℕ) : ‖θ (n : ZMod t)‖ ≤ 1 :=
  DirichletCharacter.norm_le_one θ _
private lemma kappa_mul {t : ℕ} (θ : DirichletCharacter ℂ t) (a b : ℕ) :
    θ ((a * b : ℕ) : ZMod t) = θ (a : ZMod t) * θ (b : ZMod t) := by
  rw [Nat.cast_mul, map_mul]
private lemma trivial_character_primitive : one1.IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
private lemma trivial_character_sq : one1 ^ 2 = 1 := one_pow 2
end Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.WeakMeanSquareEstimates
open Formalism.HermitianLattices.ZeroFreeRegionGL2
end Formalism.HermitianLattices.WeakMeanSquareEstimates
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace _root_.Formalism.HermitianLattices.WeakMeanSquareEstimates
theorem _root_.solution : Formalism.HermitianLattices.WeakMeanSquareEstimates.PrimePairOfBoxAndWeakMeanSquareHypotheses := by
  intro ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ hBC hBT hMS
  obtain ⟨xa, ha⟩ := numerical_bound_unit_modulus ε C₂ hε hε1 hC₂
  obtain ⟨xb, hb⟩ := numerical_bound_unit_modulus ε C₄ hε hε1 hC₄
  obtain ⟨xc, hc⟩ := numerical_zero_density_bound ε C₂ hε hε1 hC₂
  refine ⟨max (max (max x₂ x₄) (max xa xb)) (max xc (Real.exp 1)), fun x hx => ?_⟩
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx4 : x₄ ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxa : xa ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  obtain ⟨a1, a2, a3, -, a5, a6, a7, -, a9, a10⟩ := ha x hxa
  obtain ⟨-, -, -, -, -, -, -, b8, -, -⟩ := hb x hxb
  obtain ⟨c1, c2, -, c4, c5, c6, c7⟩ := hc x hxc
  set y := x ^ (ε / 5) with hy
  set t := x ^ (1 / 2 + ε) / 2 with ht
  set V := C₄ * x * Real.log x with hV
  have htpos : 0 < t := by have := Real.rpow_pos_of_pos hx0 (1 / 2 + ε); positivity
  have hr : V / t ^ 2 ≤ 1 / 8 := le_trans b8 a9
  have hX1 := exp_scale_pos ε x
  have hX2 := double_exp_scale_pos ε x
  have hX1one : 1 ≤ X1 ε x := Real.one_le_exp (Real.rpow_nonneg hx0.le _)

  obtain ⟨hP1, hM1⟩ := hMS x (X1 ε x) 8 3 (fun n => one1 (n : ZMod 1)) hx4 (by norm_num)
    (by
      intro p hp hp8
      left
      have : p ∣ 2 ^ 3 := by simpa using hp8
      have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      subst h2; exact_mod_cast a2)
    (by decide) (by norm_num) (by exact_mod_cast a3) a5
    (by rw [log_exp_scale]; exact le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) (one_le_pow₀ hl1)) (kappa_norm one1) (kappa_mul one1)
  set P1 := PPset 8 3 (X1 ε x) with hP1def
  have hP1mem : ∀ q ∈ P1, q.Prime ∧ q % 8 = 3 ∧ X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x := by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := mem_PP hX1.le hq
    exact ⟨u1, by omega, u3, u4⟩
  have hodd8 : ∀ q : ℕ, q % 2 = 1 → q.Coprime 8 := by
    intro q hq
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hB1a := badCard hBC one1 (8 * X1 ε x) P1 trivial_character_primitive trivial_character_sq (by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := hP1mem q hq
    refine ⟨by omega, Nat.coprime_one_right q, ?_⟩
    push_cast; linarith)
  have hB1b := badCard hBC chi8 (8 * X1 ε x) P1 twist_is_primitive.1.1 twist_is_primitive.1.2 (by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := hP1mem q hq
    refine ⟨by omega, hodd8 q (by omega), ?_⟩
    push_cast; linarith)
  have hp1pos : (0 : ℝ) < (P1.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hX1 _) hP1
  obtain ⟨q₁, hq₁P, hq₁B, hq₁S⟩ := markov_discard_bound P1
    (p2m_PrimePair_badSet one1 (8 * X1 ε x) P1 ∪ p2m_PrimePair_badSet chi8 (8 * X1 ε x) P1) 1 (fun _ q => p2m_PrimePair_SS one1 x q) V t htpos
    (fun _ => hM1) (by
      have h1 : (((p2m_PrimePair_badSet one1 (8 * X1 ε x) P1 ∪ p2m_PrimePair_badSet chi8 (8 * X1 ε x) P1).card : ℕ) : ℝ) ≤
          ((p2m_PrimePair_badSet one1 (8 * X1 ε x) P1).card : ℝ) + ((p2m_PrimePair_badSet chi8 (8 * X1 ε x) P1).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      have h2 := mul_le_mul_of_nonneg_right hr hp1pos.le
      push_cast
      linarith)
  rw [Finset.mem_union, not_or] at hq₁B
  obtain ⟨q1p, q18, q1lo, q1hi⟩ := hP1mem q₁ hq₁P
  have hF1 : Fact q₁.Prime := ⟨q1p⟩
  have q1ne2 : q₁ ≠ 2 := by omega
  have q1S : p2m_PrimePair_SS one1 x q₁ ≤ t := le_trans (le_abs_self _) (hq₁S 0)
  have g1 := goodOf one1 (8 * X1 ε x) P1 q₁ trivial_character_primitive trivial_character_sq q1ne2 (Nat.coprime_one_right _)
    (by push_cast; linarith) hq₁P hq₁B.1
  have g2 := goodOf chi8 (8 * X1 ε x) P1 q₁ twist_is_primitive.1.1 twist_is_primitive.1.2 q1ne2 (hodd8 q₁ (by omega))
    (by push_cast; linarith) hq₁P hq₁B.2

  have hy0 : 0 ≤ y := by linarith
  obtain ⟨a₀, e1, e2, e3, e4, e5, e6, e7⟩ := class_admissible y (x ^ 400) q₁ a2 q1p q18 (lt_trans a1 q1lo)
  set M := oddM y q₁ with hMdef
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by
    intro h; rw [h, zero_dvd_iff] at e2; omega)
  have hm0 : (1 / 4) * Real.log x ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (X2 ε x) := by
    apply c1
    · exact_mod_cast Nat.mul_pos (by norm_num) hMpos
    · have := primorial_upper_bound y q₁ hy0 q1hi
      push_cast
      linarith
  have hMS2 : ∀ {s : ℕ} (θ : DirichletCharacter ℂ s),
      X2 ε x ^ (9 / 10 : ℝ) ≤ ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) ∧
      (∑ q ∈ PPset (16 * M) a₀ (X2 ε x), p2m_PrimePair_SS θ x q ^ 2) ≤ V * ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) :=
    fun {s} θ => hMS x (X2 ε x) (16 * M) a₀ (fun n => θ (n : ZMod s)) hx4 e5 e6 e3 e4 hm0 c2 (le_of_eq (log_double_exp_scale ε x))
      (kappa_norm θ) (kappa_mul θ)
  set P2 := PPset (16 * M) a₀ (X2 ε x) with hP2def
  set Q := 8 * X1 ε x * X2 ε x with hQ
  have hP2mem : ∀ d ∈ P2, d.Prime ∧ d % 16 = 7 ∧ M ∣ d + 1 ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
      d.Coprime q₁ ∧ (d : ℝ) ≤ X1 ε x * X2 ε x ∧ (q₁ : ℝ) * d ≤ X1 ε x * X2 ε x := by
    intro d hd
    obtain ⟨u1, u2, u3, u4⟩ := mem_PP hX2.le hd
    obtain ⟨v1, v2⟩ := e7 d u2
    refine ⟨u1, v1, v2, u3, u4, ?_, by nlinarith, mul_le_mul q1hi u4 (Nat.cast_nonneg _) hX1.le⟩
    rw [Nat.coprime_primes u1 q1p]
    rintro rfl
    have h1 : d ∣ d + 1 := (Dvd.intro _ rfl : d ∣ M).trans v2
    have h2 : d ∣ 1 := (Nat.dvd_add_right (dvd_refl d)).1 h1
    exact u1.one_lt.ne' (Nat.dvd_one.1 h2)
  have hXX : 0 < X1 ε x * X2 ε x := mul_pos hX1 hX2
  have hQeq : Q = 8 * (X1 ε x * X2 ε x) := by rw [hQ]; ring
  have side1 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 1 ∧ ((1 * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, Nat.coprime_one_right d, by push_cast; rw [hQeq]; linarith⟩
  have side2 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 8 ∧ ((8 * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, hodd8 d (by omega), by push_cast; rw [hQeq]; linarith⟩
  have side3 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (1 * q₁) ∧ ((1 * q₁ * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, by rwa [one_mul], by push_cast; rw [hQeq]; linarith⟩
  have side4 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (8 * q₁) ∧ ((8 * q₁ * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, Nat.Coprime.mul_right (hodd8 d (by omega)) u6, by push_cast; rw [hQeq]; linarith⟩
  have k1 := badCard hBC one1 Q P2 trivial_character_primitive trivial_character_sq side1
  have k2 := badCard hBC chi8 Q P2 twist_is_primitive.1.1 twist_is_primitive.1.2 side2
  have k3 := badCard hBC (tw one1 q₁) Q P2 g1.1.1 g1.1.2.1 side3
  have k4 := badCard hBC (tw chi8 q₁) Q P2 g2.1.1 g2.1.2.1 side4
  have hP2 := (hMS2 one1).1
  have hp2pos : (0 : ℝ) < (P2.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hX2 _) hP2
  obtain ⟨d, hdP, hdB, hdS⟩ := markov_discard_bound P2
    ((p2m_PrimePair_badSet one1 Q P2 ∪ p2m_PrimePair_badSet chi8 Q P2) ∪ (p2m_PrimePair_badSet (tw one1 q₁) Q P2 ∪ p2m_PrimePair_badSet (tw chi8 q₁) Q P2)) 2
    (fun j q => if j = 0 then p2m_PrimePair_SS one1 x q else p2m_PrimePair_SS (tw one1 q₁) x q) V t htpos
    (by
      intro j
      by_cases hj : j = 0
      · simp only [hj, if_true]; exact (hMS2 one1).2
      · simp only [hj, if_false]; exact (hMS2 (tw one1 q₁)).2)
    (by
      have h1 : ((((p2m_PrimePair_badSet one1 Q P2 ∪ p2m_PrimePair_badSet chi8 Q P2) ∪
          (p2m_PrimePair_badSet (tw one1 q₁) Q P2 ∪ p2m_PrimePair_badSet (tw chi8 q₁) Q P2)).card : ℕ) : ℝ) ≤
          (((p2m_PrimePair_badSet one1 Q P2).card : ℝ) + ((p2m_PrimePair_badSet chi8 Q P2).card : ℝ)) +
          (((p2m_PrimePair_badSet (tw one1 q₁) Q P2).card : ℝ) + ((p2m_PrimePair_badSet (tw chi8 q₁) Q P2).card : ℝ)) := by
        exact_mod_cast (Finset.card_union_le _ _).trans
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))
      have h2 := mul_le_mul_of_nonneg_right hr hp2pos.le
      push_cast
      linarith)
  simp only [Finset.mem_union, not_or] at hdB
  obtain ⟨⟨nb1, nb2⟩, nb3, nb4⟩ := hdB
  obtain ⟨dp, d16, dM, dlo, dhi, -, -, -⟩ := hP2mem d hdP
  have hF2 : Fact d.Prime := ⟨dp⟩
  have dne2 : d ≠ 2 := by omega
  have dS0 : p2m_PrimePair_SS one1 x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 0)
  have dS1 : p2m_PrimePair_SS (tw one1 q₁) x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 1)
  have g3 := goodOf one1 Q P2 d trivial_character_primitive trivial_character_sq dne2 (side1 d hdP).2.1 (side1 d hdP).2.2 hdP nb1
  have g4 := goodOf chi8 Q P2 d twist_is_primitive.1.1 twist_is_primitive.1.2 dne2 (side2 d hdP).2.1 (side2 d hdP).2.2
    hdP nb2
  have g5 := goodOf (tw one1 q₁) Q P2 d g1.1.1 g1.1.2.1 dne2 (side3 d hdP).2.1 (side3 d hdP).2.2 hdP nb3
  have g6 := goodOf (tw chi8 q₁) Q P2 d g2.1.1 g2.1.2.1 dne2 (side4 d hdP).2.1 (side4 d hdP).2.2 hdP nb4
  obtain ⟨sp1, sp2⟩ := class_splits y q₁ d q1p d16 dM
  exact ⟨q₁, d, hF1, hF2, q18, d16, q1lo, q1hi, dlo, dhi, sp1, sp2, g1.1, g2.1, g3.1, g4.1, g5.1, g6.1,
    gBound hBT hx2 hx1 a6 a7 c7 one1 q₁ g1 q1S,
    gBound hBT hx2 hx1 c4 c5 c7 one1 d g3 dS0,
    gBound hBT hx2 hx1 c4 c5 c7 (tw one1 q₁) d g5 dS1⟩
end _root_.Formalism.HermitianLattices.WeakMeanSquareEstimates
end Formalism.HermitianLattices.ZeroFreeRegionGL2
