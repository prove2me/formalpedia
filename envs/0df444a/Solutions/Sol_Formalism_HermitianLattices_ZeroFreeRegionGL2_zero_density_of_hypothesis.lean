-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.zero_density_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:55.373938+00:00
-- url     : https://prove2.me/submissions/ce1d0f33-876c-467d-85d3-e58a8198e7de

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_bound_unit_modulus
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_zero_density_bound
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_class_admissible
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_class_splits
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_finite_splitting_of_group
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_markov_discard_bound
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
private lemma exp_scale_pos (ε x : ℝ) : 0 < X1 ε x := by unfold X1; exact Real.exp_pos _
private lemma double_exp_scale_pos (ε x : ℝ) : 0 < X2 ε x := by unfold X2; exact Real.exp_pos _
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
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h2 := congrArg (fun χ : DirichletCharacter ℂ q => χ a) h
  simp [qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply (Ne.isUnit ha0)] at h2 <;>
    norm_num at h2
private lemma qc_prim (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : (qc q).IsPrimitive := by
  have hp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hp.ne_zero⟩
  rcases hp.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level (qc q)) with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) (qc_ne_one q hq)
  · exact h
private lemma qc_sq (q : ℕ) [Fact q.Prime] : qc q ^ 2 = 1 := by
  unfold qc
  exact ((quadraticChar_isQuadratic (F := ZMod q)).comp (Int.castRingHom ℂ)).sq_eq_one
private lemma chi_eight_sq : chi8 ^ 2 = 1 := by
  unfold chi8
  exact (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one
private lemma chi_eight_primitive : chi8.IsPrimitive := by
  by_contra hne
  have h8 : chi8.conductor ∣ 2 ^ 3 := by
    simpa using DirichletCharacter.conductor_dvd_level chi8
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8
  have hi2 : i ≤ 2 := by
    by_contra h
    have h3 : i = 3 := by omega
    exact hne (by show chi8.conductor = 8; rw [hci, h3]; norm_num)
  have h4 : chi8.conductor ∣ 4 := by
    rw [hci, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hi2
  obtain ⟨hd, χ₀, hχ⟩ := DirichletCharacter.factorsThrough_conductor chi8
  have h48 : (4 : ℕ) ∣ 8 := by norm_num
  have hχ' : chi8 = DirichletCharacter.changeLevel h48 (DirichletCharacter.changeLevel h4 χ₀) := by
    rw [← DirichletCharacter.changeLevel_trans]
    exact hχ
  have e : ∀ u : (ZMod 8)ˣ, chi8 u =
      (DirichletCharacter.changeLevel h4 χ₀) (ZMod.cast (u : ZMod 8)) := by
    intro u
    exact (congrArg (fun ψ : DirichletCharacter ℂ 8 => ψ u) hχ').trans
      (DirichletCharacter.changeLevel_eq_cast_of_dvd _ h48 u)
  have h3 : Nat.Coprime 3 8 := by norm_num
  have h7 : Nat.Coprime 7 8 := by norm_num
  have e3 := e (ZMod.unitOfCoprime 3 h3)
  have e7 := e (ZMod.unitOfCoprime 7 h7)
  rw [ZMod.coe_unitOfCoprime] at e3 e7
  have hc : (ZMod.cast ((3 : ℕ) : ZMod 8) : ZMod 4) = ZMod.cast ((7 : ℕ) : ZMod 8) := by
    decide
  rw [hc, ← e7] at e3
  have v3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
  have v7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide
  simp only [chi8, MulChar.ringHomComp_apply, v3, v7] at e3
  norm_num at e3
private theorem twist_is_primitive : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q hF hθ hq2 hc
  have hp : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hc)
  haveI : NeZero t := ⟨ht⟩
  haveI : NeZero q := ⟨hp.ne_zero⟩
  haveI : NeZero (t * q) := ⟨mul_ne_zero ht hp.ne_zero⟩
  have hA : (DirichletCharacter.changeLevel (Dvd.intro q rfl) θ).conductor = t := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact hθ
  have hB : (DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)).conductor = q := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact qc_prim q hq2
  have hcop : (DirichletCharacter.changeLevel (Dvd.intro q rfl) θ).conductor.Coprime
      (DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)).conductor := by
    rw [hA, hB]
    exact hc.symm
  have hdvd := cond_mul_coprime _ _ hcop
  rw [hA, hB] at hdvd
  have hprim : (tw θ q).conductor = t * q :=
    Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) hdvd
  refine ⟨hprim, ?_, ?_⟩
  · intro h1
    have h1' := DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1
    rw [hprim] at h1'
    have h2q := hp.two_le
    have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hθ2
    unfold tw
    rw [mul_pow, ← map_pow, ← map_pow, hθ2, qc_sq, map_one, map_one, one_mul]
open Classical in
private lemma mem_badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ) :
    q ∈ badSet θ Q P ↔ q ∈ P ∧ ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h) := by
  rw [badSet, Finset.mem_filter]
private lemma mem_PP {m a q : ℕ} {X : ℝ} (hX : 0 ≤ X) (h : q ∈ PPset m a X) :
    q.Prime ∧ q % m = a % m ∧ X ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X := by
  rw [PPset, Finset.mem_filter, Finset.mem_Icc] at h
  obtain ⟨⟨_, hq⟩, hp, hm, hlt⟩ := h
  exact ⟨hp, hm, hlt, (Nat.le_floor_iff hX).1 hq⟩
private lemma badCard {C : ℝ} (hBC : BoxCountHyp C) {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ)
    (P : Finset ℕ) (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1)
    (hP : ∀ q ∈ P, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q) :
    ((badSet θ Q P).card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  refine hBC t θ Q (badSet θ Q P) h1 h2 ?_
  intro q hq
  obtain ⟨hqP, hF, hz⟩ := (mem_badSet θ Q P q).1 hq
  obtain ⟨h4, hc, hQ⟩ := hP q hqP
  exact ⟨hF, h4, hc, hQ, hz⟩
private lemma goodOf {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ)
    [hF : Fact q.Prime] (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1) (hq2 : q ≠ 2) (hc : q.Coprime t)
    (hQ : ((t * q : ℕ) : ℝ) ≤ Q) (hqP : q ∈ P) (hb : q ∉ badSet θ Q P) :
    GoodFor Q (tw θ q) ∧ tw θ q ≠ 1 := by
  have hT : TwPrimitive := twist_is_primitive
  unfold TwPrimitive at hT
  obtain ⟨hp, hne, hsq⟩ := hT.2 t θ q h1 hq2 hc
  refine ⟨?_, hne⟩
  unfold GoodFor
  refine ⟨hp, hsq h2, hQ, ?_⟩
  by_contra hz
  exact hb ((mem_badSet θ Q P q).2 ⟨hqP, hF, hz⟩)
private lemma gBound {ε C x₂ x Q : ℝ} (hBT : BoxTailHyp ε C x₂) (hx2 : x₂ ≤ x) (hx1 : 1 ≤ x)
    (hw1 : x ^ (ε / 6) ≤ Real.log Q) (hw2 : Real.log Q ≤ x ^ (ε / 4))
    (hlast : x ^ (1 / 2 + ε) / 2 + x ^ ε ≤ x ^ (1 / 2 + ε))
    {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime]
    (hg : GoodFor Q (tw θ q) ∧ tw θ q ≠ 1) (hS : SS θ x q ≤ x ^ (1 / 2 + ε) / 2) :
    ‖Gchi (tw θ q) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw θ q)‖ ≤ C * Real.log x := by
  obtain ⟨t1, t2⟩ := hBT x Q (t * q) (tw θ q) hx2 hw1 hw2 hg.2 hg.1
  refine ⟨?_, t2⟩
  have hxz : x ≤ x ^ 400 := le_self_pow₀ hx1 (by norm_num)
  rw [finite_splitting_of_group (t * q) (tw θ q) x (x ^ 400) (by linarith) hxz]
  have hSz : ‖Sz (tw θ q) x (x ^ 400)‖ = SS θ x q := by
    unfold Sz SS
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [twist_evaluation_formula t θ q n, mul_assoc]
  calc ‖- Sz (tw θ q) x (x ^ 400) - (x : ℂ) * tailL (tw θ q) (x ^ 400)‖
      ≤ ‖- Sz (tw θ q) x (x ^ 400)‖ + ‖(x : ℂ) * tailL (tw θ q) (x ^ 400)‖ := norm_sub_le _ _
    _ ≤ x ^ (1 / 2 + ε) := by rw [norm_neg, hSz]; linarith
private lemma kappa_norm {t : ℕ} (θ : DirichletCharacter ℂ t) (n : ℕ) : ‖θ (n : ZMod t)‖ ≤ 1 := DirichletCharacter.norm_le_one θ _
private lemma kappa_mul {t : ℕ} (θ : DirichletCharacter ℂ t) (a b : ℕ) :
    θ ((a * b : ℕ) : ZMod t) = θ (a : ZMod t) * θ (b : ZMod t) := by
  rw [Nat.cast_mul, map_mul]
private lemma trivial_character_primitive : one1.IsPrimitive := by
  show one1.conductor = 1
  exact Nat.dvd_one.mp (DirichletCharacter.conductor_dvd_level _)
private lemma trivial_character_sq : one1 ^ 2 = 1 := by
  simp [one1]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : PrimePairOfBoxAndMeanSquareHypotheses := by
  intro ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ hBC hBT hMS
  obtain ⟨xa, ha⟩ := numerical_bound_unit_modulus ε C₂ hε hε1 hC₂
  obtain ⟨xb, hb⟩ := numerical_bound_unit_modulus ε C₄ hε hε1 hC₄
  obtain ⟨xc, hc⟩ := numerical_zero_density_bound ε C₂ hε hε1 hC₂
  refine ⟨max (max (max x₂ x₄) (max xa xb)) (max xc 1), fun x hx => ?_⟩
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx4 : x₄ ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxa : xa ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
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
    (by decide) (by norm_num) (by exact_mod_cast a3) a5 (kappa_norm one1) (kappa_mul one1)
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
    (badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1) 1 (fun _ q => SS one1 x q) V t htpos
    (fun _ => hM1) (by
      have h1 : (((badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1).card : ℕ) : ℝ) ≤
          ((badSet one1 (8 * X1 ε x) P1).card : ℝ) + ((badSet chi8 (8 * X1 ε x) P1).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      have h2 := mul_le_mul_of_nonneg_right hr hp1pos.le
      push_cast
      linarith)
  rw [Finset.mem_union, not_or] at hq₁B
  obtain ⟨q1p, q18, q1lo, q1hi⟩ := hP1mem q₁ hq₁P
  have hF1 : Fact q₁.Prime := ⟨q1p⟩
  have q1ne2 : q₁ ≠ 2 := by omega
  have q1S : SS one1 x q₁ ≤ t := le_trans (le_abs_self _) (hq₁S 0)
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
      (∑ q ∈ PPset (16 * M) a₀ (X2 ε x), SS θ x q ^ 2) ≤ V * ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) :=
    fun {s} θ => hMS x (X2 ε x) (16 * M) a₀ (fun n => θ (n : ZMod s)) hx4 e5 e6 e3 e4 hm0 c2
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
    ((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)) 2
    (fun j q => if j = 0 then SS one1 x q else SS (tw one1 q₁) x q) V t htpos
    (by
      intro j
      by_cases hj : j = 0
      · simp only [hj, if_true]; exact (hMS2 one1).2
      · simp only [hj, if_false]; exact (hMS2 (tw one1 q₁)).2)
    (by
      have h1 : ((((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪
          (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)).card : ℕ) : ℝ) ≤
          (((badSet one1 Q P2).card : ℝ) + ((badSet chi8 Q P2).card : ℝ)) +
          (((badSet (tw one1 q₁) Q P2).card : ℝ) + ((badSet (tw chi8 q₁) Q P2).card : ℝ)) := by
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
  have dS0 : SS one1 x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 0)
  have dS1 : SS (tw one1 q₁) x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 1)
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
end Formalism.HermitianLattices.ZeroFreeRegionGL2
