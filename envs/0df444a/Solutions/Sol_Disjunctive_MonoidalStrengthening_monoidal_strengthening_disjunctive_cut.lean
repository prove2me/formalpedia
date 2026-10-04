-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.monoidal_strengthening_disjunctive_cut
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:03:28.519983+00:00
-- url     : https://prove2.me/submissions/1dc6e31b-b947-453e-bcc7-7c3d6ce8f05b

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

open Disjunctive.MonoidalStrengthening

theorem solution {q n : ℕ} [Nonempty (Fin q)]
    (acoef : Fin q → Fin n → ℝ) (a0 b0 theta : Fin q → ℝ) (J1 : Finset (Fin n))
    (hb0 : ∀ h, b0 h ≤ a0 h) (htheta : ∀ h, 0 ≤ theta h)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x)
    (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ h, b0 h ≤ ∑ j, acoef h j * x j)
    (hx_disj : ∃ h, a0 h ≤ ∑ j, acoef h j * x j) :
    Alpha0 theta a0 ≤
      ∑ j ∈ J1, AlphaJStrengthened theta a0 b0 acoef j * x j +
        ∑ j ∈ Finset.univ \ J1, AlphaJUnstrengthened theta acoef j * x j := by
  classical
  choose! k hk using hx_int
  set S : ℝ := ∑ j ∈ J1, x j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hx_nonneg j
  apply le_of_forall_pos_le_add
  intro ε hε
  set ε' : ℝ := ε / (S + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by linarith)
  -- near-optimal monoid elements
  have hex : ∀ j, ∃ mu : Fin q → ℤ, mu ∈ CutMonoid q ∧
      Finset.univ.sup' Finset.univ_nonempty
        (fun h => theta h * (acoef h j + (mu h : ℝ) * (a0 h - b0 h))) <
        AlphaJStrengthened theta a0 b0 acoef j + ε' := by
    intro j
    have hne : ({v : ℝ | ∃ mu : Fin q → ℤ, mu ∈ CutMonoid q ∧
        v = Finset.univ.sup' Finset.univ_nonempty
          (fun h => theta h * (acoef h j + (mu h : ℝ) * (a0 h - b0 h)))}).Nonempty :=
      ⟨_, 0, by simp [CutMonoid], rfl⟩
    obtain ⟨v, ⟨mu, hmu, rfl⟩, hv⟩ := Real.lt_sInf_add_pos hne hε'pos
    exact ⟨mu, hmu, hv⟩
  choose mu hmuM hmuV using hex
  set V : Fin n → ℝ := fun j => Finset.univ.sup' Finset.univ_nonempty
    (fun h => theta h * (acoef h j + (mu j h : ℝ) * (a0 h - b0 h))) with hVdef
  set m : Fin q → ℝ := fun h => ∑ j ∈ J1, (mu j h : ℝ) * x j with hmdef
  -- key lower bound for each `h`
  have hkey : ∀ h, theta h * (∑ j, acoef h j * x j + (a0 h - b0 h) * m h) ≤
      ∑ j ∈ J1, V j * x j + ∑ j ∈ Finset.univ \ J1, AlphaJUnstrengthened theta acoef j * x j := by
    intro h
    have hsplit : ∑ j, acoef h j * x j =
        ∑ j ∈ J1, acoef h j * x j + ∑ j ∈ Finset.univ \ J1, acoef h j * x j := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_univ J1)]
    have e : theta h * (∑ j, acoef h j * x j + (a0 h - b0 h) * m h) =
        ∑ j ∈ J1, theta h * (acoef h j + (mu j h : ℝ) * (a0 h - b0 h)) * x j +
          ∑ j ∈ Finset.univ \ J1, theta h * acoef h j * x j := by
      have e1 : ∀ j, theta h * (acoef h j + (mu j h : ℝ) * (a0 h - b0 h)) * x j =
          theta h * (acoef h j * x j) + (theta h * (a0 h - b0 h)) * ((mu j h : ℝ) * x j) := by
        intro j; ring
      have e2 : ∀ j, theta h * acoef h j * x j = theta h * (acoef h j * x j) := by
        intro j; ring
      simp_rw [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsplit, hmdef]
      ring
    rw [e]
    gcongr with j hj j hj
    · exact hx_nonneg j
    · exact Finset.le_sup' (fun h => theta h * (acoef h j + (mu j h : ℝ) * (a0 h - b0 h)))
        (Finset.mem_univ h)
    · exact hx_nonneg j
    · exact Finset.le_sup' (fun h => theta h * acoef h j) (Finset.mem_univ h)
  -- integrality of `m`
  set mZ : Fin q → ℤ := fun h => ∑ j ∈ J1, mu j h * k j with hmZ
  have hmcast : ∀ h, m h = (mZ h : ℝ) := by
    intro h
    simp only [hmdef, hmZ, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hk j hj]
  have hkpos : ∀ j ∈ J1, 0 ≤ k j := by
    intro j hj
    have := hx_nonneg j
    simp only [Pi.zero_apply] at this
    rw [hk j hj] at this
    exact_mod_cast this
  have hsumZ : 0 ≤ ∑ h, mZ h := by
    simp only [hmZ]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun j hj => ?_
    rw [← Finset.sum_mul]
    exact mul_nonneg (hmuM j) (hkpos j hj)
  -- the disjunctive argument
  have hmain : Alpha0 theta a0 ≤
      ∑ j ∈ J1, V j * x j + ∑ j ∈ Finset.univ \ J1, AlphaJUnstrengthened theta acoef j * x j := by
    by_cases hpos : ∃ h, 1 ≤ mZ h
    · obtain ⟨h, hh⟩ := hpos
      refine le_trans ?_ (hkey h)
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ h)) ?_
      apply mul_le_mul_of_nonneg_left _ (htheta h)
      have h1 : (1 : ℝ) ≤ m h := by rw [hmcast]; exact_mod_cast hh
      have hc : 0 ≤ a0 h - b0 h := sub_nonneg.mpr (hb0 h)
      nlinarith [hx_lb h]
    · push Not at hpos
      have hzero : ∀ h, mZ h = 0 := by
        intro h
        have hle : ∀ h', mZ h' ≤ 0 := fun h' => by linarith [hpos h']
        have hsum0 : ∑ h', mZ h' = 0 :=
          le_antisymm (Finset.sum_nonpos fun h' _ => hle h') hsumZ
        exact (Finset.sum_eq_zero_iff_of_nonpos (fun h' _ => hle h')).mp hsum0 h
          (Finset.mem_univ h)
      obtain ⟨h, hh⟩ := hx_disj
      refine le_trans ?_ (hkey h)
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ h)) ?_
      apply mul_le_mul_of_nonneg_left _ (htheta h)
      rw [hmcast, hzero h]
      simpa using hh
  -- compare `V` with the strengthened coefficients
  have hcomp : ∑ j ∈ J1, V j * x j ≤
      ∑ j ∈ J1, AlphaJStrengthened theta a0 b0 acoef j * x j + ε' * S := by
    rw [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_right (hmuV j).le (hx_nonneg j)
    rw [add_mul] at this
    linarith
  have hεS : ε' * S ≤ ε := by
    rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

#print axioms solution
