-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.final_bound_of_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:31.146959+00:00
-- url     : https://prove2.me/submissions/29cc55d0-707e-418c-acf6-818e2a99c8f0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZFinal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
attribute [local irreducible] q0 pY pJ pN
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : FinalOf := by
  rintro ⟨C, hC0, hC⟩ hDet hBC hNum
  obtain ⟨Q₀, C', hQ₀, hN⟩ := hNum C hC0
  classical

  let F : Finset PC := (range ⌈Q₀⌉₊).sigma (fun N => @Finset.univ (DirichletCharacter ℂ (N + 1)) (Fintype.ofFinite _))
  refine ⟨max C' ((F.card : ℝ) + 1), fun Q S hQ hS => ?_⟩
  have hQ14 : (1 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hQ14' : (0 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by linarith
  rcases lt_or_ge Q Q₀ with hQQ | hQQ
  ·
    have hsub : S ⊆ F := by
      intro p hp
      obtain ⟨-, hpQ, -⟩ := hS p hp
      simp only [F, mem_sigma, mem_range, mem_univ, and_true]
      have h1 : ((p.1 : ℕ) : ℝ) < Q₀ := by push_cast at hpQ; linarith
      have h2 : (Q₀ : ℝ) ≤ (⌈Q₀⌉₊ : ℝ) := Nat.le_ceil Q₀
      exact_mod_cast h1.trans_le h2
    have hc : (S.card : ℝ) ≤ F.card := by exact_mod_cast card_le_card hsub
    calc (S.card : ℝ) ≤ (F.card : ℝ) + 1 := by linarith
      _ ≤ max C' ((F.card : ℝ) + 1) := le_max_right _ _
      _ = max C' ((F.card : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hQ14 (le_trans (by positivity) (le_max_right _ _))
  ·
    obtain ⟨hsm, hfin⟩ := hN Q hQQ
    have hQ20 : (20 : ℝ) ≤ Q := le_trans hQ₀ hQQ
    set J := pJ Q with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; unfold pJ; omega
    have hY1 : 1 ≤ pY Q := by
      unfold pY
      have : 1 ≤ q0 Q := by unfold q0; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      exact Nat.one_le_pow _ _ (by omega)

    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun p : PC => p.1 = 0)
    set S' := S.filter (fun p : PC => ¬ p.1 = 0) with hS'
    have h0 : (S.filter (fun p : PC => p.1 = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      obtain ⟨Na, χa⟩ := a
      obtain ⟨Nb, χb⟩ := b
      simp only [mem_filter] at ha hb
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨-, rfl⟩ := hb
      have e1 : χa = 1 := DirichletCharacter.level_one' _ rfl
      have e2 : χb = 1 := DirichletCharacter.level_one' _ rfl
      rw [e1, e2]

    let ρ : PC → ℂ := fun p => if h : (∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧
        DirichletCharacter.LFunction p.2 s = 0) then h.choose else 0
    have hρ : ∀ p ∈ S, 1 - 1 / 400 < (ρ p).re ∧ |(ρ p).im| ≤ Q ∧ DirichletCharacter.LFunction p.2 (ρ p) = 0 := by
      intro p hp
      have h := (hS p hp).2.2
      simp only [ρ, dif_pos h]
      exact h.choose_spec
    let jf : PC → ℕ := fun p => if h : (∃ j ∈ range J, 1 / (2 * (J : ℝ)) ≤
        ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p (ρ p)‖) then h.choose else 0
    have hne1 : ∀ p ∈ S', p.2 ≠ 1 := by
      intro p hp h
      simp only [hS', mem_filter] at hp
      have hc : p.2.conductor = p.1 + 1 := (hS p hp.1).1
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    have hjf : ∀ p ∈ S', jf p ∈ range J ∧
        1 / (2 * (J : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ (jf p)) p (ρ p)‖ := by
      intro p hp
      have hpS : p ∈ S := (mem_filter.1 hp).1
      have hp0 : p.1 ≠ 0 := (mem_filter.1 hp).2
      obtain ⟨hprim, hlev, -⟩ := hS p hpS
      obtain ⟨h1, h2, h3⟩ := hρ p hpS
      have h := hDet Q hQ20 p hprim hp0 hlev (ρ p) (by unfold s0; exact h1) h2 h3
      rw [← hJdef] at h
      simp only [jf, dif_pos h]
      exact h.choose_spec
    have hre1 : ∀ p ∈ S', (ρ p).re < 1 := by
      intro p hp
      by_contra hc
      push Not at hc
      have hpS : p ∈ S := (mem_filter.1 hp).1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 (Or.inl (hne1 p hp)) hc (hρ p hpS).2.2

    have hfib := Finset.card_eq_sum_card_fiberwise (f := jf) (s := S') (t := range J) (fun p hp => (hjf p hp).1)
    set K : ℕ := pY Q * 2 ^ J with hK
    have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hblock : ∀ j ∈ range J, ((S'.filter (fun p => jf p = j)).card : ℝ) ≤
        8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ) := by
      intro j hj
      have hU : 1 ≤ pY Q * 2 ^ j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
      have h := hBC C hC0 hC Q (by linarith) (pY Q) (pN Q) (pY Q * 2 ^ j) J hU hJ1 (hsm j hj)
        (S'.filter (fun p => jf p = j)) ρ (by
          intro p hp
          obtain ⟨hpS', hpj⟩ := mem_filter.1 hp
          have hpS : p ∈ S := (mem_filter.1 hpS').1
          obtain ⟨hprim, hlev, -⟩ := hS p hpS
          obtain ⟨h1, h2, -⟩ := hρ p hpS
          refine ⟨hprim, hlev, by unfold s0; exact h1, hre1 p hpS', h2, ?_⟩
          have := (hjf p hpS').2
          rw [hpj] at this
          exact this)
      refine h.trans ?_
      have hUK : ((pY Q * 2 ^ j : ℕ) : ℝ) ≤ K := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hj).le
        exact_mod_cast Nat.mul_le_mul_left _ this
      have hrp : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (K : ℝ) ^ (3 / 200 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hUK (by norm_num)
      have : (0 : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C := by positivity
      exact mul_le_mul_of_nonneg_left hrp this
    have hS'card : (S'.card : ℝ) ≤ (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      rw [hfib]; push_cast
      refine (sum_le_sum hblock).trans ?_
      rw [sum_const, card_range, nsmul_eq_mul]
    have htot : (S.card : ℝ) ≤ 1 + (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      have : (S.card : ℝ) = (S.filter (fun p : PC => p.1 = 0)).card + S'.card := by
        rw [← hcard]; push_cast; ring
      rw [this]
      have : ((S.filter (fun p : PC => p.1 = 0)).card : ℝ) ≤ 1 := by exact_mod_cast h0
      linarith
    calc (S.card : ℝ) ≤ C' * Q ^ (1 / 4 : ℝ) := htot.trans hfin
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hQ14'
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
