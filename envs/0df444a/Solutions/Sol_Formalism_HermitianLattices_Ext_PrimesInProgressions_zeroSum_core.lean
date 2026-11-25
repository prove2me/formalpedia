-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.zeroSum_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:13.333625+00:00
-- url     : https://prove2.me/submissions/bf818e5b-fba7-4a7d-a8fe-96f942ed6920

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSum
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
private theorem pow_mul_exp_neg_le_of_large_Y (a B c2 θ cZ A₁ ℓ Y L w : ℝ) (n : ℕ) (ha : 1 ≤ a) (hB : 0 ≤ B)
    (hc2 : 0 < c2) (hcZ : 0 < cZ) (hA₁ : 1 ≤ A₁) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hℓ : 2 ≤ ℓ) (hL0 : 0 < L)
    (hLℓ : L ≤ (A₁ + 2) * ℓ) (hw1 : cZ ≤ w) (hw2 : c2 * Real.log (1 / θ) ≤ w) (hn : 1 ≤ n)
    (hwn : (n : ℝ) - 1 ≤ w)
    (hY : ((A₁ + 2) * (a + 1 + 2 / c2) + (B + 1) / (cZ / (4 * (A₁ + 2)))) * ℓ * Real.log (ℓ + 2) ≤ Y) :
    L ^ (B + 1) * Real.exp (-(w * Y / L)) ≤
      (A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * ((n : ℝ) - 1))) * θ *
        Real.exp (-(cZ / (4 * (A₁ + 2)) * Y / ℓ))) := by
  have hA2 : 0 < A₁ + 2 := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hAℓ : 0 < (A₁ + 2) * ℓ := mul_pos hA2 hℓ0
  obtain ⟨g, hgdef⟩ : ∃ g, g = Real.log (ℓ + 2) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = 2 / c2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = 4 * (B + 1) / cZ := ⟨_, rfl⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = Y / ((A₁ + 2) * ℓ) := ⟨_, rfl⟩
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hg4 : Real.log 4 ≤ g := by rw [hgdef]; exact Real.log_le_log (by norm_num) (by linarith)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have hg : 1.38 ≤ g := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hr0 : 0 ≤ r := by rw [hr]; exact (div_pos two_pos hc2).le
  have hs0 : 0 ≤ s := by rw [hs]; exact (div_pos (by linarith) hcZ).le
  have hQ : (A₁ + 2) * (a + 1 + 2 / c2) + (B + 1) / (cZ / (4 * (A₁ + 2))) = (A₁ + 2) * (a + 1 + r + s) := by
    rw [hr, hs]; field_simp
  rw [hQ, ← hgdef] at hY
  have hμP : (a + 1 + r + s) * g ≤ μ := by
    rw [hμdef, le_div_iff₀ hAℓ]
    have : (a + 1 + r + s) * g * ((A₁ + 2) * ℓ) = (A₁ + 2) * (a + 1 + r + s) * ℓ * g := by ring
    linarith
  have hμ0 : 0 ≤ μ := le_trans (mul_nonneg (by linarith) hg0) hμP
  have hw0 : 0 ≤ w := by linarith
  have hwl : w * μ ≤ w * Y / L := by
    rw [le_div_iff₀ hL0]
    calc w * μ * L ≤ w * μ * ((A₁ + 2) * ℓ) := mul_le_mul_of_nonneg_left hLℓ (mul_nonneg hw0 hμ0)
      _ = w * Y := by rw [hμdef]; field_simp
  have hwμ : w * ((a + 1 + r + s) * g) ≤ w * μ := mul_le_mul_of_nonneg_left hμP hw0

  have hn1 : 0 ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk : a + Real.log 2 ≤ 3 / 4 * (g * (a + 1)) := by
    linarith [mul_nonneg (sub_nonneg.mpr hg) (sub_nonneg.mpr ha)]
  have T1 : (a + Real.log 2) * ((n : ℝ) - 1) ≤ 3 / 4 * (w * g * (a + 1)) := by
    calc (a + Real.log 2) * ((n : ℝ) - 1) ≤ 3 / 4 * (g * (a + 1)) * ((n : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hk hn1
      _ ≤ 3 / 4 * (g * (a + 1)) * w :=
          mul_le_mul_of_nonneg_left hwn (mul_nonneg (by norm_num) (mul_nonneg hg0 (by linarith)))
      _ = 3 / 4 * (w * g * (a + 1)) := by ring
  have hlθ : 0 ≤ Real.log (1 / θ) := Real.log_nonneg (by rw [le_div_iff₀ hθ0]; linarith)
  have hlog1θ : Real.log (1 / θ) = -Real.log θ := by rw [one_div, Real.log_inv]
  have hwr : 2 * Real.log (1 / θ) ≤ w * r := by
    have h := mul_le_mul_of_nonneg_right hw2 hr0
    have : c2 * Real.log (1 / θ) * r = 2 * Real.log (1 / θ) := by rw [hr]; field_simp
    linarith
  have T2 : -Real.log θ ≤ 3 / 4 * (w * g * r) := by
    have h3 : 3 / 4 * g * (2 * Real.log (1 / θ)) ≤ 3 / 4 * g * (w * r) :=
      mul_le_mul_of_nonneg_left hwr (mul_nonneg (by norm_num) hg0)
    have h4 : Real.log (1 / θ) ≤ 3 / 4 * g * (2 * Real.log (1 / θ)) := by
      linarith [mul_nonneg (sub_nonneg.mpr hg) hlθ]
    have : 3 / 4 * g * (w * r) = 3 / 4 * (w * g * r) := by ring
    linarith
  have hws : 4 * (B + 1) ≤ w * s := by
    have h := mul_le_mul_of_nonneg_right hw1 hs0
    have : cZ * s = 4 * (B + 1) := by rw [hs]; field_simp
    linarith
  have T3 : (B + 1) * g ≤ 3 / 4 * (w * g * s) := by
    have h7 : 3 / 4 * g * (4 * (B + 1)) ≤ 3 / 4 * g * (w * s) :=
      mul_le_mul_of_nonneg_left hws (mul_nonneg (by norm_num) hg0)
    have h8 : 0 ≤ g * (B + 1) := mul_nonneg hg0 (by linarith)
    have : 3 / 4 * g * (w * s) = 3 / 4 * (w * g * s) := by ring
    linarith
  have T4 : cZ / (4 * (A₁ + 2)) * Y / ℓ ≤ 1 / 4 * (w * μ) := by
    have he : cZ / (4 * (A₁ + 2)) * Y / ℓ = cZ / 4 * μ := by rw [hμdef]; field_simp
    rw [he]
    have := mul_le_mul_of_nonneg_right hw1 hμ0
    linarith
  have hexp : w * ((a + 1 + r + s) * g) = w * g * (a + 1) + w * g * r + w * g * s := by ring
  have hlogL : Real.log L ≤ Real.log (A₁ + 2) + g := by
    calc Real.log L ≤ Real.log ((A₁ + 2) * ℓ) := Real.log_le_log hL0 hLℓ
      _ = Real.log (A₁ + 2) + Real.log ℓ := Real.log_mul (by linarith) (by linarith)
      _ ≤ Real.log (A₁ + 2) + g := by
        have := Real.log_le_log hℓ0 (by linarith : ℓ ≤ ℓ + 2)
        rw [hgdef]; linarith
  have hlogLB : Real.log L * (B + 1) ≤ (Real.log (A₁ + 2) + g) * (B + 1) :=
    mul_le_mul_of_nonneg_right hlogL (by linarith)
  have hLHS : L ^ (B + 1) * Real.exp (-(w * Y / L)) = Real.exp (Real.log L * (B + 1) + -(w * Y / L)) := by
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
  have hRHS : (A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * ((n : ℝ) - 1))) * θ *
        Real.exp (-(cZ / (4 * (A₁ + 2)) * Y / ℓ))) =
      Real.exp (Real.log (A₁ + 2) * (B + 1) + (-((a + Real.log 2) * ((n : ℝ) - 1)) + Real.log θ +
        -(cZ / (4 * (A₁ + 2)) * Y / ℓ))) := by
    rw [Real.rpow_def_of_pos hA2]
    simp only [Real.exp_add, Real.exp_log hθ0]
  rw [hLHS, hRHS]
  apply Real.exp_le_exp.mpr
  linarith
private theorem sum_zero_multiplicity_le_two_mul_of_separated {M : ℕ} [NeZero M] (V : DirichletCharacter ℂ M → Finset ℂ)
    (m : DirichletCharacter ℂ M → ℂ → ℕ) (R K : ℝ) (hK : 0 ≤ K)
    (hwinV : ∀ χ, ∀ ρ ∈ V χ, ((∑ ρ' ∈ (V χ).filter (fun ρ' => |ρ'.im - ρ.im| ≤ 1), m χ ρ' : ℕ) : ℝ) ≤ K)
    (hsep : ∀ S : Finset (DirichletCharacter ℂ M × ℂ), (∀ p ∈ S, p.2 ∈ V p.1) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) → (S.card : ℝ) ≤ R) :
    ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ V χ, (m χ ρ : ℝ) ≤ 2 * R * K := by
  classical
  obtain ⟨rep, hrep⟩ : ∃ rep : DirichletCharacter ℂ M → ℤ → ℂ, ∀ χ k,
      k ∈ (V χ).image (fun ρ => ⌊ρ.im⌋) → rep χ k ∈ V χ ∧ ⌊(rep χ k).im⌋ = k := by
    refine ⟨fun χ k => if h : ∃ ρ ∈ V χ, ⌊ρ.im⌋ = k then h.choose else 0, ?_⟩
    intro χ k hk
    have h : ∃ ρ ∈ V χ, ⌊ρ.im⌋ = k := Finset.mem_image.mp hk
    simp only [dif_pos h]
    exact h.choose_spec
  have hper : ∀ χ, ∑ ρ ∈ V χ, (m χ ρ : ℝ) ≤ (((V χ).image (fun ρ => ⌊ρ.im⌋)).card : ℝ) * K := by
    intro χ
    calc ∑ ρ ∈ V χ, (m χ ρ : ℝ)
        = ∑ k ∈ (V χ).image (fun ρ => ⌊ρ.im⌋), ∑ ρ ∈ (V χ).filter (fun ρ => ⌊ρ.im⌋ = k), (m χ ρ : ℝ) :=
          (Finset.sum_fiberwise_of_maps_to (s := V χ) (t := (V χ).image (fun ρ : ℂ => ⌊ρ.im⌋))
            (g := fun ρ : ℂ => ⌊ρ.im⌋) (fun ρ hρ => Finset.mem_image_of_mem (fun ρ : ℂ => ⌊ρ.im⌋) hρ)
            (fun ρ => (m χ ρ : ℝ))).symm
      _ ≤ ∑ k ∈ (V χ).image (fun ρ => ⌊ρ.im⌋), K := by
          apply Finset.sum_le_sum
          intro k hk
          obtain ⟨hr1, hr2⟩ := hrep χ k hk
          refine le_trans ?_ (hwinV χ (rep χ k) hr1)
          push_cast
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ρ hρ
            rw [Finset.mem_filter] at hρ ⊢
            refine ⟨hρ.1, ?_⟩
            have hk' : ⌊ρ.im⌋ = k := hρ.2
            have e1 := Int.floor_le ρ.im
            have e2 := Int.lt_floor_add_one ρ.im
            have e3 := Int.floor_le (rep χ k).im
            have e4 := Int.lt_floor_add_one (rep χ k).im
            rw [hk'] at e1 e2
            rw [hr2] at e3 e4
            rw [abs_le]
            constructor <;> linarith
          · intro ρ _ _
            exact Nat.cast_nonneg _
      _ = (((V χ).image (fun ρ => ⌊ρ.im⌋)).card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpar : ∀ r : ℤ, (∑ χ : DirichletCharacter ℂ M,
      ((((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = r)).card : ℝ)) ≤ R := by
    intro r
    have hcard := Finset.card_sigma (Finset.univ : Finset (DirichletCharacter ℂ M))
      (fun χ => ((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = r))
    have hinj : Set.InjOn (fun q : (Σ _ : DirichletCharacter ℂ M, ℤ) => (q.1, rep q.1 q.2))
        ((Finset.univ : Finset (DirichletCharacter ℂ M)).sigma
          (fun χ => ((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = r)) : Set _) := by
      rintro ⟨χ, k⟩ hq ⟨χ', k'⟩ hq' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      subst h1
      have m1 := Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2
      have m2 := Finset.mem_filter.mp (Finset.mem_sigma.mp hq').2
      have f1 := (hrep χ k m1.1).2
      have f2 := (hrep χ k' m2.1).2
      rw [h2] at f1
      have hkk : k = k' := f1.symm.trans f2
      subst hkk
      rfl
    have hS := hsep (((Finset.univ : Finset (DirichletCharacter ℂ M)).sigma
          (fun χ => ((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = r))).image
          (fun q => (q.1, rep q.1 q.2))) ?_ ?_
    · rw [Finset.card_image_of_injOn hinj, hcard] at hS
      push_cast at hS
      exact hS
    · intro p hp
      obtain ⟨⟨χ, k⟩, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (hrep χ k (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).1).1
    · intro p hp p' hp' hne hfst
      obtain ⟨⟨χ, k⟩, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨⟨χ', k'⟩, hq', rfl⟩ := Finset.mem_image.mp hp'
      have hχ : χ = χ' := hfst
      subst hχ
      have hkk : k ≠ k' := by
        intro h
        apply hne
        subst h
        rfl
      have m1 := Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2
      have m2 := Finset.mem_filter.mp (Finset.mem_sigma.mp hq').2
      have f1 := (hrep χ k m1.1).2
      have f2 := (hrep χ k' m2.1).2
      have e1 := Int.floor_le (rep χ k).im
      have e2 := Int.lt_floor_add_one (rep χ k).im
      have e3 := Int.floor_le (rep χ k').im
      have e4 := Int.lt_floor_add_one (rep χ k').im
      rw [f1] at e1 e2
      rw [f2] at e3 e4
      have hr1 : k % 2 = r := m1.2
      have hr2 : k' % 2 = r := m2.2
      have hpar2 : k + 2 ≤ k' ∨ k' + 2 ≤ k := by omega
      show 1 ≤ |(rep χ k).im - (rep χ k').im|
      rcases hpar2 with h | h
      · have h' : (k : ℝ) + 2 ≤ k' := by exact_mod_cast h
        rw [abs_sub_comm]
        exact le_abs.mpr (Or.inl (by linarith))
      · have h' : (k' : ℝ) + 2 ≤ k := by exact_mod_cast h
        exact le_abs.mpr (Or.inl (by linarith))
  have htot : ∀ χ, ((V χ).image (fun ρ => ⌊ρ.im⌋)).card ≤
      (((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 0)).card +
        (((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 1)).card := by
    intro χ
    have hsub : (V χ).image (fun ρ => ⌊ρ.im⌋) ⊆ ((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 0) ∪
        ((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 1) := by
      intro k hk
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  calc ∑ χ, ∑ ρ ∈ V χ, (m χ ρ : ℝ) ≤ ∑ χ, (((V χ).image (fun ρ => ⌊ρ.im⌋)).card : ℝ) * K :=
        Finset.sum_le_sum (fun χ _ => hper χ)
    _ ≤ ∑ χ, (((((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 0)).card : ℝ) +
          ((((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 1)).card : ℝ)) * K := by
        apply Finset.sum_le_sum
        intro χ _
        apply mul_le_mul_of_nonneg_right _ hK
        exact_mod_cast htot χ
    _ = ((∑ χ, ((((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 0)).card : ℝ)) +
          (∑ χ, ((((V χ).image (fun ρ => ⌊ρ.im⌋)).filter (fun k => k % 2 = 1)).card : ℝ))) * K := by
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (R + R) * K := mul_le_mul_of_nonneg_right (add_le_add (hpar 0) (hpar 1)) hK
    _ = 2 * R * K := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (a B C : ℝ) (ha : 1 ≤ a) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hdens : ∀ (M : ℕ) [NeZero M] (T v : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 3 ≤ M → 2 ≤ T →
      (∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ Real.log ((M : ℝ) * T) * (1 - p.2.re) ≤ v ∧ |p.2.im| ≤ T ∧
        IsLZero p.1 p.2) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
      (S.card : ℝ) ≤ C * Real.exp (a * v) * Real.log ((M : ℝ) * T) ^ B)
    (κ c2 C₁ A₁ : ℝ) (hκ : κ ≤ 1 / 20) (hc2 : 0 < c2) (hA₁ : 1 ≤ A₁)
    (M : ℕ) [NeZero M] (Z : DirichletCharacter ℂ M → Finset ℂ) (m : DirichletCharacter ℂ M → ℂ → ℕ)
    (h8 : 8 ∣ M)
    (hZ : ∀ χ, ∀ ρ ∈ Z χ, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ (M : ℝ) ^ A₁ + 1)
    (hms : ∀ χ, ∀ ρ ∈ Z χ, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m χ ρ = 1)
    (hwin : ∀ χ, ∀ t : ℝ, ((∑ ρ ∈ (Z χ).filter (fun ρ => |ρ.im - t| ≤ 1), m χ ρ : ℕ) : ℝ) ≤
      C₁ * Real.log ((M : ℝ) * (|t| + 2)))
    (y : ℝ) (hy : 2 ≤ y)
    (hL : ((A₁ + 2) * (a + 1 + 2 / c2) + (B + 1) / (cZ / (4 * (A₁ + 2)))) * Real.log M *
      Real.log (Real.log M + 2) ≤ Real.log y)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθ : ∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ →
      c2 * Real.log (1 / θ) ≤ Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) * (1 - ρ.re)) :
    ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
      (4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1)) * θ *
        Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) := by
  classical
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM3 : 3 ≤ M := by omega
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hl2 := Real.log_two_gt_d9
  have hℓ : 2 ≤ Real.log M := by
    have h8' : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    have := Real.log_le_log (by norm_num) hMr
    linarith
  have hpow1 : 1 ≤ (M : ℝ) ^ A₁ := Real.one_le_rpow (by linarith) (by linarith)
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) := ⟨_, rfl⟩
  rw [← hLdef] at hθ
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by nlinarith)
  have hLT : L ≤ (A₁ + 2) * Real.log M := by
    have hstep : (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) ^ (A₁ + 2) := by
      rw [Real.rpow_add (by linarith : (0 : ℝ) < M), Real.rpow_two]
      nlinarith [mul_nonneg (sub_nonneg.mpr hpow1) (by nlinarith : (0 : ℝ) ≤ (M : ℝ) * ((M : ℝ) - 1)),
        mul_nonneg (sub_nonneg.mpr hMr) (by linarith : (0 : ℝ) ≤ (M : ℝ))]
    rw [hLdef]
    calc Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ≤ Real.log ((M : ℝ) ^ (A₁ + 2)) :=
          Real.log_le_log (mul_pos (by linarith) (by linarith)) hstep
      _ = (A₁ + 2) * Real.log M := Real.log_rpow (by linarith) _
  have hcZ : 0 < cZ := by
    have hch := (Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet).1
    unfold cZ
    exact lt_min hch (by norm_num)
  have hcZc : cZ ≤ Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet := by unfold cZ; exact min_le_left _ _
  have hcZ20 : cZ ≤ 1 / 20 := by unfold cZ; exact min_le_right _ _
  have hy0 : 0 < y := by linarith
  have hlogt : ∀ χ, ∀ ρ ∈ Z χ, 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) ∧
      Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ L := by
    intro χ ρ hρ
    have him := (hZ χ ρ hρ).2.2
    have ha0 := abs_nonneg ρ.im
    constructor
    · exact Real.log_pos (by nlinarith)
    · rw [hLdef]
      exact Real.log_le_log (mul_pos (by linarith) (by linarith))
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have hw : ∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → cZ ≤ L * (1 - ρ.re) := by
    intro χ ρ hρ hnr
    unfold InRegion at hnr
    push_neg at hnr
    obtain ⟨h1, h2⟩ := hlogt χ ρ hρ
    have h3 : cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by linarith
    rw [div_lt_iff₀ h1] at h3
    have h4 : 0 < 1 - ρ.re := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]
  have hZFR := (Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet).2
  have hwide : ∀ s : ℂ, InRegion cZ M s → InRegion (Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet) M s := by
    intro s hs
    unfold InRegion at hs ⊢
    have hl : 0 < Real.log ((M : ℝ) * (|s.im| + 2)) := Real.log_pos (by nlinarith [abs_nonneg s.im])
    have : cZ / Real.log ((M : ℝ) * (|s.im| + 2)) ≤
        Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet / Real.log ((M : ℝ) * (|s.im| + 2)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hcZc (inv_nonneg.mpr hl.le)
    exact (sub_le_sub_left this 1).trans hs
  have hin : ∀ χ, ∀ ρ ∈ Z χ, InRegion cZ M ρ →
      ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤ 0 := by
    intro χ ρ hρ hir
    obtain ⟨hsq, hne, him0, hder, _⟩ := hZFR M χ ρ (hwide ρ hir) (hZ χ ρ hρ).1
    have hm1 : m χ ρ = 1 := hms χ ρ hρ hder
    have hρeq : ((ρ.re : ℝ) : ℂ) = ρ := Complex.ext (by simp) (by simp [him0])
    have hre1 : ρ.re < 1 := by
      by_contra hc
      push_neg at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hc (hZ χ ρ hρ).1.2
    have hlow : 1 - 1 / (8 * Real.log M) < ρ.re := by
      have hir' := hir
      unfold InRegion at hir'
      rw [him0, abs_zero, zero_add] at hir'
      have hlM : 0 < Real.log M := by linarith
      have hl2M : Real.log M < Real.log ((M : ℝ) * 2) := Real.log_lt_log (by linarith) (by linarith)
      have hpos2 : 0 < Real.log ((M : ℝ) * 2) := by linarith
      have hq : 1 / (8 * Real.log M) * Real.log M = 1 / 8 := by field_simp
      have hq2 : 1 / (8 * Real.log M) * Real.log M < 1 / (8 * Real.log M) * Real.log ((M : ℝ) * 2) :=
        mul_lt_mul_of_pos_left hl2M (by positivity)
      have : cZ / Real.log ((M : ℝ) * 2) < 1 / (8 * Real.log M) := by
        rw [div_lt_iff₀ hpos2]
        linarith
      linarith
    have hExc : IsExcPair χ ρ.re := ⟨hsq, hne, by rw [hρeq]; exact (hZ χ ρ hρ).1.2, hlow, hre1⟩
    have hirc : InRegion cZ M ((ρ.re : ℝ) : ℂ) := by rw [hρeq]; exact hir
    have hex : ∃ p : DirichletCharacter ℂ M × ℝ, IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ) :=
      ⟨(χ, ρ.re), hExc, hirc⟩
    have heOf : eOf M = some hex.choose := by unfold eOf; rw [dif_pos hex]
    obtain ⟨⟨χ₁, β₁⟩, hq⟩ : ∃ q, hex.choose = q := ⟨_, rfl⟩
    have hspec := hex.choose_spec
    rw [hq] at hspec heOf
    obtain ⟨⟨_, hne1, hL1, _, _⟩, hir1⟩ := hspec
    have hz1 : IsLZero χ₁ (β₁ : ℂ) := ⟨Or.inl hne1, hL1⟩
    obtain ⟨hχeq, hβeq⟩ := (hZFR M χ₁ (β₁ : ℂ) (hwide _ hir1) hz1).2.2.2.2 χ ρ (hwide ρ hir) (hZ χ ρ hρ).1
    have hexc1 : excW (eOf M) χ ρ = 1 := by
      rw [heOf]
      simp only [excW]
      rw [if_pos ⟨hχeq, hβeq⟩]
    rw [hexc1, hm1]
    simp
  have hout : ∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ →
      ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
        (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) := by
    intro χ ρ _ _
    have hdiv : L * (1 - ρ.re) * Real.log y / L = (1 - ρ.re) * Real.log y := by
      rw [mul_assoc]
      exact mul_div_cancel_left₀ _ hLpos.ne'
    have hyr : y ^ (ρ.re - 1) = Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) := by
      rw [Real.rpow_def_of_pos hy0, hdiv]
      congr 1
      ring
    rw [hyr]
    have hE := Real.exp_pos (-(L * (1 - ρ.re) * Real.log y / L))
    have hex0 : (0 : ℝ) ≤ excW (eOf M) χ ρ := Nat.cast_nonneg _
    nlinarith [mul_nonneg hex0 hE.le]
  obtain ⟨W, hWdef⟩ : ∃ W : DirichletCharacter ℂ M → Finset ℂ,
      W = fun χ => (Z χ).filter (fun ρ => ¬ InRegion cZ M ρ) := ⟨_, rfl⟩
  have hWmem : ∀ χ ρ, ρ ∈ W χ ↔ ρ ∈ Z χ ∧ ¬ InRegion cZ M ρ := by
    intro χ ρ
    simp only [hWdef, Finset.mem_filter]
  have hsplit : ∀ χ, ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
      ∑ ρ ∈ W χ, (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) := by
    intro χ
    rw [← Finset.sum_filter_add_sum_filter_not (Z χ) (InRegion cZ M)]
    have h1 : ∑ ρ ∈ (Z χ).filter (fun ρ => InRegion cZ M ρ),
        ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤ 0 :=
      Finset.sum_nonpos (fun ρ hρ => hin χ ρ (Finset.mem_filter.mp hρ).1 (Finset.mem_filter.mp hρ).2)
    have h2 := Finset.sum_le_sum (s := (Z χ).filter (fun ρ => ¬ InRegion cZ M ρ))
      (fun ρ hρ => hout χ ρ (Finset.mem_filter.mp hρ).1 (Finset.mem_filter.mp hρ).2)
    have h3 : W χ = (Z χ).filter (fun ρ => ¬ InRegion cZ M ρ) := by rw [hWdef]
    rw [h3]
    linarith
  obtain ⟨lev, hlev⟩ : ∃ lev : ℂ → ℕ, lev = fun ρ => ⌈L * (1 - ρ.re)⌉₊ - 1 := ⟨_, rfl⟩
  have hlev' : ∀ ρ, lev ρ = ⌈L * (1 - ρ.re)⌉₊ - 1 := by intro ρ; rw [hlev]
  have hlevinfo : ∀ χ, ∀ ρ ∈ W χ, lev ρ < ⌈L⌉₊ ∧ (lev ρ : ℝ) < L * (1 - ρ.re) ∧
      L * (1 - ρ.re) ≤ (lev ρ : ℝ) + 1 := by
    intro χ ρ hρ
    obtain ⟨hρZ, hnr⟩ := (hWmem χ ρ).mp hρ
    have hwc := hw χ ρ hρZ hnr
    have hre1 := (hZ χ ρ hρZ).2.1
    have hw0 : 0 < L * (1 - ρ.re) := by linarith
    have hwL : L * (1 - ρ.re) ≤ L := mul_le_of_le_one_right hLpos.le (by linarith)
    have h1 : 0 < ⌈L * (1 - ρ.re)⌉₊ := Nat.ceil_pos.mpr hw0
    have h2 : ⌈L * (1 - ρ.re)⌉₊ ≤ ⌈L⌉₊ := Nat.ceil_mono hwL
    have h3 : (⌈L * (1 - ρ.re)⌉₊ : ℝ) < L * (1 - ρ.re) + 1 := Nat.ceil_lt_add_one hw0.le
    have h4 : L * (1 - ρ.re) ≤ (⌈L * (1 - ρ.re)⌉₊ : ℝ) := Nat.le_ceil _
    have hc : ((⌈L * (1 - ρ.re)⌉₊ - 1 : ℕ) : ℝ) = (⌈L * (1 - ρ.re)⌉₊ : ℝ) - 1 := Nat.cast_pred h1
    rw [hlev', hc]
    refine ⟨by omega, by linarith, by linarith⟩
  have hK0 : 0 ≤ |C₁| * L := mul_nonneg (abs_nonneg _) hLpos.le
  have hLB : 0 < L ^ (B + 1) := Real.rpow_pos_of_pos hLpos _
  have hlevel : ∀ j : ℕ, ∑ χ, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
      (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) ≤
      2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
        Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) * Real.exp a * (1 / 2) ^ j := by
    intro j
    have hVsub : ∀ χ, ∀ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
        ρ ∈ Z χ ∧ ¬ InRegion cZ M ρ ∧ lev ρ = j := by
      intro χ ρ hρ
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hρ
      exact ⟨((hWmem χ ρ).mp h1).1, ((hWmem χ ρ).mp h1).2, h2⟩
    have hpt : ∀ χ, ∀ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
        Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) ≤
          (A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1))) * θ *
            Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) / L ^ (B + 1) := by
      intro χ ρ hρ
      obtain ⟨hρZ, hnr, hlj⟩ := hVsub χ ρ hρ
      have hinfo := hlevinfo χ ρ ((hWmem χ ρ).mpr ⟨hρZ, hnr⟩)
      rw [hlj] at hinfo
      have H := pow_mul_exp_neg_le_of_large_Y a B c2 θ cZ A₁ (Real.log M) (Real.log y) L (L * (1 - ρ.re)) (j + 1) ha hB hc2
        hcZ hA₁ hθ0 hθ1 hℓ hLpos hLT (hw χ ρ hρZ hnr) (hθ χ ρ hρZ hnr) (by omega)
        (by push_cast; linarith [hinfo.2.1]) hL
      rw [le_div_iff₀ hLB]
      linarith [H]
    have hwinV : ∀ χ, ∀ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
        ((∑ ρ' ∈ ((W χ).filter (fun ρ => lev ρ = j)).filter (fun ρ' => |ρ'.im - ρ.im| ≤ 1),
          m χ ρ' : ℕ) : ℝ) ≤ |C₁| * L := by
      intro χ ρ hρ
      have hρZ := (hVsub χ ρ hρ).1
      have hsubZ : (W χ).filter (fun ρ => lev ρ = j) ⊆ Z χ :=
        fun x hx => (hVsub χ x hx).1
      have h1 : (∑ ρ' ∈ ((W χ).filter (fun ρ => lev ρ = j)).filter (fun ρ' => |ρ'.im - ρ.im| ≤ 1),
          m χ ρ') ≤ ∑ ρ' ∈ (Z χ).filter (fun ρ' => |ρ'.im - ρ.im| ≤ 1), m χ ρ' :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ hsubZ)
      have h2 := hwin χ ρ.im
      obtain ⟨hlg, hlgL⟩ := hlogt χ ρ hρZ
      calc ((∑ ρ' ∈ ((W χ).filter (fun ρ => lev ρ = j)).filter (fun ρ' => |ρ'.im - ρ.im| ≤ 1),
            m χ ρ' : ℕ) : ℝ)
          ≤ ((∑ ρ' ∈ (Z χ).filter (fun ρ' => |ρ'.im - ρ.im| ≤ 1), m χ ρ' : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ C₁ * Real.log ((M : ℝ) * (|ρ.im| + 2)) := h2
        _ ≤ |C₁| * Real.log ((M : ℝ) * (|ρ.im| + 2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hlg.le
        _ ≤ |C₁| * L := mul_le_mul_of_nonneg_left hlgL (abs_nonneg _)
    have hsepS : ∀ S : Finset (DirichletCharacter ℂ M × ℂ),
        (∀ p ∈ S, p.2 ∈ (W p.1).filter (fun ρ => lev ρ = j)) →
        (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
        (S.card : ℝ) ≤ C * Real.exp (a * ((j : ℝ) + 1)) * L ^ B := by
      intro S hS hsep'
      have hcond : ∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧
          Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) * (1 - p.2.re) ≤ (j : ℝ) + 1 ∧
          |p.2.im| ≤ (M : ℝ) ^ A₁ + 3 ∧ IsLZero p.1 p.2 := by
        intro p hp
        obtain ⟨hρZ, hnr, hlj⟩ := hVsub p.1 p.2 (hS p hp)
        have hinfo := hlevinfo p.1 p.2 ((hWmem p.1 p.2).mpr ⟨hρZ, hnr⟩)
        rw [hlj] at hinfo
        have hwc := hw p.1 p.2 hρZ hnr
        obtain ⟨hz, hre1, him⟩ := hZ p.1 p.2 hρZ
        have hre2 : p.2.re ≤ 1 := by
          by_contra hc
          push_neg at hc
          nlinarith
        refine ⟨by linarith, hre2, ?_, by linarith, hz⟩
        rw [← hLdef]
        exact hinfo.2.2
      have hd := hdens M ((M : ℝ) ^ A₁ + 3) ((j : ℝ) + 1) S hM3 (by linarith) hcond hsep'
      rw [← hLdef] at hd
      exact hd
    have hcnt := sum_zero_multiplicity_le_two_mul_of_separated (fun χ => (W χ).filter (fun ρ => lev ρ = j)) m
      (C * Real.exp (a * ((j : ℝ) + 1)) * L ^ B) (|C₁| * L) hK0 hwinV hsepS
    have hexpj : Real.exp (a * ((j : ℝ) + 1)) * Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1))) =
        Real.exp a * (1 / 2 : ℝ) ^ j := by
      have h2 : (1 / 2 : ℝ) ^ j = Real.exp (j * Real.log (1 / 2)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [h2, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [one_div, Real.log_inv]
      push_cast
      ring
    have hG0 : 0 ≤ (A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1))) * θ *
        Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hθ0.le) (Real.exp_pos _).le)
    calc ∑ χ, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
          (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L))
        ≤ ∑ χ, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j), (m χ ρ : ℝ) *
            ((A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1))) * θ *
              Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) / L ^ (B + 1)) :=
          Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun ρ hρ =>
            mul_le_mul_of_nonneg_left (hpt χ ρ hρ) (Nat.cast_nonneg _)))
      _ = (∑ χ, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j), (m χ ρ : ℝ)) *
            ((A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1))) * θ *
              Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) / L ^ (B + 1)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun χ _ => by rw [Finset.sum_mul])
      _ ≤ (2 * (C * Real.exp (a * ((j : ℝ) + 1)) * L ^ B) * (|C₁| * L)) *
            ((A₁ + 2) ^ (B + 1) * (Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1))) * θ *
              Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) / L ^ (B + 1)) :=
          mul_le_mul_of_nonneg_right hcnt (div_nonneg hG0 hLB.le)
      _ = 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
            Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) *
            (Real.exp (a * ((j : ℝ) + 1)) * Real.exp (-((a + Real.log 2) * (((j + 1 : ℕ) : ℝ) - 1)))) *
            ((L ^ B * L) / L ^ (B + 1)) := by ring
      _ = 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
            Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) *
            (Real.exp a * (1 / 2 : ℝ) ^ j) * 1 := by
          rw [hexpj, ← Real.rpow_add_one hLpos.ne', div_self hLB.ne']
      _ = 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
            Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) * Real.exp a * (1 / 2) ^ j := by
          ring
  have hWlev : ∀ χ, ∑ ρ ∈ W χ, (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) =
      ∑ j ∈ Finset.range ⌈L⌉₊, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
        (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) := by
    intro χ
    exact (Finset.sum_fiberwise_of_maps_to (s := W χ) (t := Finset.range ⌈L⌉₊) (g := lev)
      (fun ρ hρ => Finset.mem_range.mpr (hlevinfo χ ρ hρ).1)
      (fun ρ => (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)))).symm
  have hC0 : 0 ≤ C := by linarith
  have hrp0 : 0 ≤ (A₁ + 2) ^ (B + 1) := Real.rpow_nonneg (by linarith) _
  have hE0 := Real.exp_pos (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))
  have hQ0 : 0 ≤ 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
      Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) * Real.exp a :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
      hC0) hrp0) hθ0.le) hE0.le) (Real.exp_pos _).le
  have hX0 : 0 ≤ 4 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
      Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
      hC0) hrp0) hθ0.le) hE0.le
  have hea : Real.exp a ≤ Real.exp (a + a * cZ / 2) := by
    apply Real.exp_le_exp.mpr
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ a) hcZ.le
    linarith
  calc ∑ χ, ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1)
      ≤ ∑ χ, ∑ ρ ∈ W χ, (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) :=
        Finset.sum_le_sum (fun χ _ => hsplit χ)
    _ = ∑ χ, ∑ j ∈ Finset.range ⌈L⌉₊, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
          (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) :=
        Finset.sum_congr rfl (fun χ _ => hWlev χ)
    _ = ∑ j ∈ Finset.range ⌈L⌉₊, ∑ χ, ∑ ρ ∈ (W χ).filter (fun ρ => lev ρ = j),
          (m χ ρ : ℝ) * Real.exp (-(L * (1 - ρ.re) * Real.log y / L)) := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range ⌈L⌉₊, 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
          Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) * Real.exp a * (1 / 2) ^ j :=
        Finset.sum_le_sum (fun j _ => hlevel j)
    _ = 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
          Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) * Real.exp a *
          ∑ j ∈ Finset.range ⌈L⌉₊, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 2 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
          Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) * Real.exp a * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hQ0
    _ = (4 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
          Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) * Real.exp a := by ring
    _ ≤ (4 * |C₁| * C * (A₁ + 2) ^ (B + 1) * θ *
          Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M))) * Real.exp (a + a * cZ / 2) :=
        mul_le_mul_of_nonneg_left hea hX0
    _ = (4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1)) * θ *
          Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
