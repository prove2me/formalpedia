-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:20:37.986073+00:00
-- url     : https://prove2.me/submissions/4534353e-b34a-47cb-ac50-24fb4adcea70

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_shift_close_of_shift_close_of_periodic
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real

theorem tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (A : ℝ × ℝ → ℝ) (W : ℝ × ℝ → V n)
    (hsm : ∃ s₀ : ℝ, ContDiffOn ℝ ∞ A (Set.Ioi s₀ ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ W (Set.Ioi s₀ ×ˢ Set.univ))
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => A p - σ * P.T * p.1) (s, t)‖ ≤ ε)
    (hW : ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε)
    (d c : ℝ) (hA0 : TendstoZeroUnif (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d))
    (hW0 : TendstoZeroUnif (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c))) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d) ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c)) := by
  obtain ⟨s₀, hAs, hWs⟩ := hsm
  have hT := P.T_pos
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσT : σ * P.T ≠ 0 :=
    mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hT.ne'
  have hU : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hnhds : ∀ s t : ℝ, s₀ < s → Ioi s₀ ×ˢ (univ : Set ℝ) ∈ 𝓝 (s, t) :=
    fun s t h => hU.mem_nhds ⟨h, trivial⟩
  have hle : ∀ m : ℕ, ((m : ℕ∞) : WithTop ℕ∞) ≤ ∞ := fun m => by exact_mod_cast le_top
  have hx : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hxc : ∀ c₁ : ℝ, ContDiff ℝ ∞ (fun p : ℝ × ℝ => P.x (σ * P.T * p.2 + c₁)) :=
    fun c₁ => hx.comp (by fun_prop)
  have hlin : ContDiff ℝ ∞ (fun p : ℝ × ℝ => σ * P.T * p.1) := by fun_prop
  set L : ℝ × ℝ →L[ℝ] ℝ := (σ * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ with hL
  have hLapp : ∀ p : ℝ × ℝ, L p = σ * P.T * p.2 := fun p => by simp [hL]
  have hLn : ‖L‖ ≤ P.T := by
    have h1 : ‖σ * P.T‖ = P.T := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hσ1, abs_of_pos hT, one_mul]
    calc ‖L‖ ≤ ‖σ * P.T‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ := by rw [hL]; exact norm_smul_le (σ * P.T) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      _ ≤ P.T * 1 := mul_le_mul h1.le (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (norm_nonneg _) hT.le
      _ = P.T := mul_one _
  refine ⟨⟨⟨s₀, (hAs.sub hlin.contDiffOn).sub contDiffOn_const⟩, fun m ε hε => ?_⟩,
    ⟨⟨s₀, hWs.sub (hxc c).contDiffOn⟩, fun m ε hε => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨s₁, h⟩ := hA0 ε hε
      exact ⟨s₁, fun s hs t => by rw [norm_iteratedFDeriv_zero]; exact h s hs t⟩
    · obtain ⟨s₁, h⟩ := hA m hm ε hε
      refine ⟨max s₁ (s₀ + 1), fun s hs t => ?_⟩
      have hs1 : s ≥ s₁ := le_trans (le_max_left _ _) hs
      have hs0 : s₀ < s := by linarith [le_max_right s₁ (s₀ + 1)]
      have hca : ContDiffAt ℝ m (fun p : ℝ × ℝ => A p - σ * P.T * p.1) (s, t) :=
        (((hAs.sub hlin.contDiffOn).contDiffAt (hnhds s t hs0))).of_le (hle m)
      have heq : (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d) =
          (fun p : ℝ × ℝ => A p - σ * P.T * p.1) - fun _ => d := rfl
      rw [heq, iteratedFDeriv_sub_apply hca contDiffAt_const, iteratedFDeriv_const_of_ne hm.ne',
        Pi.zero_apply, sub_zero]
      exact h s hs1 t
  · have hyc : Continuous (iteratedFDeriv ℝ m P.x) := hx.continuous_iteratedFDeriv (hle m)
    have hxT : Function.Periodic P.x P.T := P.periodic
    have hper : ∀ a : ℝ, (∀ τ, P.x (τ + a) = P.x τ) →
        ∀ τ, iteratedFDeriv ℝ m P.x (τ + a) = iteratedFDeriv ℝ m P.x τ := by
      intro a ha τ
      rw [← iteratedFDeriv_comp_add_right]
      congr 1
      funext z
      exact ha z
    have hyT : Function.Periodic (iteratedFDeriv ℝ m P.x) P.T := hper P.T P.periodic
    set K : ℝ := P.T ^ m + 1 with hKdef
    have hK : 0 < K := by positivity
    obtain ⟨δ, hδ, hkey⟩ := shift_close_of_shift_close_of_periodic hT hx.continuous hyc hxT hyT
      hper (ε / 2 / K) (by positivity)
    obtain ⟨s₁, h1⟩ := hW m (min (ε / 2) (δ / 2)) (by positivity)
    obtain ⟨s₂, h2⟩ := hW0 (δ / 2) (by positivity)
    refine ⟨max (max s₁ s₂) (s₀ + 1), fun s hs t => ?_⟩
    have hs1 : s ≥ s₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have hs2 : s ≥ s₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have hs0 : s₀ < s := by linarith [le_max_right (max s₁ s₂) (s₀ + 1)]
    obtain ⟨c', hc'⟩ := h1 s hs1
    have hclose : ∀ τ, ‖P.x (τ + c') - P.x (τ + c)‖ ≤ δ := by
      intro τ
      have ht' : σ * P.T * (τ / (σ * P.T)) = τ := mul_div_cancel₀ τ hσT
      have e1 := hc' 0 (Nat.zero_le _) (τ / (σ * P.T))
      rw [norm_iteratedFDeriv_zero] at e1
      have e2 := h2 s hs2 (τ / (σ * P.T))
      simp only [ht'] at e1 e2
      calc ‖P.x (τ + c') - P.x (τ + c)‖
          = ‖(W (s, τ / (σ * P.T)) - P.x (τ + c)) - (W (s, τ / (σ * P.T)) - P.x (τ + c'))‖ := by
            congr 1; abel
        _ ≤ ‖W (s, τ / (σ * P.T)) - P.x (τ + c)‖ + ‖W (s, τ / (σ * P.T)) - P.x (τ + c')‖ :=
            norm_sub_le _ _
        _ ≤ δ / 2 + δ / 2 := add_le_add e2 (e1.trans (min_le_right _ _))
        _ = δ := by ring
    have hyclose := hkey c' c hclose
    set f : ℝ → V n := (fun τ => P.x (τ + c')) - (fun τ => P.x (τ + c)) with hfdef
    have hf1 : ContDiff ℝ ∞ (fun τ => P.x (τ + c')) := hx.comp (by fun_prop)
    have hf2 : ContDiff ℝ ∞ (fun τ => P.x (τ + c)) := hx.comp (by fun_prop)
    have hf : ContDiff ℝ ∞ f := hf1.sub hf2
    have hsplit : (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c)) =
        (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c')) + f ∘ L := by
      funext p
      simp only [Pi.add_apply, Function.comp_apply, hfdef, Pi.sub_apply, hLapp]
      abel
    have hWc : ContDiffAt ℝ m (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c')) (s, t) :=
      ((hWs.sub (hxc c').contDiffOn).contDiffAt (hnhds s t hs0)).of_le (hle m)
    have hfL : ContDiffAt ℝ m (f ∘ L) (s, t) :=
      ((hf.comp L.contDiff).of_le (hle m)).contDiffAt
    have hfd : ∀ τ, iteratedFDeriv ℝ m f τ =
        iteratedFDeriv ℝ m P.x (τ + c') - iteratedFDeriv ℝ m P.x (τ + c) := by
      intro τ
      rw [hfdef, iteratedFDeriv_sub_apply ((hf1.of_le (hle m)).contDiffAt)
        ((hf2.of_le (hle m)).contDiffAt), iteratedFDeriv_comp_add_right,
        iteratedFDeriv_comp_add_right]
    rw [hsplit, iteratedFDeriv_add_apply hWc hfL,
      L.iteratedFDeriv_comp_right hf (s, t) (hle m)]
    have b1 : ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c')) (s, t)‖
        ≤ ε / 2 := (hc' m le_rfl t).trans (min_le_left _ _)
    have b2 : ‖(iteratedFDeriv ℝ m f (L (s, t))).compContinuousLinearMap fun _ => L‖ ≤
        ε / 2 / K * P.T ^ m := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hfd]
      exact mul_le_mul (hyclose _) (pow_le_pow_left₀ (norm_nonneg _) hLn m)
        (by positivity) (by positivity)
    have b3 : ε / 2 / K * P.T ^ m ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      nlinarith [pow_nonneg hT.le m]
    exact (norm_add_le _ _).trans (by linarith)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (A : ℝ × ℝ → ℝ) (W : ℝ × ℝ → V n)
    (hsm : ∃ s₀ : ℝ, ContDiffOn ℝ ∞ A (Set.Ioi s₀ ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ W (Set.Ioi s₀ ×ˢ Set.univ))
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => A p - σ * P.T * p.1) (s, t)‖ ≤ ε)
    (hW : ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε)
    (d c : ℝ) (hA0 : TendstoZeroUnif (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d))
    (hW0 : TendstoZeroUnif (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c))) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d) ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c)) :=
  tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase_aux H hH P σ hσ A W hsm hA hW d c hA0 hW0
