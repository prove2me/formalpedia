-- Prove2me | solution 1 for Formalism.ValuationGridEstimates.grid_index_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:58.108178+00:00
-- url     : https://prove2.me/submissions/036756aa-fec8-4aa2-b57b-69ec8159d6f4

import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationBoundIndexed
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_ValuationRatioIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.ValuationGridEstimates
open Finset
private theorem sum_mul_add_smul_five_eq_add_sums {W : Type} (W0 : Finset W) (lam a b c d f : W → ℝ)
    (k1 k2 k3 k4 : ℝ) :
    ∑ w ∈ W0, lam w * (a w + k1 * b w + k2 * c w + k3 * d w + k4 * f w) =
      ∑ w ∈ W0, lam w * a w + k1 * ∑ w ∈ W0, lam w * b w + k2 * ∑ w ∈ W0, lam w * c w +
        k3 * ∑ w ∈ W0, lam w * d w + k4 * ∑ w ∈ W0, lam w * f w := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring
end Formalism.ValuationGridEstimates
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.ValuationGridEstimates
open Finset
namespace Formalism.ValuationGridEstimates
theorem _root_.solution : GridValuationBoundIndexed := by
  intro W X S m N lam δ ell N0 vr vx XX ch dd hh yy S0 cc ee qq vq H BN Bδ W0
    hlam hδ hN0 hvq hprime hlamL hdd hddN hyy hcc hvr hH hBN hBδ hqq
  classical

  have group : ∀ φ : ℕ → ℝ, (∀ l, 0 ≤ φ l) →
      ∑ w ∈ W0, lam w * φ (ell w) ≤ ∑ l ∈ W0.image ell, φ l * Real.log l := by
    intro φ hφ
    rw [← Finset.sum_fiberwise_of_maps_to (g := ell) (t := W0.image ell)
      (fun w hw => Finset.mem_image_of_mem ell hw)]
    refine Finset.sum_le_sum fun l _ => ?_
    have h1 : ∑ w ∈ W0 with ell w = l, lam w * φ (ell w) =
        φ l * ∑ w ∈ W0 with ell w = l, lam w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [(Finset.mem_filter.1 hw).2]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left
      (hlamL l _ (fun w hw => (Finset.mem_filter.1 hw).2)) (hφ l)
  have hprimes : ∀ l ∈ W0.image ell, l.Prime := by
    intro l hl
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hl
    exact hprime w
  have hBN0 : ∀ ij : Fin m × Fin m, 0 ≤ BN := fun ij => by
    simpa using hBN ij 0 ∅ (by simp)
  have hlog : ∀ s ∈ S0, 0 ≤ Real.log (qq s) := fun s hs => by
    simpa using hqq s hs ∅
  have hT1 : ∀ ij, ∑ w ∈ W0, lam w * (∑ x ∈ XX ij (ch w), |vx w x|) ≤
      ∑ b, ∑ x ∈ XX ij b, H x := by
    intro ij
    rw [← Finset.sum_fiberwise_of_maps_to (g := ch) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum fun b _ => ?_
    have h1 : ∑ w ∈ W0 with ch w = b, lam w * (∑ x ∈ XX ij (ch w), |vx w x|) =
        ∑ x ∈ XX ij b, ∑ w ∈ W0 with ch w = b, lam w * |vx w x| := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [(Finset.mem_filter.1 hw).2, Finset.mul_sum]
    rw [h1]
    exact Finset.sum_le_sum fun x _ => hH x _
  have hT2 : ∀ ij, ∑ w ∈ W0, lam w * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) ≤ N * BN := by
    intro ij
    have h1 : ∑ w ∈ W0, lam w * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) =
        ∑ s ∈ Icc (1 : ℤ) (hh ij), ∑ w ∈ W0, lam w * N0 ij s (ell w) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    rw [h1]
    have h2 : ∀ s ∈ Icc (1 : ℤ) (hh ij), ∑ w ∈ W0, lam w * N0 ij s (ell w) ≤ BN := by
      intro s _
      exact (group (N0 ij s) (hN0 ij s)).trans (hBN ij s _ hprimes)
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc] at h3
    have h4 : ((hh ij : ℤ) + 1 - 1).toNat = hh ij := by omega
    rw [h4] at h3
    have h5 : (hh ij : ℝ) ≤ N := by
      have := hdd ij
      have := hddN ij
      exact_mod_cast (by omega : hh ij ≤ N)
    have := hBN0 ij
    nlinarith
  have hT3 : ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ 1 := by
    refine (group (fun l => ((l : ℝ) ^ 2)⁻¹) (fun l => by positivity)).trans ?_
    have h1 := prime_budget_bound (fun _ => 0) 0 (fun P _ => by simp) (W0.image ell) hprimes
    simpa using h1
  have hT4 : ∑ w ∈ W0, lam w * δ w ≤ Bδ := hBδ W0
  have hT5 : ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) ≤
      ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
    have h1 : ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) =
        ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring
    rw [h1]
    refine Finset.sum_le_sum fun s hs => ?_
    have h2 := hqq s hs W0
    have h3 : (cc s : ℝ) ≤ ee s := by exact_mod_cast hcc s hs
    have h4 := hlog s hs
    calc (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s ≤ (cc s : ℝ) * Real.log (qq s) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (ee s : ℝ) * Real.log (qq s) := mul_le_mul_of_nonneg_right h3 h4
  have hT5nn : 0 ≤ ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hlam w)
      (Finset.sum_nonneg fun s _ => mul_nonneg (by positivity) (hvq w s))
  have hSnn : 0 ≤ ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
    Finset.sum_nonneg fun s hs => mul_nonneg (by positivity) (hlog s hs)
  set K : ℝ := 5 * (N * BN) + 2 * N + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)
    with hK
  have hper : ∀ ij, ∑ w ∈ W0, lam w * ((∑ x ∈ XX ij (ch w), |vx w x|) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ +
      6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) ≤
      (∑ b, ∑ x ∈ XX ij b, H x) + K := by
    intro ij
    rw [sum_mul_add_smul_five_eq_add_sums W0 lam (fun w => ∑ x ∈ XX ij (ch w), |vx w x|)
      (fun w => ∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) (fun w => ((ell w : ℝ) ^ 2)⁻¹)
      δ (fun w => ∑ s ∈ S0, (cc s : ℝ) * vq w s) 5 (dd ij) 6 (2 * yy ij)]
    have e1 := hT1 ij
    have e2 := hT2 ij
    have e3 : (dd ij : ℝ) * ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ 2 * N := by
      have h1 : (dd ij : ℝ) ≤ 2 * N := by exact_mod_cast hddN ij
      calc (dd ij : ℝ) * ∑ w ∈ W0, lam w * ((ell w : ℝ) ^ 2)⁻¹ ≤ (dd ij : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hT3 (by positivity)
        _ ≤ 2 * N := by linarith
    have e5 : 2 * (yy ij : ℝ) * ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s) ≤
        2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
      have h1 : (yy ij : ℝ) ≤ m := by exact_mod_cast hyy ij
      have h2 : 0 ≤ (yy ij : ℝ) := by positivity
      calc 2 * (yy ij : ℝ) * ∑ w ∈ W0, lam w * (∑ s ∈ S0, (cc s : ℝ) * vq w s)
          ≤ 2 * (yy ij : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
            mul_le_mul_of_nonneg_left hT5 (by positivity)
        _ ≤ 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
            mul_le_mul_of_nonneg_right (by linarith) hSnn
    rw [hK]
    linarith
  calc ∑ w ∈ W0, lam w * ∑ ij, vr w ij
      ≤ ∑ w ∈ W0, lam w * ∑ ij, ((∑ x ∈ XX ij (ch w), |vx w x|) +
        5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ +
        6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) :=
        Finset.sum_le_sum fun w hw =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hvr w hw ij) (hlam w)
    _ = ∑ ij, ∑ w ∈ W0, lam w * ((∑ x ∈ XX ij (ch w), |vx w x|) +
        5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ +
        6 * δ w + 2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ ij : Fin m × Fin m, ((∑ b, ∑ x ∈ XX ij b, H x) + K) := Finset.sum_le_sum fun ij _ => hper ij
    _ = (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) + (m : ℝ) ^ 2 * K := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fin]
        push_cast
        ring
    _ ≤ (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
        (m : ℝ) ^ 2 * (10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          simp
        · have hBN : 0 ≤ BN := hBN0 (⟨0, hm⟩, ⟨0, hm⟩)
          have h1 : K ≤ 10 * N * BN + 2 * N + 6 * Bδ +
              4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
            rw [hK]
            have : 0 ≤ (N : ℝ) * BN := mul_nonneg (by positivity) hBN
            have : 0 ≤ (m : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
              mul_nonneg (by positivity) hSnn
            nlinarith
          have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)
          linarith
end Formalism.ValuationGridEstimates
