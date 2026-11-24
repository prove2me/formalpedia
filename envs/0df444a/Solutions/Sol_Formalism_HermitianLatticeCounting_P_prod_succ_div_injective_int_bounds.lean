-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_succ_div_injective_int_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:36.989571+00:00
-- url     : https://prove2.me/submissions/382c54a7-900e-4216-af16-3f23e56ccb14

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_succ_div_injective_pos_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} (I : Finset ι) (x : ι → ℤ) (hinj : Set.InjOn x (I : Set ι)) (h0 : ∀ i ∈ I, x i ≠ 0)
    (h1 : ∀ i ∈ I, x i ≠ -1) :
    1 / ((I.card : ℝ) + 1) ≤ ∏ i ∈ I, (((x i : ℝ) + 1) / (x i : ℝ)) ∧
      ∏ i ∈ I, (((x i : ℝ) + 1) / (x i : ℝ)) ≤ (I.card : ℝ) + 1 := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not I (fun i => 0 < x i)
    (fun i => (((x i : ℝ) + 1) / (x i : ℝ)))
  have hPcard : (I.filter (fun i => 0 < x i)).card ≤ I.card := Finset.card_filter_le _ _
  have hQcard : (I.filter (fun i => ¬ 0 < x i)).card ≤ I.card := Finset.card_filter_le _ _
  have hPeq : ∏ i ∈ I.filter (fun i => 0 < x i), (((x i : ℝ) + 1) / (x i : ℝ)) =
      ∏ i ∈ I.filter (fun i => 0 < x i), ((((x i).toNat : ℕ) : ℝ) + 1) / (((x i).toNat : ℕ) : ℝ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hpos : 0 < x i := (Finset.mem_filter.mp hi).2
    have e : (((x i).toNat : ℕ) : ℝ) = (x i : ℝ) := by
      have := Int.toNat_of_nonneg hpos.le
      exact_mod_cast this
    rw [e]
  have injP : Set.InjOn (fun i => (x i).toNat) ((I.filter (fun i => 0 < x i) : Finset ι) : Set ι) := by
    intro i hi j hj hij
    have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    have hij' : (x i).toNat = (x j).toNat := hij
    apply hinj hi'.1 hj'.1
    have e1 := Int.toNat_of_nonneg hi'.2.le
    have e2 := Int.toNat_of_nonneg hj'.2.le
    rw [← e1, ← e2, hij']
  have hPb := prod_succ_div_injective_pos_bounds (I.filter (fun i => 0 < x i)) (fun i => (x i).toNat) injP
    (fun i hi => by
      have := (Finset.mem_filter.mp hi).2
      omega)
  have hQeq : ∏ i ∈ I.filter (fun i => ¬ 0 < x i), (((x i : ℝ) + 1) / (x i : ℝ)) =
      (∏ i ∈ I.filter (fun i => ¬ 0 < x i),
        ((((-x i - 1).toNat : ℕ) : ℝ) + 1) / (((-x i - 1).toNat : ℕ) : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hq := Finset.mem_filter.mp hi
    have hxi0 := h0 i hq.1
    have hxi1 := h1 i hq.1
    have hle : x i ≤ -2 := by
      have := hq.2
      omega
    have e : (((-x i - 1).toNat : ℕ) : ℝ) = -(x i : ℝ) - 1 := by
      have := Int.toNat_of_nonneg (show 0 ≤ -x i - 1 by omega)
      have e' : (((-x i - 1).toNat : ℕ) : ℤ) = -x i - 1 := this
      have e'' : ((((-x i - 1).toNat : ℕ) : ℤ) : ℝ) = ((-x i - 1 : ℤ) : ℝ) := by rw [e']
      push_cast at e''
      exact e''
    rw [e, inv_div, show -(x i : ℝ) - 1 = -((x i : ℝ) + 1) by ring,
      show -((x i : ℝ) + 1) + 1 = -(x i : ℝ) by ring, neg_div_neg_eq]
  have injQ : Set.InjOn (fun i => (-x i - 1).toNat)
      ((I.filter (fun i => ¬ 0 < x i) : Finset ι) : Set ι) := by
    intro i hi j hj hij
    have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    have hij' : (-x i - 1).toNat = (-x j - 1).toNat := hij
    apply hinj hi'.1 hj'.1
    have hi0 := h0 i hi'.1
    have hj0 := h0 j hj'.1
    have hi2 := hi'.2
    have hj2 := hj'.2
    omega
  have hQb := prod_succ_div_injective_pos_bounds (I.filter (fun i => ¬ 0 < x i)) (fun i => (-x i - 1).toNat) injQ
    (fun i hi => by
      have hq := Finset.mem_filter.mp hi
      have := h0 i hq.1
      have := h1 i hq.1
      have := hq.2
      omega)
  rw [← hsplit, hPeq, hQeq]
  obtain ⟨hP1, hP2⟩ := hPb
  obtain ⟨hQ1, hQ2⟩ := hQb
  have hPc : ((I.filter (fun i => 0 < x i)).card : ℝ) ≤ I.card := by exact_mod_cast hPcard
  have hQc : ((I.filter (fun i => ¬ 0 < x i)).card : ℝ) ≤ I.card := by exact_mod_cast hQcard
  set X := ∏ i ∈ I.filter (fun i => 0 < x i), ((((x i).toNat : ℕ) : ℝ) + 1) / (((x i).toNat : ℕ) : ℝ)
  set Y := ∏ i ∈ I.filter (fun i => ¬ 0 < x i),
    ((((-x i - 1).toNat : ℕ) : ℝ) + 1) / (((-x i - 1).toNat : ℕ) : ℝ)
  have hY0 : 0 < Y := by linarith
  have hYinv : Y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ1
  have hYinv0 : 0 ≤ Y⁻¹ := (inv_pos.mpr hY0).le
  have hN0 : (0:ℝ) < (I.card : ℝ) + 1 := by positivity
  constructor
  · have h1' : 1 / ((I.card : ℝ) + 1) ≤ Y⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hY0 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hP1 hYinv0]
  · nlinarith [mul_le_mul_of_nonneg_left hYinv (show (0:ℝ) ≤ X by linarith)]
end Formalism.HermitianLatticeCounting.P
