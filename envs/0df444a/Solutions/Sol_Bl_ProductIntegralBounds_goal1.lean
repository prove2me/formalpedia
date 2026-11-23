-- Prove2me | solution 1 for Bl.ProductIntegralBounds.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:47.537981+00:00
-- url     : https://prove2.me/submissions/06ef93c1-948a-476d-b62c-5ba3c4ad737b

import Mathlib
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v w
namespace Bl.ProductIntegralBounds
private theorem mulBd {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (F G : MvPowerSeries τ K)
    (hF : ∀ d, ‖MvPowerSeries.coeff d F‖ ≤ a) (hG : ∀ d, ‖MvPowerSeries.coeff d G‖ ≤ b) :
    ∀ d, ‖MvPowerSeries.coeff d (F * G)‖ ≤ a * b := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) ha
private theorem prodInt {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w} {ι : Type v}
    (X : ι → MvPowerSeries τ K) (s : Finset ι)
    (hX : ∀ i ∈ s, ∀ d, ‖MvPowerSeries.coeff d (X i)‖ ≤ 1) :
    ∀ d, ‖MvPowerSeries.coeff d (∏ i ∈ s, X i)‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · rw [norm_one]
    · rw [norm_zero]; exact zero_le_one
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have h := mulBd zero_le_one zero_le_one (X a) (∏ i ∈ t, X i)
      (hX a (Finset.mem_insert_self a t))
      (ih (fun i hi => hX i (Finset.mem_insert_of_mem hi)))
    intro d
    have := h d
    rwa [one_mul] at this
end Bl.ProductIntegralBounds
end

set_option autoImplicit false
universe u v w
open Bl Bl.ProductIntegralBounds
namespace Bl.ProductIntegralBounds
theorem _root_.solution :
  ∀ {K : Type u} [inst : NormedField.{u} K] [IsUltrametricDist.{u} K] {τ : Type w} {ι : Type v} {C : Real},
  LE.le.{0} 0 C →
    ∀ (X Y : ι → MvPowerSeries.{w, u} τ K) (s : Finset.{v} ι),
      (∀ (i : ι), Membership.mem.{v, v} s i → Bl.ProductIntegralBounds.IntegralMv.{u, w} (X i)) →
        (∀ (i : ι), Membership.mem.{v, v} s i → Bl.ProductIntegralBounds.IntegralMv.{u, w} (Y i)) →
          (∀ (i : ι),
              Membership.mem.{v, v} s i →
                Bl.ProductIntegralBounds.Bd.{u, w} C (HSub.hSub.{max u w, max u w, max u w} (X i) (Y i))) →
            Bl.ProductIntegralBounds.Bd.{u, w} C
              (HSub.hSub.{max u w, max u w, max u w} (Finset.prod.{v, max u w} s fun (i : ι) ↦ X i)
                (Finset.prod.{v, max u w} s fun (i : ι) ↦ Y i)) := by
  intro K _ _ τ ι C hC X Y s hX hY hXY
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d
    rw [Finset.prod_empty, Finset.prod_empty, sub_self, map_zero, norm_zero]
    exact hC
  | insert a t hat ih =>
    have ih' := ih (fun i hi => hX i (Finset.mem_insert_of_mem hi))
      (fun i hi => hY i (Finset.mem_insert_of_mem hi))
      (fun i hi => hXY i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hat, Finset.prod_insert hat]
    have e : X a * ∏ i ∈ t, X i - Y a * ∏ i ∈ t, Y i
        = X a * (∏ i ∈ t, X i - ∏ i ∈ t, Y i) + (X a - Y a) * ∏ i ∈ t, Y i := by ring
    rw [e]
    have h1 := mulBd zero_le_one hC (X a) _ (hX a (Finset.mem_insert_self a t)) ih'
    have h2 := mulBd hC zero_le_one (X a - Y a) _ (hXY a (Finset.mem_insert_self a t))
      (prodInt Y t (fun i hi => hY i (Finset.mem_insert_of_mem hi)))
    intro d
    rw [map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := h1 d; rwa [one_mul] at this
    · have := h2 d; rwa [mul_one] at this
end Bl.ProductIntegralBounds
