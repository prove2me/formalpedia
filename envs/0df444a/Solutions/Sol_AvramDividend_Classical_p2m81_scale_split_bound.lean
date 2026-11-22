-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_scale_split_bound
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T12:10:30.05016+00:00
-- url     : https://prove2.me/submissions/3f745494-957b-4707-ac3c-b57d414a7bb8

import Theorems.Thm_AvramDividend_Classical_p2m81_scale_head_bound
import Theorems.Thm_AvramDividend_Classical_p2m81_scale_tail_bound

open MeasureTheory Filter Set Topology
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (ψ : ℝ → ℝ) (q a β0 K : ℝ) (ha : 0 < a)
    (hNonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hMono : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ y → W x ≤ W y)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → q < ψ θ → IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * W y) (Ioi (0 : ℝ)) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W y) = (ψ θ - q)⁻¹)
    (hβ0nn : 0 ≤ β0) (hβ0lt : q < ψ β0)
    (hK : (∫ x in Ioi (0 : ℝ), Real.exp (-(β0 * x)) * W x) = K)
    (hEv : ∀ᶠ θ in atTop, 0 < θ ∧ q < ψ θ) :
    ∀ᶠ β in atTop, β / (ψ β - q) ≤ W a + β * Real.exp (-(β - β0) * a) * K := by
  filter_upwards [hEv, eventually_ge_atTop β0] with β hβ hβ0
  obtain ⟨hInt, hVal⟩ := hLap β hβ.1.le hβ.2
  have hIntHead := hInt.mono_set (show Ioc (0 : ℝ) a ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hIntTail := hInt.mono_set (Ioi_subset_Ioi ha.le)
  have hHead := p2m81_scale_head_bound W a β ha hβ.1
    (fun x hx => hMono x a hx.1.le ha.le hx.2) (hNonneg a ha.le) hIntHead
  have hTail := p2m81_scale_tail_bound W a β0 β K ha hβ0
    (fun x hx => hNonneg x hx.le) (hLap β0 hβ0nn hβ0lt).1 hIntTail hK.le
  have hd : Disjoint (Ioc (0 : ℝ) a) (Ioi a) :=
    disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  have hsplit := setIntegral_union hd measurableSet_Ioi hIntHead hIntTail
  rw [Ioc_union_Ioi_eq_Ioi ha.le, hVal] at hsplit
  have hbound : (ψ β - q)⁻¹ ≤ W a / β + Real.exp (-(β - β0) * a) * K :=
    hsplit.le.trans (add_le_add hHead hTail)
  calc
    β / (ψ β - q) = β * (ψ β - q)⁻¹ := div_eq_mul_inv _ _
    _ ≤ β * (W a / β + Real.exp (-(β - β0) * a) * K) :=
      mul_le_mul_of_nonneg_left hbound hβ.1.le
    _ = W a + β * Real.exp (-(β - β0) * a) * K := by
      rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ hβ.1.ne', ← mul_assoc]
