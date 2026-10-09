-- Prove2me | solution 1 for BCMPNetworks.Core.bcmp_product_form
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:46:08.118962+00:00
-- url     : https://prove2.me/submissions/0976c700-2700-4385-ade3-c4b1da6322e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_ProductForm
import Definitions.Def_BCMPNetworks_Core_IndependentBalance
import Theorems.Thm_BCMPNetworks_Core_productForm_independent_balance
import Theorems.Thm_BCMPNetworks_Core_independent_balance_imp_global_balance

-- Own helper (fully proved): the unnormalized product form is nonnegative.
open BCMPNetworks.Core in
theorem bcmp9df_productForm_nonneg {N R m : ℕ} (net : BCMPNetworks.Core.Network N R m)
    (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (he : ∀ i r, 0 ≤ e i r) (S : net.State) :
    0 ≤ net.productForm e S := by
  classical
  obtain ⟨S, hfit, -⟩ := S
  unfold Network.productForm
  apply mul_nonneg
  · unfold Network.d
    split_ifs
    · exact zero_le_one
    · have h := hnet.arrival_ok
      cases hA : net.arrival with
      | total lam =>
        simp only [hA] at h ⊢
        exact Finset.prod_nonneg fun n _ => h.1 n
      | perChain lam =>
        simp only [hA] at h ⊢
        exact Finset.prod_nonneg fun k _ => Finset.prod_nonneg fun n _ => h.1 k n
  · apply Finset.prod_nonneg
    intro i _
    have hf := hfit i
    have hterm : net.type i ≠ .fcfs → ∀ r (l : Fin (net.u i r)),
        0 ≤ e i r * net.A i r l / net.μs i r l := by
      intro ht r l
      have hA : 0 ≤ net.A i r l := Finset.prod_nonneg fun j _ => hnet.a_nonneg i r j
      exact div_nonneg (mul_nonneg (he i r) hA) (hnet.μs_pos i r l ht).le
    show 0 ≤ net.f e i (S i)
    generalize S i = x at hf ⊢
    rcases x with l | v | l
    · have ht : net.type i = .fcfs := by
        revert hf; cases net.type i <;> simp [LocalState.Fits]
      have hμ := hnet.μ_pos i ht
      simp only [Network.f]
      refine mul_nonneg (pow_nonneg (one_div_nonneg.mpr hμ.le) _) (List.prod_nonneg ?_)
      intro x hxl
      simp only [List.mem_map] at hxl
      obtain ⟨a, _, rfl⟩ := hxl
      exact he i a
    · have ht : net.type i ≠ .fcfs := by
        intro h; rw [h] at hf; simp [LocalState.Fits] at hf
      have h2 : ∀ r (l : Fin (net.u i r)),
          0 ≤ (e i r * net.A i r l / net.μs i r l) ^ (v r l) / ((v r l).factorial : ℝ) :=
        fun r l => div_nonneg (pow_nonneg (hterm ht r l) _) (Nat.cast_nonneg _)
      simp only [Network.f]
      split
      · exact mul_nonneg (Nat.cast_nonneg _)
          (Finset.prod_nonneg fun r _ => Finset.prod_nonneg fun l _ => h2 r l)
      · exact Finset.prod_nonneg fun r _ => Finset.prod_nonneg fun l _ => h2 r l
      · exact le_rfl
    · have ht : net.type i ≠ .fcfs := by
        intro h; rw [h] at hf; simp [LocalState.Fits] at hf
      simp only [Network.f]
      refine List.prod_nonneg ?_
      intro x hxl
      simp only [List.mem_map] at hxl
      obtain ⟨y, _, rfl⟩ := hxl
      exact hterm ht y.1 y.2

theorem solution {N R m : ℕ} (net : BCMPNetworks.Core.Network N R m)
    (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (he : ∀ i r, 0 ≤ e i r)
    (htraffic : net.TrafficEquations e) :
    BCMPNetworks.Core.GlobalBalance (net.productForm e) net.rate ∧
    ((∀ P Q : net.State → ℝ, net.IsEquilibrium P → net.IsEquilibrium Q → P = Q) →
      ∀ Z : ℝ, HasSum (net.productForm e) Z → 0 < Z →
        ∀ P : net.State → ℝ, net.IsEquilibrium P →
          ∀ S, P S = net.productForm e S / Z) := by
  have hGB := BCMPNetworks.Core.independent_balance_imp_global_balance net hnet _
    (BCMPNetworks.Core.productForm_independent_balance net hnet e he htraffic)
  refine ⟨hGB, ?_⟩
  intro huniq Z hZ hZpos P hP S
  have hQ : net.IsEquilibrium (fun S => net.productForm e S / Z) := by
    refine ⟨fun S => div_nonneg (bcmp9df_productForm_nonneg net hnet e he S) hZpos.le, ?_, ?_⟩
    · simpa [div_self hZpos.ne'] using hZ.div_const Z
    · intro j
      have := hGB j
      simp only [div_eq_mul_inv]
      calc net.productForm e j * Z⁻¹ * ∑' k, net.rate j k
          = Z⁻¹ * (net.productForm e j * ∑' k, net.rate j k) := by ring
        _ = Z⁻¹ * ∑' k, net.productForm e k * net.rate k j := by rw [this]
        _ = ∑' k, net.productForm e k * Z⁻¹ * net.rate k j := by
            rw [← tsum_mul_left]; congr 1; ext k; ring
  exact congrFun (huniq P _ hP hQ) S
