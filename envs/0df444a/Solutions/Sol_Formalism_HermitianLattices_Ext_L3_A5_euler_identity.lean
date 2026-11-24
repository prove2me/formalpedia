-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.euler_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:45.872797+00:00
-- url     : https://prove2.me/submissions/3dbaae98-6555-40f2-8965-461c0f52179a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_tendsto_weighted
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_dif_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_nrm_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_dif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι X : Type*} {q : ι → ℝ}
open scoped Classical
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (hρS : ∀ i ∈ S, ∀ j, ρ i j = 1)
    (hρb : ∀ i j, |ρ i (j + 1) - ρ i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c c0 C : ℝ) (E : ι → ℝ)
    (hc : c0 = 0 → c = 0)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v)
    (H3 : ∀ S' : Finset ι, S ⊆ S' →
      Tendsto (fun j => sc j * ∑ n ∈ B j, a n * ∏ i ∈ S', ρ i (val n i)) atTop
        (𝓝 (c0 * ∏ i ∈ S', E i))) :
    c * ∑' v : ι →₀ ℕ, v.prod (dif ρ) / nrm q v = c0 * ∏' i, E i := by
  have key : ∀ S' : Finset ι, S ⊆ S' →
      c0 * ∏ i ∈ S', E i = c * ∑' v : ι →₀ ℕ,
        (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v := by
    intro S' hSS'
    have h0 : ∀ i, cut ρ S' i 0 = 1 := fun i => by simp [cut, hρ0]
    have hS : ∀ i ∈ S, ∀ j, cut ρ S' i j = 1 := fun i hi j => by
      simp [cut, hSS' hi, hρS i hi j]
    have hb : ∀ i j, |cut ρ S' i (j + 1) - cut ρ S' i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := by
      intro i j
      by_cases hi : i ∈ S'
      · simpa [cut, hi] using hρb i j
      · simp only [cut, if_neg hi, sub_self, abs_zero]
        exact div_nonneg (by positivity) (by linarith [hq i])
    have hT := tendsto_weighted hq hsum S h0 hS hb val B a sc c C H1 H2
    have e1 : ∀ n, (val n).prod (cut ρ S') = ∏ i ∈ S', ρ i (val n i) :=
      fun n => prod_cut hρ0 S' (val n)
    have e2 : ∀ v : ι →₀ ℕ, v.prod (dif (cut ρ S')) =
        if v.support ⊆ S' then v.prod (dif ρ) else 0 :=
      fun v => prod_dif_cut ρ S' v
    simp only [e1, e2] at hT
    exact tendsto_nhds_unique (H3 S' hSS') hT
  set L := ∑' v : ι →₀ ℕ, v.prod (dif ρ) / nrm q v with hL
  have hG : Tendsto (fun S' : Finset ι => ∑' v : ι →₀ ℕ,
      (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v) atTop (𝓝 L) := by
    refine tendsto_tsum_of_dominated_convergence
      (f := fun S' v => (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v)
      (g := fun v => v.prod (dif ρ) / nrm q v)
      (bound := fun v => |v.prod (dif ρ)| / nrm q v)
      (summable_dif hq hsum hρb) ?_ ?_
    · intro v
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop v.support] with S' hS'
      try dsimp only
      rw [if_pos (show v.support ⊆ S' from hS')]
    · filter_upwards with S' v
      try dsimp only
      have hw := nrm_pos hq v
      split_ifs
      · rw [Real.norm_eq_abs, abs_div, abs_of_pos hw]
      · rw [zero_div, norm_zero]
        exact div_nonneg (abs_nonneg _) hw.le
  by_cases hc0 : c0 = 0
  · simp [hc0, hc hc0]
  · have hP : HasProd E (c * L / c0) := by
      have h1 : Tendsto (fun S' : Finset ι => c * (∑' v : ι →₀ ℕ,
          (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v) / c0) atTop
          (𝓝 (c * L / c0)) := (hG.const_mul c).div_const c0
      have h2 : (fun S' : Finset ι => c * (∑' v : ι →₀ ℕ,
          (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v) / c0)
          =ᶠ[atTop] fun S' => ∏ i ∈ S', E i := by
        filter_upwards [eventually_ge_atTop S] with S' hS'
        rw [← key S' hS', mul_comm, mul_div_assoc, div_self hc0, mul_one]
      exact h1.congr' h2
    rw [hP.tprod_eq, mul_div_assoc', mul_comm c0, mul_div_assoc, div_self hc0, mul_one]
end Formalism.HermitianLattices.Ext.L3.A5
