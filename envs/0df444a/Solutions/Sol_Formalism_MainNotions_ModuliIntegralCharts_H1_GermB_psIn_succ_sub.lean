-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.psIn_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:02.8803+00:00
-- url     : https://prove2.me/submissions/deb754ca-d9e2-43f6-807f-18f0567f6a79

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_rename_mem_orig_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) S) :
    psIn d (m + 1) r g - psIn d m r g ∈ orig S (Fin n' × Fin d) ^ (m + 1) := by
  unfold psIn
  rw [← map_sub]
  apply rename_mem_orig_pow
  unfold psTrunc
  have memD : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ),
      e ∈ (degLE k : Finset ((Fin n × Fin d) →₀ ℕ)) ↔ (e.sum fun _ a => a) ≤ k := by
    intro k e
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.sum fun _ a => a := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
          exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · ext i
        simp
  have monoMem : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ) (c : S), k ≤ (e.sum fun _ a => a) →
      MvPolynomial.monomial e c ∈ orig S (Fin n × Fin d) ^ k := by
    intro k e c hk
    have hmem : (e.prod fun i a => MvPolynomial.X i ^ a) ∈ orig S (Fin n × Fin d) ^ (e.sum fun _ a => a) := by
      simp only [Finsupp.prod, Finsupp.sum]
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Ideal.prod_mem_prod
      intro i _
      apply Ideal.pow_mem_pow
      unfold orig
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [MvPolynomial.monomial_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hmem)
  have hsub : (degLE m : Finset ((Fin n × Fin d) →₀ ℕ)) ⊆ degLE (m + 1) := by
    intro e he
    rw [memD] at he ⊢
    omega
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply Ideal.sum_mem
  intro e he
  rw [Finset.mem_sdiff, memD, memD] at he
  apply monoMem
  omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
