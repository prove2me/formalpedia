-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.ratio_unscale_and_quality_padding
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:26:42.286972+00:00
-- url     : https://prove2.me/submissions/955aa0f7-d698-442a-a66b-3c173041a919

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

noncomputable def scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k) : Physical n k :=
  { g with u := fun e => S * g.u e }

@[simp] lemma scalePhysical_graph {n k : ℕ} (S : ℝ) (g : Physical n k) :
    (scalePhysical S g).graph = g.graph := rfl
@[simp] lemma scalePhysical_active {n k : ℕ} (S : ℝ) (g : Physical n k) :
    (scalePhysical S g).active = g.active := rfl
@[simp] lemma scalePhysical_gamma {n k : ℕ} (S : ℝ) (g : Physical n k) :
    (scalePhysical S g).gamma = g.gamma := rfl
@[simp] lemma scalePhysical_u {n k : ℕ} (S : ℝ) (g : Physical n k) (e : Fin k) :
    (scalePhysical S g).u e = S * g.u e := rfl

lemma physicalNorm_scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k) (x : Fin n → ℝ) :
    physicalNorm (scalePhysical S g) x = S * physicalNorm g x := by
  classical
  simp only [physicalNorm, scalePhysical_graph, scalePhysical_active, scalePhysical_u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

lemma cutCapacity_scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k)
    (C : Finset (Fin n)) :
    cutCapacity (scalePhysical S g) C = S * cutCapacity g C := by
  classical
  simp only [cutCapacity, scalePhysical_graph, scalePhysical_active, scalePhysical_u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) <;> simp [hc]

@[simp] lemma cutDemand_scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k)
    (C : Finset (Fin n)) :
    cutDemand (scalePhysical S g) C = cutDemand g C := rfl

lemma ratioGuarantee_scalePhysical {n k : ℕ} {S G U K : ℝ} (g : Physical n k)
    (C : Finset (Fin n)) (hS : 0 < S)
    (h : RatioGuarantee (scalePhysical S g) K G (S * U) C) :
    RatioGuarantee g K G U C := by
  classical
  rcases h with ⟨hG, hU, hdem, hcap, hratio⟩
  have hU0 : 0 < U := by
    by_contra hn
    have hz : S * U ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hS.le (le_of_not_gt hn)
    exact (not_lt_of_ge hz) hU
  refine ⟨hG, hU0, ?_, ?_, ?_⟩
  · simpa using hdem
  · rw [cutCapacity_scalePhysical] at hcap
    exact (mul_le_mul_iff_of_pos_left hS).mp hcap
  · intro x hx
    have hSx : 0 < physicalNorm (scalePhysical S g) x := by
      rw [physicalNorm_scalePhysical]
      exact mul_pos hS hx
    have hh := hratio x hSx
    rw [physicalNorm_scalePhysical] at hh
    have hleft : G / U = S * (G / (S * U)) := by
      field_simp [hS.ne', hU0.ne']
    have hright : (dot g.gamma x / physicalNorm g x) / K =
        S * ((dot (scalePhysical S g).gamma x /
          (S * physicalNorm g x)) / K) := by
      simp only [scalePhysical_gamma]
      field_simp [hS.ne', hx.ne']
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hh hS.le

lemma RatioGuarantee.mono_quality {n k : ℕ} {g : Physical n k}
    {K₀ K G U : ℝ} {C : Finset (Fin n)} (hK₀ : 0 < K₀) (hKK : K₀ ≤ K)
    (h : RatioGuarantee g K₀ G U C) : RatioGuarantee g K G U C := by
  rcases h with ⟨hG, hU, hdem, hcap, hratio⟩
  refine ⟨hG, hU, hdem, hcap, ?_⟩
  intro x hx
  have hh := hratio x hx
  have hK : 0 < K := lt_of_lt_of_le hK₀ hKK
  let r := dot g.gamma x / physicalNorm g x
  by_cases hr0 : 0 ≤ r
  · have hnonneg : 0 ≤ r / K := div_nonneg hr0 hK.le
    have hneg : G / U < 0 := div_neg_of_neg_of_pos hG hU
    exact hneg.le.trans hnonneg
  · have hrn : r ≤ 0 := le_of_not_ge hr0
    have hr : r / K₀ ≤ r / K := by
      rw [div_le_div_iff₀ hK₀ hK]
      nlinarith
    exact hh.trans hr

end DecrAlmostLinearSSSP.Decremental.NonemptyCut

open DecrAlmostLinearSSSP.Decremental DecrAlmostLinearSSSP.Decremental.NonemptyCut

theorem solution {n k : ℕ} {S G U K₀ K : ℝ}
    (g : Physical n k) (C : Finset (Fin n)) (hS : 0 < S)
    (hK₀ : 0 < K₀) (hKK : K₀ ≤ K)
    (h : RatioGuarantee { g with u := fun e => S * g.u e } K₀ G (S * U) C) :
    RatioGuarantee g K G U C := by
  exact RatioGuarantee.mono_quality hK₀ hKK (ratioGuarantee_scalePhysical g C hS h)
