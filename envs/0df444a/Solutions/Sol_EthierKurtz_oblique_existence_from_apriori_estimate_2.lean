-- Prove2me | solution 2 for EthierKurtz.oblique_existence_from_apriori_estimate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:55:29.895926+00:00
-- url     : https://prove2.me/submissions/e6335908-a3b6-4b3d-b5a4-ab17d8f44848

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_closedRegionRestriction

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz.EZ213

theorem const_mem_graph {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (hopen : IsOpen Ω)
    (μ : ℝ) (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℝ) :
    (BoundedContinuousFunction.const (closure Ω) k, (0 : (closure Ω) →ᵇ ℝ)) ∈
      EthierKurtz.obliqueDiffusionGraph Ω μ a b c := by
  simp only [EthierKurtz.obliqueDiffusionGraph, Set.mem_setOf_eq]
  set F := EthierKurtz.closedRegionRestriction
    (BoundedContinuousFunction.const (closure Ω) k) with hFdef
  have hF : ∀ x ∈ Ω, F x = k := by
    intro x hx
    simp only [hFdef, EthierKurtz.closedRegionRestriction, dif_pos (subset_closure hx)]
    rfl
  have hD : ∀ x ∈ Ω, fderiv ℝ F x = 0 := by
    intro x hx
    have : F =ᶠ[𝓝 x] fun _ => k := by
      filter_upwards [hopen.mem_nhds hx] with y hy using hF y hy
    rw [this.fderiv_eq]; simp
  have hD2 : ∀ x ∈ Ω, ∀ j : Fin d,
      fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x = 0 := by
    intro x hx j
    have : (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp [hD y hy]
    rw [this.fderiv_eq]; simp
  have hG : ∀ x, EthierKurtz.closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) x = 0 := by
    intro x
    unfold EthierKurtz.closedRegionRestriction
    split_ifs <;> rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact contDiffOn_const.congr (fun x hx => hF x hx)
  · intro i j
    refine ⟨(continuousOn_const (c := (0 : ℝ))).congr (fun x hx => by simp [hD2 x hx j]), 1, 0, one_pos, le_rfl, ?_⟩
    intro ρ _ _ x z _ y hy w hw
    have hy' := (connectedComponentIn_subset _ _ hy).1
    have hw' := (connectedComponentIn_subset _ _ hw).1
    simp [hD2 y hy' j, hD2 w hw' j]
  · intro x hx
    simp [hG, hD x hx, hD2 x hx]
  · refine ⟨fun _ => 0, continuous_const, ?_, ?_⟩
    · intro x hx
      exact (hD x hx).symm
    · intro x _
      rfl

end EthierKurtz.EZ213

open EthierKurtz

theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (hEst : ∃ lamstar : ℝ, 0 < lamstar ∧ ∃ C₀ : NNReal,
      ∀ (f h : (closure Ω) →ᵇ ℝ) (Ch : NNReal) (lam : ℝ),
        lamstar ≤ lam →
        HolderWith Ch ⟨μ, hμ.1.le⟩ ⇑h →
        (∃ g : (closure Ω) →ᵇ ℝ,
          (f, g) ∈ obliqueDiffusionGraph Ω μ a b c ∧ lam • f - g = h) →
        (∀ x : closure Ω,
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖ ≤
            ↑(C₀ * (Ch + 1))) ∧
        HolderWith (C₀ * (Ch + 1)) ⟨μ, hμ.1.le⟩ (fun x : closure Ω =>
          ‖⇑f x‖ + ∑ i : Fin (n + 1),
              ‖fderiv ℝ (closedRegionRestriction f) ↑x
                (EuclideanSpace.single i 1)‖ +
            ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              ‖fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f) y
                (EuclideanSpace.single j 1)) ↑x
                (EuclideanSpace.single i 1)‖)) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c,
          lam₀ • fg.1 - fg.2 = h := by
  exfalso
  obtain ⟨lamstar, -, C₀, hC⟩ := hEst
  obtain ⟨x0, hx0⟩ := hconnected.nonempty
  set f := BoundedContinuousFunction.const (closure Ω) ((C₀ : ℝ) + 1) with hf
  have hmem := EthierKurtz.EZ213.const_mem_graph Ω hopen μ a b c ((C₀ : ℝ) + 1)
  have hHold : HolderWith 0 ⟨μ, hμ.1.le⟩
      ⇑(BoundedContinuousFunction.const (closure Ω) (lamstar * ((C₀ : ℝ) + 1))) :=
    HolderWith.const
  have key := (hC f _ 0 lamstar le_rfl hHold
    ⟨0, hmem, by ext x; simp [hf]⟩).1 ⟨x0, subset_closure hx0⟩
  have h1 : ‖f ⟨x0, subset_closure hx0⟩‖ = (C₀ : ℝ) + 1 := by
    simp [hf, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C₀ : ℝ) + 1)]
  have h2 : ‖f ⟨x0, subset_closure hx0⟩‖ ≤ ((C₀ * (0 + 1) : NNReal) : ℝ) := by
    refine le_trans ?_ key
    have s1 : (0 : ℝ) ≤ ∑ i : Fin (n + 1),
        ‖fderiv ℝ (EthierKurtz.closedRegionRestriction f) x0 (EuclideanSpace.single i 1)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have s2 : (0 : ℝ) ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        ‖fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y
          (EuclideanSpace.single j 1)) x0 (EuclideanSpace.single i 1)‖ :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    linarith
  rw [h1] at h2
  simp at h2
  norm_num at h2
