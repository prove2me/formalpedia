-- Prove2me | solution 1 for FiniteEnergyPlane.exists_gradNorm_le_of_dlambdaEnergy_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:10:55.03353+00:00
-- url     : https://prove2.me/submissions/286c1a54-8157-4ad5-9fea-1c279c4f6307

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_FiniteEnergyPlane_exists_bubble
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A compact subset of `ℂ \ {0}` lies in all large members of a monotone open exhaustion. -/
theorem eventually_subset_of_exhaustion (D : ℕ → Set ℂ) (hDo : ∀ k, IsOpen (D k))
    (hDm : Monotone D) (hDu : ⋃ k, D k = {z : ℂ | z ≠ 0}) (K : Set ℂ) (hK : IsCompact K)
    (hK0 : K ⊆ {z : ℂ | z ≠ 0}) : ∀ᶠ k in atTop, K ⊆ D k := by
  obtain ⟨k₀, hk₀⟩ := hK.elim_directed_cover D hDo (by rwa [hDu]) hDm.directed_le
  filter_upwards [eventually_ge_atTop k₀] with k hk
  exact hk₀.trans (hDm hk)

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Curves on a monotone exhaustion of `ℂ \ {0}` with bounded Hofer energy and `dλ`-energy below
every period have gradients bounded on compact subsets, for all large indices. -/
theorem exists_gradNorm_le_of_dlambdaEnergy_le_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (U : ℕ → Set ℂ) (hUo : ∀ k, IsOpen (U k))
    (hUm : Monotone U) (hUu : ⋃ k, U k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J (U k) (v k)) (C e : ℝ)
    (hE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C)
    (hd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T) (K : Set ℂ) (hK : IsCompact K)
    (hK0 : K ⊆ {z : ℂ | z ≠ 0}) :
    ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, gradNorm H (v k) z ≤ M := by
  classical
  by_contra hcon
  push_neg at hcon
  have hev := eventually_subset_of_exhaustion U hUo hUm hUu K hK hK0
  have hfr : ∀ m : ℕ, ∃ᶠ k in atTop, K ⊆ U k ∧ ∃ z ∈ K, (m : ℝ) < gradNorm H (v k) z := by
    intro m
    exact ((hcon m).and_eventually hev).mono fun k hk => ⟨hk.2, hk.1⟩
  obtain ⟨ψ, hψ, hP⟩ := extraction_forall_of_frequently hfr
  have hP2 : ∀ j : ℕ, ∃ z ∈ K, (j : ℝ) < gradNorm H (v (ψ j)) z := fun j => (hP j).2
  choose z hzK hz using hP2
  have hsub0 : ∀ k, U k ⊆ {z : ℂ | z ≠ 0} := fun k => by
    rw [← hUu]; exact Set.subset_iUnion U k
  have hΓ : ((↑({0} : Finset ℂ) : Set ℂ))ᶜ = {z : ℂ | z ≠ 0} := by
    ext w; simp
  have hunion : ⋃ j, U (ψ j) = ((↑({0} : Finset ℂ) : Set ℂ))ᶜ := by
    rw [hΓ, ← hUu]
    apply Set.Subset.antisymm
    · exact Set.iUnion_mono' fun j => ⟨ψ j, subset_rfl⟩
    · exact Set.iUnion_mono fun j => hUm (hψ.id_le j)
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl 0
    (fun h0 => hK0 h0 rfl)
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨φ, -, z', r, P, -, -, -, hball, hPT, hlim⟩ := exists_bubble H hH J hJ {0}
    (fun j => U (ψ j)) (fun j => hUo _) (fun a b hab => hUm (hψ.monotone hab))
    (fun j => by rw [hΓ]; exact hsub0 _) hunion (fun j => v (ψ j)) (fun j => hv _) C
    (fun j => hE _) z (fun j => (hP j).1 (hzK j))
    (tendsto_atTop_mono (fun j => (hz j).le) tendsto_natCast_atTop_atTop)
    ⟨δ, hδ, fun k γ hγ => by
      rw [Finset.mem_singleton] at hγ
      subst hγ
      rw [sub_zero]
      by_contra hlt
      push_neg at hlt
      exact hδK (mem_ball_zero_iff.2 hlt) (hzK k)⟩
    (Or.inl ⟨R, fun k => hR _ (hzK k)⟩)
  have hle : limsup (fun j => dlambdaEnergy H (ball (z' j) (r j)) (v (ψ (φ j)))) atTop ≤
      ENNReal.ofReal e :=
    limsup_le_of_le (h := Eventually.of_forall fun j =>
      (lintegral_mono_set (hball j)).trans (hd _))
  have h2 := hlim.trans hle
  rw [ENNReal.ofReal_le_ofReal_iff'] at h2
  rcases h2 with h2 | h2
  · exact absurd (he₁ P hPT) (not_lt.2 h2)
  · exact absurd P.T_pos (not_lt.2 h2)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (U : ℕ → Set ℂ) (hUo : ∀ k, IsOpen (U k))
    (hUm : Monotone U) (hUu : ⋃ k, U k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J (U k) (v k)) (C e : ℝ)
    (hE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C)
    (hd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T) (K : Set ℂ) (hK : IsCompact K)
    (hK0 : K ⊆ {z : ℂ | z ≠ 0}) :
    ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, gradNorm H (v k) z ≤ M :=
  exists_gradNorm_le_of_dlambdaEnergy_le_aux H hH J hJ U hUo hUm hUu v hv C e hE hd he₁ K hK hK0
