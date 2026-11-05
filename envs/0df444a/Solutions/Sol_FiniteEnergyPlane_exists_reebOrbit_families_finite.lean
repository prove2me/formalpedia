-- Prove2me | solution 1 for FiniteEnergyPlane.exists_reebOrbit_families_finite
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T16:26:19.126595+00:00
-- url     : https://prove2.me/submissions/facfb0d0-7640-4a52-9da0-c20c111666cf

import Definitions.Def_FiniteEnergyPlane_Compactness
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_period_lower_bound
import Theorems.Thm_FiniteEnergyPlane_exists_reebOrbit_of_tendsto
import Theorems.Thm_FiniteEnergyPlane_exists_shift_of_isNondegenerate_of_near
import Theorems.Thm_FiniteEnergyPlane_exists_loop_gap_of_not_shift

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-! Finitely many families of periodic Reeb orbits of bounded period, with a `C⁰` gap. -/


namespace FiniteEnergyPlane

variable {n : ℕ} {H : V n → ℝ}

/-- Same period and time shift, on the orbits of period at most `T`. -/
def rofSetoid (H : V n → ℝ) (T : ℝ) : Setoid {Q : ReebOrbit H // Q.T ≤ T} where
  r A B := A.1.T = B.1.T ∧ ∃ c : ℝ, ∀ τ : ℝ, A.1.x τ = B.1.x (τ + c)
  iseqv :=
    { refl := fun A => ⟨rfl, 0, fun τ => by simp⟩
      symm := by
        rintro A B ⟨h, c, hc⟩
        refine ⟨h.symm, -c, fun τ => ?_⟩
        have := hc (τ + -c)
        rw [neg_add_cancel_right] at this
        exact this.symm
      trans := by
        rintro A B C ⟨h, c, hc⟩ ⟨h', c', hc'⟩
        refine ⟨h.trans h', c + c', fun τ => ?_⟩
        rw [hc τ, hc' (τ + c), add_assoc] }

lemma rofSetoid_finite (hH : IsStrictlyStarShapedLevel H) (T : ℝ)
    (hnd : ∀ Q : ReebOrbit H, Q.T ≤ T → Q.IsNondegenerate) :
    Finite (Quotient (rofSetoid H T)) := by
  by_contra hfin
  rw [not_finite_iff_infinite] at hfin
  let f := Infinite.natEmbedding (Quotient (rofSetoid H T))
  let Q : ℕ → {Q : ReebOrbit H // Q.T ≤ T} := fun k => (f k).out
  have hne : ∀ k l, k ≠ l → ¬ (rofSetoid H T).r (Q k) (Q l) := by
    intro k l hkl hr
    apply hkl
    apply f.injective
    have : (Quotient.mk (rofSetoid H T) (Q k)) = Quotient.mk (rofSetoid H T) (Q l) :=
      Quotient.sound hr
    simpa [Q, Quotient.out_eq] using this
  obtain ⟨T₀, hT₀, hT₀'⟩ := exists_period_lower_bound H hH
  have hK : IsCompact (energySurface H ×ˢ Icc T₀ T) :=
    (isCompact_energySurface H hH).prod isCompact_Icc
  obtain ⟨⟨p, T'⟩, hmem, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := fun k => ((Q k).1.x 0, (Q k).1.T))
    (fun k => ⟨(Q k).1.mem 0, hT₀' _, (Q k).2⟩)
  have hT'pos : 0 < T' := hT₀.trans_le hmem.2.1
  have hlim1 : Tendsto (fun k => (Q (φ k)).1.x 0) atTop (𝓝 p) :=
    (continuous_fst.tendsto _).comp hlim
  have hlim2 : Tendsto (fun k => (Q (φ k)).1.T) atTop (𝓝 T') :=
    (continuous_snd.tendsto _).comp hlim
  obtain ⟨P, hPT, hPx⟩ := exists_reebOrbit_of_tendsto H hH (fun k => (Q (φ k)).1) p T' hT'pos
    hlim1 hlim2
  have hPnd : P.IsNondegenerate := hnd P (by rw [hPT]; exact hmem.2.2)
  obtain ⟨r, hr, hrig⟩ := exists_shift_of_isNondegenerate_of_near H hH P hPnd
  have hev1 : ∀ᶠ k in atTop, |(Q (φ k)).1.T - P.T| < r := by
    rw [hPT]
    have := (Metric.tendsto_nhds.1 hlim2) r hr
    simpa [Real.dist_eq] using this
  have hev2 : ∀ᶠ k in atTop, ‖(Q (φ k)).1.x 0 - P.x 0‖ < r := by
    rw [hPx]
    have := (Metric.tendsto_nhds.1 hlim1) r hr
    simpa [dist_eq_norm] using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and hev2)
  obtain ⟨h1, c1, hc1⟩ := hrig _ (hN N le_rfl).1 (hN N le_rfl).2
  obtain ⟨h2, c2, hc2⟩ := hrig _ (hN (N + 1) (Nat.le_succ N)).1 (hN (N + 1) (Nat.le_succ N)).2
  refine hne (φ N) (φ (N + 1)) (hφ.injective.ne (by omega)) ⟨h1.trans h2.symm, c1 - c2, fun τ => ?_⟩
  rw [hc1 τ, hc2 (τ + (c1 - c2))]
  congr 1
  ring

theorem exists_reebOrbit_families_finite_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (T : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ T → Q.IsNondegenerate) :
    ∃ (N : ℕ) (Q : Fin N → ReebOrbit H) (δ : ℝ), 0 < δ ∧ (∀ i, (Q i).T ≤ T) ∧
      (∀ R : ReebOrbit H, R.T ≤ T →
        ∃ i, (Q i).T = R.T ∧ ∃ c : ℝ, ∀ τ : ℝ, R.x τ = (Q i).x (τ + c)) ∧
      ∀ i j, i ≠ j → ∀ c c' : ℝ, ∃ t : ℝ,
        δ ≤ ‖(Q i).x ((Q i).T * t + c) - (Q j).x ((Q j).T * t + c')‖ := by
  haveI := rofSetoid_finite hH T hnd
  let e := Finite.equivFin (Quotient (rofSetoid H T))
  let N := Nat.card (Quotient (rofSetoid H T))
  let A : Fin N → {Q : ReebOrbit H // Q.T ≤ T} := fun i => (e.symm i).out
  have hnot : ∀ i j, i ≠ j → ¬ ((A i).1.T = (A j).1.T ∧
      ∃ c : ℝ, ∀ τ : ℝ, (A i).1.x τ = (A j).1.x (τ + c)) := by
    intro i j hij hr
    apply hij
    apply e.symm.injective
    have : (Quotient.mk (rofSetoid H T) (A i)) = Quotient.mk (rofSetoid H T) (A j) :=
      Quotient.sound hr
    simpa [A, Quotient.out_eq] using this
  have hgap : ∀ p : Fin N × Fin N, ∃ δ : ℝ, 0 < δ ∧ (p.1 ≠ p.2 → ∀ c c' : ℝ, ∃ t : ℝ,
      δ ≤ ‖(A p.1).1.x ((A p.1).1.T * t + c) - (A p.2).1.x ((A p.2).1.T * t + c')‖) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · obtain ⟨δ, hδ, h⟩ := exists_loop_gap_of_not_shift H hH (A p.1).1 (A p.2).1 (hnot _ _ hp)
      exact ⟨δ, hδ, fun _ => h⟩
  choose d hd0 hd using hgap
  set S : Finset ℝ := insert 1 (Finset.univ.image d) with hS
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hδpos : 0 < S.min' hSne := by
    have hm := S.min'_mem hSne
    rcases Finset.mem_insert.1 hm with h | h
    · rw [h]; exact one_pos
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      rw [← hp]; exact hd0 p
  have hδle : ∀ p, S.min' hSne ≤ d p := fun p =>
    S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ p)))
  refine ⟨N, fun i => (A i).1, S.min' hSne, hδpos, fun i => (A i).2, ?_, ?_⟩
  · intro R hR
    let R' : {Q : ReebOrbit H // Q.T ≤ T} := ⟨R, hR⟩
    refine ⟨e (Quotient.mk (rofSetoid H T) R'), ?_⟩
    have hA : Quotient.mk (rofSetoid H T) (A (e (Quotient.mk (rofSetoid H T) R'))) =
        Quotient.mk (rofSetoid H T) R' := by
      simp [A, Quotient.out_eq]
    obtain ⟨h1, c, hc⟩ := Quotient.exact hA
    obtain ⟨h1', c', hc'⟩ := (rofSetoid H T).symm ⟨h1, c, hc⟩
    exact ⟨h1, c', hc'⟩
  · intro i j hij c c'
    obtain ⟨t, ht⟩ := hd (i, j) hij c c'
    exact ⟨t, (hδle (i, j)).trans ht⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (T : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ T → Q.IsNondegenerate) :
    ∃ (N : ℕ) (Q : Fin N → ReebOrbit H) (δ : ℝ), 0 < δ ∧ (∀ i, (Q i).T ≤ T) ∧
      (∀ R : ReebOrbit H, R.T ≤ T →
        ∃ i, (Q i).T = R.T ∧ ∃ c : ℝ, ∀ τ : ℝ, R.x τ = (Q i).x (τ + c)) ∧
      ∀ i j, i ≠ j → ∀ c c' : ℝ, ∃ t : ℝ,
        δ ≤ ‖(Q i).x ((Q i).T * t + c) - (Q j).x ((Q j).T * t + c')‖ :=
  exists_reebOrbit_families_finite_aux H hH T hnd
