-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_filterNeTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:22.562493+00:00
-- url     : https://prove2.me/submissions/c6f8776a-08e6-47aa-afe9-bcd7fcc46b84

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasStrictNormalCrossingsWith_of_forall_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]
private theorem filterNeTop_nil : filterNeTop ([] : List X.IdealSheafData) = [] := rfl
private theorem filterNeTop_cons_of_ne_top (D : X.IdealSheafData) (T : List X.IdealSheafData)
    (h : D ≠ ⊤) : filterNeTop (D :: T) = D :: filterNeTop T := by
  simp [filterNeTop, h]
private theorem filterNeTop_cons_top (T : List X.IdealSheafData) :
    filterNeTop ((⊤ : X.IdealSheafData) :: T) = filterNeTop T := by
  simp [filterNeTop]
private theorem exists_index_map_of_filterNeTop_eq (n : ℕ) :
    ∀ (E E' : List X.IdealSheafData),
    E.length + E'.length ≤ n → filterNeTop E' = filterNeTop E →
    ∃ g : ℕ → ℕ,
      (∀ i, i < E'.length → E'[i]? ≠ some ⊤ → g i < E.length ∧ E[g i]? = E'[i]?) ∧
      (∀ i j, i < E'.length → j < E'.length → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
        g i = g j → i = j) := by
  induction n with
  | zero =>
    intro E E' hlen _
    have h0 : E'.length = 0 := by omega
    exact ⟨id, fun i hi _ => absurd hi (by omega), fun i j hi _ _ _ _ => absurd hi (by omega)⟩
  | succ n ih =>
    intro E E' hlen hfilt
    cases E' with
    | nil =>
      exact ⟨id, fun i hi _ => absurd hi (by simp), fun i j hi _ _ _ _ => absurd hi (by simp)⟩
    | cons D T' =>
      by_cases hD : D = ⊤
      · subst hD
        rw [filterNeTop_cons_top] at hfilt
        have hlen' : E.length + T'.length ≤ n := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨g₀, h1, h2⟩ := ih E T' hlen' hfilt
        refine ⟨unshiftIndex g₀, ?_, ?_⟩
        · intro i hi hne
          cases i with
          | zero => simp at hne
          | succ i =>
            simp only [List.getElem?_cons_succ] at hne
            simp only [List.length_cons] at hi
            simp only [unshiftIndex, List.getElem?_cons_succ]
            exact h1 i (by omega) hne
        · intro i j hi hj hni hnj hgij
          cases i with
          | zero => simp at hni
          | succ i =>
            cases j with
            | zero => simp at hnj
            | succ j =>
              have e1 : unshiftIndex g₀ (i + 1) = g₀ i := rfl
              have e2 : unshiftIndex g₀ (j + 1) = g₀ j := rfl
              have hij : g₀ i = g₀ j := by omega
              simp only [List.getElem?_cons_succ] at hni hnj
              simp only [List.length_cons] at hi hj
              have := h2 i j (by omega) (by omega) hni hnj hij
              omega
      · rw [filterNeTop_cons_of_ne_top D T' hD] at hfilt
        cases E with
        | nil =>
          rw [filterNeTop_nil] at hfilt
          exact absurd hfilt (List.cons_ne_nil _ _)
        | cons C T =>
          by_cases hC : C = ⊤
          · subst hC
            rw [filterNeTop_cons_top] at hfilt
            have hlen' : T.length + (D :: T').length ≤ n := by
              simp only [List.length_cons] at hlen ⊢
              omega
            have hfilt' : filterNeTop (D :: T') = filterNeTop T := by
              rw [filterNeTop_cons_of_ne_top D T' hD]
              exact hfilt
            obtain ⟨g₀, h1, h2⟩ := ih T (D :: T') hlen' hfilt'
            refine ⟨fun i => g₀ i + 1, ?_, ?_⟩
            · intro i hi hne
              obtain ⟨ha, hb⟩ := h1 i hi hne
              refine ⟨by simp only [List.length_cons]; omega, ?_⟩
              simpa using hb
            · intro i j hi hj hni hnj hgij
              have hgij' : g₀ i + 1 = g₀ j + 1 := hgij
              exact h2 i j hi hj hni hnj (by omega)
          · rw [filterNeTop_cons_of_ne_top C T hC] at hfilt
            simp only [List.cons.injEq] at hfilt
            obtain ⟨hcond, hTT⟩ := hfilt
            have hlen' : T.length + T'.length ≤ n := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨g₀, h1, h2⟩ := ih T T' hlen' hTT
            refine ⟨shiftIndex g₀, ?_, ?_⟩
            · intro i hi hne
              cases i with
              | zero =>
                simp only [shiftIndex]
                refine ⟨by simp, ?_⟩
                simp [hcond]
              | succ i =>
                simp only [List.getElem?_cons_succ] at hne
                simp only [List.length_cons] at hi
                obtain ⟨ha, hb⟩ := h1 i (by omega) hne
                simp only [shiftIndex, List.getElem?_cons_succ]
                exact ⟨by simp only [List.length_cons]; omega, hb⟩
            · intro i j hi hj hni hnj hgij
              cases i with
              | zero =>
                cases j with
                | zero => rfl
                | succ j =>
                  have e1 : shiftIndex g₀ 0 = 0 := rfl
                  have e2 : shiftIndex g₀ (j + 1) = g₀ j + 1 := rfl
                  omega
              | succ i =>
                cases j with
                | zero =>
                  have e1 : shiftIndex g₀ 0 = 0 := rfl
                  have e2 : shiftIndex g₀ (i + 1) = g₀ i + 1 := rfl
                  omega
                | succ j =>
                  have e1 : shiftIndex g₀ (i + 1) = g₀ i + 1 := rfl
                  have e2 : shiftIndex g₀ (j + 1) = g₀ j + 1 := rfl
                  have hij : g₀ i = g₀ j := by omega
                  simp only [List.getElem?_cons_succ] at hni hnj
                  simp only [List.length_cons] at hi hj
                  have := h2 i j (by omega) (by omega) hni hnj hij
                  omega
private theorem transportAssignment_of_eq_top {m : ℕ} (E' : List X.IdealSheafData)
    (a : ℕ → Option (Fin m)) (g : ℕ → ℕ) (i : ℕ) (h : E'[i]? = some ⊤) :
    transportAssignment E' a g i = none := by
  simp [transportAssignment, h]
private theorem transportAssignment_of_ne_top {m : ℕ} (E' : List X.IdealSheafData)
    (a : ℕ → Option (Fin m)) (g : ℕ → ℕ) (i : ℕ) (h : E'[i]? ≠ some ⊤) :
    transportAssignment E' a g i = a (g i) := by
  simp [transportAssignment, h]
private theorem transportAssignment_injective_and_coordIdeal {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (E E' : List X.IdealSheafData) (a : ℕ → Option (Fin m)) (g : ℕ → ℕ)
    (hg1 : ∀ i, i < E'.length → E'[i]? ≠ some ⊤ → g i < E.length ∧ E[g i]? = E'[i]?)
    (hg2 : ∀ i j, i < E'.length → j < E'.length → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
      g i = g j → i = j)
    (hinj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t}) :
    (∀ i < E'.length, ∀ j < E'.length, ∀ t : Fin m,
        transportAssignment E' a g i = some t → transportAssignment E' a g j = some t → i = j) ∧
      (∀ (i : ℕ) (hi : i < E'.length), transportAssignment E' a g i = none →
        restrictIdeal E'[i] U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < E'.length) (t : Fin m), transportAssignment E' a g i = some t →
        restrictIdeal E'[i] U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hni : E'[i]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top E' a g i hc] at hti
      simp at hti
    have hnj : E'[j]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top E' a g j hc] at htj
      simp at htj
    rw [transportAssignment_of_ne_top E' a g i hni] at hti
    rw [transportAssignment_of_ne_top E' a g j hnj] at htj
    obtain ⟨hgi, -⟩ := hg1 i hi hni
    obtain ⟨hgj, -⟩ := hg1 j hj hnj
    exact hg2 i j hi hj hni hnj (hinj (g i) hgi (g j) hgj t hti htj)
  · intro i hi hn
    by_cases hc : E'[i]? = some ⊤
    · have he : E'[i] = ⊤ := by
        rw [List.getElem?_eq_getElem hi] at hc
        exact Option.some_inj.mp hc
      rw [he]
      exact Scheme.IdealSheafData.comap_top U.ι
    · rw [transportAssignment_of_ne_top E' a g i hc] at hn
      obtain ⟨hgi, hb⟩ := hg1 i hi hc
      have he : E[g i] = E'[i] := by
        rw [List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi] at hb
        exact Option.some_inj.mp hb
      rw [← he]
      exact hnone (g i) hgi hn
  · intro i hi t hti
    have hc : E'[i]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top E' a g i hc] at hti
      simp at hti
    rw [transportAssignment_of_ne_top E' a g i hc] at hti
    obtain ⟨hgi, hb⟩ := hg1 i hi hc
    have he : E[g i] = E'[i] := by
      rw [List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi] at hb
      exact Option.some_inj.mp hb
    rw [← he]
    exact hsome (g i) hgi t hti
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData) (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith p Z E' := by
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq (E.length + E'.length) E E' le_rfl h.symm
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := hE.exists_etaleChart hx
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome
  exact ⟨U, hxU, m, c, transportAssignment E' a g, S, k1, k2, k3, hZ⟩
end FunctorialResolution.EmbeddedResolution
