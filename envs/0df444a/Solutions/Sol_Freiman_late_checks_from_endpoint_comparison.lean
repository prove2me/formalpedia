-- Prove2me | solution 1 for Freiman.late_checks_from_endpoint_comparison
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:26:44.923905+00:00
-- url     : https://prove2.me/submissions/89d8bd00-1c7b-44d2-8e3e-f64f2f2a5065

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic
open Freiman
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private theorem lateEndpointWords : ∀ i : Fin 162,
    (lateEndpoint lateCatalog (i.val+1)).words.1 ≠ [] ∧
    (lateEndpoint lateCatalog (i.val+1)).words.2 ≠ [] := by decide +kernel
private theorem lateEndpointWordsOfIndex (i : ℕ) (hi : lateIndex i lateCatalog.endpoints.size) :
    (lateEndpoint lateCatalog i).words.1 ≠ [] ∧ (lateEndpoint lateCatalog i).words.2 ≠ [] := by
  have hn : 0 < i ∧ i ≤ 162 := hi
  have h := lateEndpointWords ⟨i-1,by omega⟩
  simpa only [Nat.sub_add_cancel hn.1] using h

theorem solution (he : lateEndpointLaw) (hg : lateGreaterLaw) (hl : ∀ z : CertField, (certFieldLower z : ℝ) ≤ certFieldVal z) : lateChecksLaw := by
  intro p i hi hm hv heall hr c hc
  have hcvalid := hv.2.2.2.2.2.2.2.2.2.2.2.1 c hc
  rcases hcvalid with ⟨hia,hib,hra,hrb,hma,hmb,hcomparison⟩
  obtain ⟨as,has,haRequired⟩ := hma
  obtain ⟨bs,hbs,hbRequired⟩ := hmb
  have hva := heall c.a hia
  have hvb := heall c.b hib
  have haHolds : lateHolds (lateBounds lateCatalog as) (lateR p) (lateS p) (lateQ p) := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    exact hr _ (List.mem_map.mpr ⟨j,haRequired j hj,rfl⟩)
  have hbHolds : lateHolds (lateBounds lateCatalog bs) (lateR p) (lateS p) (lateQ p) := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    exact hr _ (List.mem_map.mpr ⟨j,hbRequired j hj,rfl⟩)
  have haMatch : lateMatches p (lateEndpoint lateCatalog c.a).right3 := by simpa only [hra] using hm
  have hbMatch : lateMatches p (lateEndpoint lateCatalog c.b).right3 := by simpa only [hrb] using hm
  have haValue := he p _ haMatch (lateEndpointWordsOfIndex c.a hia).1
    (lateEndpointWordsOfIndex c.a hia).2 hva as has haHolds
  have hbValue := he p _ hbMatch (lateEndpointWordsOfIndex c.b hib).1
    (lateEndpointWordsOfIndex c.b hib).2 hvb bs hbs hbHolds
  have ha0 : 0 ≤ certFieldVal (lateEndpoint lateCatalog c.a).value.1 := by
    exact le_trans (by exact_mod_cast hva.2.1) (hl _)
  have ha1 : 0 ≤ certFieldVal (lateEndpoint lateCatalog c.a).value.2 := by
    exact le_trans (by exact_mod_cast hva.2.2.1) (hl _)
  have hb0 : 0 ≤ certFieldVal (lateEndpoint lateCatalog c.b).value.1 := by
    exact le_trans (by exact_mod_cast hvb.2.1) (hl _)
  have hb1 : 0 ≤ certFieldVal (lateEndpoint lateCatalog c.b).value.2 := by
    exact le_trans (by exact_mod_cast hvb.2.2.1) (hl _)
  have hholds : lowerHistoryComparisonHolds
      (lateGreater (lateEndpoint lateCatalog c.a).value (lateEndpoint lateCatalog c.b).value c.strict)
      (lateR p) (lateS p) (lateQ p) := by
    cases heq : lateGreater (lateEndpoint lateCatalog c.a).value (lateEndpoint lateCatalog c.b).value c.strict with
    | automatic => trivial
    | impossible => simpa only [heq] using hcomparison
    | bound b =>
      rw [heq] at hcomparison
      exact hr b hcomparison
  have result := hg p hm.1 _ _ ha0 ha1 hb0 hb1 c.strict hholds
  change (if c.strict then
    lateActualEndpoint p (lateEndpoint lateCatalog c.b).words (lateEndpoint lateCatalog c.b).upper <
      lateActualEndpoint p (lateEndpoint lateCatalog c.a).words (lateEndpoint lateCatalog c.a).upper
    else lateActualEndpoint p (lateEndpoint lateCatalog c.b).words (lateEndpoint lateCatalog c.b).upper ≤
      lateActualEndpoint p (lateEndpoint lateCatalog c.a).words (lateEndpoint lateCatalog c.a).upper)
  rw [haValue,hbValue]
  exact result
#print axioms solution
