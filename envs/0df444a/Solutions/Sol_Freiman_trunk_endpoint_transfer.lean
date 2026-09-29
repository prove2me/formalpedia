-- Prove2me | solution 1 for Freiman.trunk_endpoint_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:55:19.932979+00:00
-- url     : https://prove2.me/submissions/855ec750-6ac0-4beb-9678-47740d21f2ea

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (he : TrunkEndpointLaw) (hg : TrunkGreaterLaw)
    (p : LowerPair) (k : Fin 16) (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context)
    (sp : Section14Spec)
    (hs : ∀ b ∈ trunkBranches (trunkCatalog.states k).context sp,
      trunkHolds b.1 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) →
      lowerHistoryComparisonHolds b.2 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p))) :
    trunkSpecHolds p sp := by
  have hpar : (trunkCatalog.states k).context.parity.1 = false := by
    fin_cases k <;> rfl
  intro hextra
  obtain ⟨zx, cx, hzx, hcx, hex, hpx⟩ :=
    he (lowerNormalize p) (trunkCatalog.states k).context hf sp.first sp.firstUpper (trunkSpecIncoming sp)
  obtain ⟨zy, cy, hzy, hcy, hey, hpy⟩ :=
    he (lowerNormalize p) (trunkCatalog.states k).context hf sp.second sp.secondUpper (trunkSpecIncoming sp)
  have hmem : (sp.extra ++ cx ++ cy, trunkGreater (trunkCatalog.states k).context zx zy sp.strict) ∈
      trunkBranches (trunkCatalog.states k).context sp :=
    List.mem_flatMap.2 ⟨(zx, cx), hzx, List.mem_map.2 ⟨(zy, cy), hzy, rfl⟩⟩
  have hhold : trunkHolds (sp.extra ++ cx ++ cy) (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact hextra b hb
    · exact hcx b hb
    · exact hcy b hb
  have hcmp := (hg (lowerNormalize p) (trunkCatalog.states k).context hf zx zy hpx hpy sp.strict).1 (hs _ hmem hhold)
  have hframe : ∀ (w : LowerPair) (u : Bool), trunkSpecLocalEndpoint p w u (trunkSpecIncoming sp) =
      trunkFramedEndpoint (lowerNormalize p) (trunkCatalog.states k).context w u (trunkSpecIncoming sp) := by
    intro w u
    unfold trunkSpecLocalEndpoint trunkFramedEndpoint lowerHistoryCommonOdd
    rw [hpar]
    by_cases hc : (lowerNormalize p).1.length % 2 = 0
    · have h1 : ¬ ((lowerNormalize p).1.length % 2 = 1) := by omega
      simp [hc, h1]
    · have h1 : (lowerNormalize p).1.length % 2 = 1 := by omega
      simp [hc, h1]
  rw [hframe, hframe, hex, hey]
  exact hcmp
