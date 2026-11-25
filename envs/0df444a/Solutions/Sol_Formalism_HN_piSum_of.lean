-- Prove2me | solution 1 for Formalism.HN.piSum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:08.841798+00:00
-- url     : https://prove2.me/submissions/2e22dc9e-47fb-4647-93a0-d26d80ab535b

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_single
import Theorems.Thm_Formalism_HN_piSum_single_mu
import Theorems.Thm_Formalism_HN_piSum_inf
import Theorems.Thm_Formalism_HN_piSum_forall_insert
import Theorems.Thm_Formalism_HN_piSum_forall_insert_neg
import Theorems.Thm_Formalism_HN_piSum_forall_insert_only
import Theorems.Thm_Formalism_HN_piSum_orth
import Theorems.Thm_Formalism_HN_degree_supermodular
import Theorems.Thm_Formalism_HN_satBasic_zl_bot
import Theorems.Thm_Formalism_HN_saturation_basic_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe uR uι uV uE uS
namespace Formalism.HN
theorem _root_.solution (hS : HNSum.{uR, max uι uV, max uι uE, uS}) : PiSum.{uR, uι, uV, uE} := by
  intro R ι _ _ _ V E _ _ _ _ _ ρ L hL
  obtain ⟨-, hbin⟩ := hS R (∀ i, V i) (PiLp 2 E) (piReal ρ)
  have key : ∀ s : Finset ι, IsLat (piReal ρ) (piSumT L s) ∧
      rk (piReal ρ) (piSumT L s) = ∑ i ∈ s, rk (ρ i) (L i) ∧
      deg (piReal ρ) (piSumT L s) = ∑ i ∈ s, deg (ρ i) (L i) ∧
      ((∃ i ∈ s, L i ≠ ⊥) → piSumT L s ≠ ⊥ ∧ ∀ θ : ℝ,
        (muMax (piReal ρ) (piSumT L s) ≤ θ ↔ ∀ i ∈ s, L i ≠ ⊥ → muMax (ρ i) (L i) ≤ θ) ∧
        (θ ≤ muMin (piReal ρ) (piSumT L s) ↔ ∀ i ∈ s, L i ≠ ⊥ → θ ≤ muMin (ρ i) (L i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hT0 : piSumT L (∅ : Finset ι) = ⊥ := by simp [piSumT]
      rw [hT0]
      have hbot : IsLat (piReal ρ) (⊥ : Submodule R (∀ i, V i)) := by
        refine ⟨?_, ?_⟩
        · rw [Submodule.bot_coe]; exact Set.injOn_singleton _ _
        · rw [satBasic_zl_bot]; infer_instance
      obtain ⟨-, -, -, B4, B5, -⟩ := saturation_basic_properties _ _ _ (piReal ρ) _ hbot
      refine ⟨hbot, ?_, ?_, ?_⟩
      · rw [Finset.sum_empty]; exact (B4 ⊥ le_rfl).2 rfl
      · rw [Finset.sum_empty]; exact B5
      · rintro ⟨i, hi, -⟩
        exact absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      obtain ⟨ihL, ihr, ihd, ihm⟩ := ih
      have hT : piSumT L (insert a s) = piSumS L a ⊔ piSumT L s := Finset.iSup_insert a s _
      have hSa := piSum_single ρ a (L a) (hL a)
      have horth := piSum_orth ρ L a s ha
      obtain ⟨hLat, hdeg, hmu⟩ := hbin (piSumS L a) (piSumT L s) hSa.1 ihL horth
      have hrk := (degree_supermodular _ _ _ (piReal ρ) (piSumS L a ⊔ piSumT L s) (piSumS L a)
        (piSumT L s) hLat le_sup_left le_sup_right).1
      have hbot0 : rk (piReal ρ) (⊥ : Submodule R (∀ i, V i)) = 0 :=
        ((saturation_basic_properties _ _ _ (piReal ρ) _ hLat).2.2.2.1 ⊥ bot_le).2 rfl
      rw [piSum_inf L a s ha, hbot0] at hrk
      rw [hT]
      refine ⟨hLat, ?_, ?_, ?_⟩
      · have hra : rk (piReal ρ) (piSumS L a) = rk (ρ a) (L a) := hSa.2.1
        rw [Finset.sum_insert ha, ← ihr, ← hra]
        omega
      · rw [Finset.sum_insert ha, hdeg, ← ihd, ← hSa.2.2]
        rfl
      · intro hex
        by_cases ha0 : L a = ⊥
        · have hSa0 : piSumS L a = ⊥ := by
            show (L a).map _ = ⊥
            rw [ha0, Submodule.map_bot]
          have hex' : ∃ i ∈ s, L i ≠ ⊥ := by
            obtain ⟨i, hi, hi0⟩ := hex
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact absurd ha0 hi0
            · exact ⟨i, hi, hi0⟩
          obtain ⟨hT0, hm⟩ := ihm hex'
          rw [hSa0, bot_sup_eq]
          refine ⟨hT0, fun θ => ⟨?_, ?_⟩⟩
          · exact (hm θ).1.trans
              (piSum_forall_insert_neg s a (fun i => L i ≠ ⊥) _ (fun h => h ha0)).symm
          · exact (hm θ).2.trans
              (piSum_forall_insert_neg s a (fun i => L i ≠ ⊥) _ (fun h => h ha0)).symm
        · obtain ⟨hSa0, hma⟩ := piSum_single_mu ρ L a (hL a) ha0
          have hne : piSumS L a ⊔ piSumT L s ≠ ⊥ := fun h =>
            hSa0 (eq_bot_iff.2 (h ▸ le_sup_left))
          by_cases hs : ∃ i ∈ s, L i ≠ ⊥
          · obtain ⟨hT0, hm⟩ := ihm hs
            obtain ⟨emax, emin⟩ := hmu hSa0 hT0
            refine ⟨hne, fun θ => ⟨?_, ?_⟩⟩
            · rw [emax, max_le_iff, (hma θ).1, (hm θ).1]
              exact (piSum_forall_insert s a (fun i => L i ≠ ⊥)
                (fun i => muMax (ρ i) (L i) ≤ θ) ha0).symm
            · rw [emin, le_min_iff, (hma θ).2, (hm θ).2]
              exact (piSum_forall_insert s a (fun i => L i ≠ ⊥)
                (fun i => θ ≤ muMin (ρ i) (L i)) ha0).symm
          · push Not at hs
            have hTs : piSumT L s = ⊥ := by
              refine eq_bot_iff.2 (iSup₂_le fun i hi => ?_)
              show (L i).map _ ≤ ⊥
              rw [hs i hi, Submodule.map_bot]
            rw [hTs, sup_bot_eq]
            refine ⟨hSa0, fun θ => ⟨?_, ?_⟩⟩
            · exact (hma θ).1.trans (piSum_forall_insert_only s a (fun i => L i ≠ ⊥)
                (fun i => muMax (ρ i) (L i) ≤ θ) ha0
                (fun i hi h => h (hs i hi))).symm
            · exact (hma θ).2.trans (piSum_forall_insert_only s a (fun i => L i ≠ ⊥)
                (fun i => θ ≤ muMin (ρ i) (L i)) ha0
                (fun i hi h => h (hs i hi))).symm
  obtain ⟨h1, h2, h3, h4⟩ := key Finset.univ
  have hU : piSumT L Finset.univ = Submodule.pi Set.univ L := by
    simp only [piSumT, piSumS, Finset.mem_univ, iSup_pos]
    exact Submodule.iSup_map_single
  rw [hU] at h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun hex θ => ?_⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨-, hm⟩ := h4 ⟨i, Finset.mem_univ i, hi⟩
  simpa using hm θ
end Formalism.HN
