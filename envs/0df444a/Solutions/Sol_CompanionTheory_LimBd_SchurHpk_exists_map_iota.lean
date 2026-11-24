-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.exists_map_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:21:10.835326+00:00
-- url     : https://prove2.me/submissions/3b595a5c-61a3-4ee5-bd94-8ae23b2fd7b8

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_eq_smul_haar
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_iota_eq
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_iota_measEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution (hP : IsCayley k r ε P) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μG = Measure.map (iota (ε := ε) P) (c • muG ε) := by
  obtain ⟨hσ, h0, hnull, hinv⟩ := hμ
  have hE := iota_measEmb hP
  set ν : Measure (UJ ε) := Measure.comap (iota P) μG with hν
  have hmap : Measure.map (iota P) ν = μG := by
    rw [hν, hE.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    intro hxS
    exact hx (exists_iota_eq hP hxS)
  have : SigmaFinite ν := SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmap]; exact hσ)
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    have hl : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of (iota P g))) :=
      (show Measurable fun x : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => ∑ l, iota P g i l * x l j : Formalism.QuantumDeterminants.Mt k r) by fun_prop)
    have e : Measure.map (iota P) (Measure.map (g * ·) ν) = Measure.map (iota P) ν := by
      rw [Measure.map_map hE.measurable (measurable_const_mul g),
        show iota P ∘ (g * ·) = Formalism.QuantumDeterminants.lmulM (Matrix.of (iota P g)) ∘ iota P from
          funext fun h => iota_mul hP g h,
        ← Measure.map_map hl hE.measurable, hmap]
      exact hinv _ (iota_mem hP g)
    rw [← hE.comap_map (Measure.map (g * ·) ν), e, hE.comap_map]
  have hν0 : ν ≠ 0 := fun h => h0 (by rw [← hmap, h, Measure.map_zero])
  obtain ⟨c, hc0, hcT, e⟩ := exists_eq_smul_haar ν (muG ε) hν0
  exact ⟨c, hc0, hcT, by rw [← e, hmap]⟩
end CompanionTheory.LimBd.SchurHpk
