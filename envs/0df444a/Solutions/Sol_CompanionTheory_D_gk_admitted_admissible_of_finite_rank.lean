-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.admissible_of_finite_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:24.94179+00:00
-- url     : https://prove2.me/submissions/c30cf100-edd5-45dc-b99e-ffa547589f4e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
import Theorems.Thm_CompanionTheory_D_gk_admitted_exists_elt
import Theorems.Thm_CompanionTheory_D_gk_admitted_conjTranspose_mem
import Theorems.Thm_CompanionTheory_D_gk_admitted_Kset_sub
import Theorems.Thm_CompanionTheory_D_gk_admitted_continuous_toM
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : Iwa ε) : AdmUJ ε := by
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (KG ε) := (Measure.haar : Measure (KG ε)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (KG ε) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homUJ hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homUJ hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_toM fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (KG ε) μ H ((homUJ hσ).comp (KG ε).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ k.2 u hu) v hv
  choose st hst using fun g : UJ ε => exists_elt (conjTranspose_mem (m := toM g) g.2)
  let Tr : Set (UJ ε) := {s | (stdU ε hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU ε hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toM (st g) * U = (Uᴴ * toM g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU ε hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : UJ ε, U * stdU ε hU g * Uᴴ = toM g := fun g => by
      show U * (Uᴴ * toM g * U) * Uᴴ = _
      calc U * (Uᴴ * toM g * U) * Uᴴ = (U * Uᴴ) * toM g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact injective_coeMatrix ε ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : UJ ε, ∃ k ∈ KG ε, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toM g) g.2
    obtain ⟨k, rfl⟩ := exists_elt (Kset_sub hk)
    obtain ⟨s, rfl⟩ := exists_elt hs
    exact ⟨k, hk, s, ht, injective_coeMatrix ε hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → UJ ε, stdPoly E (fun i => homUJ hσ (g i)) = 0 := fun g =>
    h3 (UJ ε) (KG ε) μ st Tr (Fin n) (stdU ε hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (UJ ε) (KG ε) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homUJ hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (UJ ε) H (homUJ hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by
    obtain ⟨g, rfl⟩ := exists_elt hg
    exact hS' g u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ (toMK k) (T u) = T (e k • σ (toMK k) u)
    rw [map_smul, hT _ k.2]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
end CompanionTheory.D.gk.admitted
