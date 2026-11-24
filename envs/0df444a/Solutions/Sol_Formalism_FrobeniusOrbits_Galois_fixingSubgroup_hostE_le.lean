-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.fixingSubgroup_hostE_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:02.863056+00:00
-- url     : https://prove2.me/submissions/687917c5-7478-4997-af3f-16dea6758b40

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_trace_eq_iff_units
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_eq_neg_one_one_one_iff_eq_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_apply_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_one_val
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    (hostE ζ a b).fixingSubgroup ≤ Subgroup.zpowers (tau0 hqd h) := by
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have mem : ∀ y ∈ ({ζ + ζ⁻¹, a, b} : Set L), y ∈ hostE ζ a b := by
    intro y hy
    rw [hostE_eq_adjoin]
    exact IntermediateField.subset_adjoin ℚ _ hy
  have hθ := hσ _ (mem _ (Set.mem_insert _ _))
  have ha := hσ _ (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hb := hσ _ (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  rw [apply_theta h.1] at hθ
  have hc : h.1.autToPow ℚ σ = 1 ∨ h.1.autToPow ℚ σ = -1 := by
    rw [← trace_eq_iff_units h.1, hθ, Units.val_one, one_val, pow_one, pow_one]
  have hsa : sgn σ a = 1 := by rw [sgn.eq_1, if_pos ha]
  have hsb : sgn σ b = 1 := by rw [sgn.eq_1, if_pos hb]
  have hbij := (layer_galois hqd h).2.2.2
  rcases hc with hc | hc
  · have h1 : σ = 1 := by
      apply hbij.1
      rw [galMap.eq_1, galMap.eq_1, hc, hsa, hsb, map_one, sgn.eq_1, sgn.eq_1,
        if_pos (AlgEquiv.one_apply a), if_pos (AlgEquiv.one_apply b)]
    rw [h1]
    exact Subgroup.one_mem _
  · have h1 : σ = tau0 hqd h := by
      rw [← galMap_eq_neg_one_one_one_iff_eq_zeta_inversion hqd h, galMap.eq_1, hc, hsa, hsb]
    rw [h1]
    exact Subgroup.mem_zpowers _
end Formalism.FrobeniusOrbits.Galois
