-- Prove2me | solution 1 for Formalism.D5.balTop_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:19.926078+00:00
-- url     : https://prove2.me/submissions/ba11765f-1461-4071-874d-5a703c8f2e5f

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_thick_filter
import Theorems.Thm_Formalism_D5_thick_inj
import Theorems.Thm_Formalism_D5_rho_thick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private lemma sum_filter_sub_sum_filter_and_not_eq_sum {α : Type} [Fintype α] {p q : α → Prop}
    {hp : DecidablePred p} {hpq : DecidablePred (fun g => p g ∧ ¬ q g)}
    {s : Finset α} {F : α → ℂ} (hs : ∀ g, (p g ∧ q g) ↔ g ∈ s) :
    ∑ g ∈ Finset.univ.filter p, F g - ∑ g ∈ Finset.univ.filter (fun g => p g ∧ ¬ q g), F g
      = ∑ g ∈ s, F g := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  have h1 : ∑ g ∈ s, F g = ∑ g, (if g ∈ s then F g else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext g
    simp
  rw [h1]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have h := hs g
  split_ifs <;> first | (simp; done) | (exfalso; tauto) | rfl
end
end Formalism.D5
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5
theorem _root_.solution {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 t : H) (j : Fin m) :
    balTop Hs (Nd.a t) t (Nd.w u0 j) = (thickZ Hs Nd u0 t j).re +
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt Nd.T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((Nd.w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC Hs ψ (Nd.a t / Nd.w u0 j (cconj + g + topPl t))).re := by
  have hmem : ∀ g : E0 × H,
      (¬ InPhi (g + topPl t) ∧ IsThickAt Nd.T2 u0 (cconj + g + topPl t)) ↔
        g ∈ Nd.T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) := by
    intro g
    have h := Finset.ext_iff.mp (thick_filter Nd.T2 u0 t) g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  rw [balTop, thickZ, ← Complex.add_re, ← mul_add]
  congr 2
  rw [← sub_eq_iff_eq_add]
  refine (sum_filter_sub_sum_filter_and_not_eq_sum (p := fun g : E0 × H => ¬ InPhi (g + topPl t))
    (q := fun g : E0 × H => IsThickAt Nd.T2 u0 (cconj + g + topPl t)) hmem).trans ?_
  rw [Finset.sum_image ((thick_inj u0 t).mono (Set.subset_univ _))]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [rho_thick, Nd.w_thick u0 j s hs]
end Formalism.D5
