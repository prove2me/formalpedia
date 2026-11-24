-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.TySet_repar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:04.943708+00:00
-- url     : https://prove2.me/submissions/1e73e446-51fc-490b-b727-52581f6dd8e3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_repar
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.TySet V g)
    (hxx : ∀ n, tyS V.l (fun s => x' s n) = PowerSeries.subst τ (tyS V.l fun s => x s n)) :
    x' ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hτs : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hs : ∀ f : PowerSeries C, PowerSeries.subst τ f = PowerSeries.substAlgHom hτs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hγ i).1, hint _ (hγ i).2⟩
  · intro q
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hlam q).1, hint _ (hlam q).2⟩
  · intro i
    rw [alongCv_repar hγ0 hτ, h1 i]
    simp only [hxx, hs, map_sum, map_smul]
  · intro q
    rw [hxx, h2 q, alongCv_repar hγ0 hτ]
    simp only [hxx, hs, map_add, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp
end Formalism.L2.FormalSeriesBounds.RawChart
