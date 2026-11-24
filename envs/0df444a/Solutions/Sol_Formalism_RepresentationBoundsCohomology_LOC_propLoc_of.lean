-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.propLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:58:54.763453+00:00
-- url     : https://prove2.me/submissions/d77de3a7-7b4e-43eb-9c88-b19eeeb5d1fe

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_locDirect
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_locDualOrth
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_locTorsDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution (hQ : StatLocQuotLen.{u}) : StatPropLoc.{u} := by
  intro O A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr HfV HfV' ℓ e' d N δ ι₁ ι₂ P Q hann hδ hP hQ'
  have h1 : ∀ i, ∀ y ∈ (P i).HfY, ((ℓ : O) ^ e') • (P i).φs y ∈ HfV.map q :=
    fun i => locDirect O A HV q HfV (P i) ℓ e' (hP i).1 (hP i).2
  have h2 : ∀ i, ∀ y ∈ (Q i).HfY, ((ℓ : O) ^ e') • (Q i).φs y ∈ HfV.map q := by
    intro i y hy
    rw [hann]
    exact locDualOrth O A HT' pr (HfV'.comap j') (Q i) ℓ e' (hQ' i).1 (hQ' i).2.1 (hQ' i).2.2 y hy
  refine ⟨h1, h2, ?_⟩
  have hle : pushSpan P Q ≤ (HfV.map q).comap (LinearMap.lsmul O A ((ℓ : O) ^ e')) := by
    refine sup_le (iSup_le fun i => ?_) (iSup_le fun i => ?_)
    · rintro _ ⟨y, hy, rfl⟩
      exact h1 i y hy
    · rintro _ ⟨y, hy, rfl⟩
      exact h2 i y hy
  have hS : ∀ s ∈ pushSpan P Q, ((ℓ : O) ^ e') • s ∈ annih pr (HfV'.comap j') := fun s hs => by
    rw [← hann]
    exact hle hs
  have hT := locTorsDual O A HT' pr (HfV'.comap j') (pushSpan P Q) ((ℓ : O) ^ e') hS
  rw [← hann] at hT
  refine hT.trans ?_
  haveI : IsNoetherian O HT' := isNoetherian_of_isNoetherianRing_of_finite O HT'
  haveI : Module.Finite O (HfV'.comap j') := Module.IsNoetherian.finite O (HfV'.comap j')
  have htors : Submodule.torsion O HT' ≤ HfV'.comap j' := by
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have h0 : (a : O) • j' x = 0 := by
      rw [← map_smul]
      have : (a : O) • x = 0 := hax
      rw [this, map_zero]
    have hj : j' x = 0 :=
      ((Module.isTorsionFree_iff_smul_eq_zero.1 inferInstance (a : O) (j' x) h0).resolve_left
        (nonZeroDivisors.coe_ne_zero a))
    show j' x ∈ HfV'
    rw [hj]
    exact HfV'.zero_mem
  let δ' : N →ₗ[O] HfV'.comap j' :=
    δ.codRestrict (HfV'.comap j') (fun n => htors (hδ ▸ LinearMap.mem_range_self δ n))
  have htors' : Submodule.torsion O (HfV'.comap j') ≤ LinearMap.range δ' := by
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have hx' : (x : HT') ∈ Submodule.torsion O HT' := by
      refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
      have := congrArg Subtype.val hax
      simpa using this
    rw [← hδ] at hx'
    obtain ⟨n, hn⟩ := hx'
    exact ⟨n, Subtype.ext hn⟩
  exact hQ O (HfV'.comap j') d N δ' htors' ℓ e'
end Formalism.RepresentationBoundsCohomology.LOC
