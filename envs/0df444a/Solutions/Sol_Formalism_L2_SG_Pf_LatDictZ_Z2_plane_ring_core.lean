-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.plane_ring_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:09.353894+00:00
-- url     : https://prove2.me/submissions/9a35b828-b3d1-4544-a1ba-8c971dd4a09a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_IdealLike_cancel
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_ring_half
import Theorems.Thm_PIW_AdelClassFin_DictRing_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution {S : Subring K} {P Q : K → Prop} (hP : IdealLike S P) (hQ : IdealLike S Q)
    (hunit : ∀ a ∈ S, ¬ P a → ¬ Q a → IsUnitIn S a)
    {ε η γ α β c μ : K} (hε : ε ∈ S) (hη : η ∈ S) (hα : α ∈ S) (hβ : β ∈ S) (hc : c ∈ S)
    (hμ : IsUnitIn S μ) (hγ : α * ε + β * η + γ = 1) :
    IsUnitIn S ε ∨ IsUnitIn S η ∨ IsUnitIn S (ε + μ * η) ∨
      (IsUnitIn S (γ + ε + c * η) ∨ IsUnitIn S (γ + ε + (c + μ) * η) ∨
        IsUnitIn S (γ + c * ε + η) ∨ IsUnitIn S (γ + (c + μ) * ε + η)) := by
  by_cases hUε : IsUnitIn S ε
  · exact Or.inl hUε
  by_cases hUη : IsUnitIn S η
  · exact Or.inr (Or.inl hUη)
  have hε' : P ε ∨ Q ε := by
    by_contra hh
    push Not at hh
    exact hUε (hunit ε hε hh.1 hh.2)
  have hη' : P η ∨ Q η := by
    by_contra hh
    push Not at hh
    exact hUη (hunit η hη hh.1 hh.2)
  by_cases hPP : P ε ∧ P η
  · exact Or.inr (Or.inr (Or.inr (plane_ring_half hP hQ hunit hε hη hα hβ hc hμ hγ hPP.1 hPP.2)))
  by_cases hQQ : Q ε ∧ Q η
  · exact Or.inr (Or.inr (Or.inr (plane_ring_half hQ hP (fun a ha h1 h2 => hunit a ha h2 h1)
      hε hη hα hβ hc hμ hγ hQQ.1 hQQ.2)))
  refine Or.inr (Or.inr (Or.inl ?_))
  have m3 : ε + μ * η ∈ S := S.add_mem hε (S.mul_mem hμ.2.1 hη)
  rcases hε' with hPε | hQε
  · have hPη : ¬ P η := fun h => hPP ⟨hPε, h⟩
    have hQη : Q η := hη'.resolve_left hPη
    have hQε : ¬ Q ε := fun h => hQQ ⟨h, hQη⟩
    refine hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)
    · apply hPη
      apply hP.cancel hμ
      convert hP.1 _ _ h3 hPε using 1
      ring
    · apply hQε
      convert hQ.1 _ _ h3 (hQ.2.1 μ hμ.2.1 η hQη) using 1
      ring
  · have hQη : ¬ Q η := fun h => hQQ ⟨hQε, h⟩
    have hPη : P η := hη'.resolve_right hQη
    have hPε : ¬ P ε := fun h => hPP ⟨h, hPη⟩
    refine hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)
    · apply hPε
      convert hP.1 _ _ h3 (hP.2.1 μ hμ.2.1 η hPη) using 1
      ring
    · apply hQη
      apply hQ.cancel hμ
      convert hQ.1 _ _ h3 hQε using 1
      ring
end Formalism.L2.SG.Pf.LatDictZ.Z2
