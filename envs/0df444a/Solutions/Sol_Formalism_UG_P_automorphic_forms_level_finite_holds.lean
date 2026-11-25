-- Prove2me | solution 1 for Formalism.UG.P.automorphic_forms_level_finite_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:31.840434+00:00
-- url     : https://prove2.me/submissions/1140df6f-8646-4bdb-9879-41cbffe6161b

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
import Theorems.Thm_Formalism_UG_P_mem_AMFK_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj
end Formalism.UG.P
