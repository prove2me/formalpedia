-- Prove2me | solution 1 for Formalism.UG.P.extend_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:06.838713+00:00
-- url     : https://prove2.me/submissions/61ecb9f1-a66a-447e-bb6c-034d361d8bad

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
import Theorems.Thm_Formalism_UG_P_mk_of_eq
import Theorems.Thm_Formalism_UG_P_rho_eq_of_eq

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
variable {G : Type} [Group G] (Γ K : Subgroup G)
variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
namespace Formalism.UG.P
theorem _root_.solution (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (ρ : Representation k Γ W) (w : ClassSet Γ K → W)
    (hw : ∀ c, ∀ γ ∈ stabAt Γ K (s c), ρ γ (w c) = w c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    extend Γ K s hs ρ w g = ρ γ (w c) := by
  have hc : DoubleCoset.mk Γ K g = c := mk_of_eq Γ K s hs c g γ κ e
  have hp := Classical.choose_spec (exists_rep Γ K s hs g)
  unfold extend
  generalize Classical.choose (exists_rep Γ K s hs g) = p at hp ⊢
  rw [hc] at hp ⊢
  exact rho_eq_of_eq Γ K ρ (s c) (w c) (hw c) p.1 γ p.2 κ (hp.symm.trans e)
end Formalism.UG.P
