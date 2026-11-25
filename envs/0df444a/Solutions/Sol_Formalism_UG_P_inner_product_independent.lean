-- Prove2me | solution 1 for Formalism.UG.P.inner_product_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:24:18.487015+00:00
-- url     : https://prove2.me/submissions/125d8202-d67d-46de-a91f-2f78f52c11df

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep
import Theorems.Thm_Formalism_UG_P_card_stabAt_mul

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
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.IpIndep := by
  intro G _ Γ K k _ _ W _ _ ρ _ B hB s s' hs hs' _ f hf f' hf'
  have hf2 : ∀ (γ : Γ) (g : G) (κ : K), f ((γ : G) * g * κ) = ρ γ (f g) := hf
  have hf2' : ∀ (γ : Γ) (g : G) (κ : K), f' ((γ : G) * g * κ) = ρ γ (f' g) := hf'
  unfold ipAMF
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨γ, hγ, κ, hκ, he⟩ := (DoubleCoset.eq _ _ (s c) (s' c)).1 ((hs c).trans (hs' c).symm)
  have h1 : s' c = ((⟨γ, hγ⟩ : Γ) : G) * s c * ((⟨κ, hκ⟩ : K) : G) := he
  rw [h1, card_stabAt_mul, hf2, hf2', hB]
end Formalism.UG.P
