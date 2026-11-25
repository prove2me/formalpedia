-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.gat_nonempty_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:35:59.758184+00:00
-- url     : https://prove2.me/submissions/39a926a5-9afb-4ce9-bf2f-c5ea97581a03

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_exists_integral_nonzero_form
import Theorems.Thm_Formalism_MainNotions_G_Inhab_level1_finClasses
import Theorems.Thm_Formalism_MainNotions_G_Inhab_level1_trivStab
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ G.TrivStab ∧ G.FinClasses ∧ G.M ≠ ⊥ ∧ G.Mna ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Formalism.BasicNotions.Examples₂.LevelValuationRings.hidaSettingOfEven p 2 h5 le_rfl even_two
  obtain ⟨F, h1, h2, h3⟩ := exists_integral_nonzero_form h
  refine ⟨gat1 h, le_rfl, fun _ => level1_trivStab h, fun _ => level1_finClasses h, ?_, ?_⟩
  · intro hb; rw [hb] at h1; exact h3 ((Submodule.mem_bot _).1 h1)
  · intro hb; rw [hb] at h2; exact h3 ((Submodule.mem_bot _).1 h2)
end Formalism.MainNotions.G.Inhab
