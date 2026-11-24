-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.edge_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:29:57.703813+00:00
-- url     : https://prove2.me/submissions/b3888640-2698-48fa-b7f0-82578149e2cf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
import Theorems.Thm_Formalism_MainNotions_G_Inhab_gen_mem
import Theorems.Thm_Formalism_MainNotions_G_Inhab_p_smul_gen
import Theorems.Thm_Formalism_MainNotions_G_Inhab_lat1
import Theorems.Thm_Formalism_MainNotions_G_Inhab_le_of_mem


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
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (e : Edge W Qq 1) (he : IsEdge p n' 1 e) :
    ∃ a : ℤ, e = edge1 W Qq p a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  obtain ⟨s, t⟩ := e
  obtain ⟨b, rfl⟩ := lat1 h s h1
  obtain ⟨a, rfl⟩ := lat1 h t h2
  have hab : a ≤ b := le_of_mem h (h3 (gen_mem b))
  have hba : b ≤ a + 1 := by
    have := h4 _ (gen_mem a)
    rw [p_smul_gen h] at this
    exact le_of_mem h this
  refine ⟨a, ?_⟩
  rcases (by omega : b = a + 1 ∨ b = a) with rfl | rfl
  · rfl
  · exfalso
    have htop : Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b) = ⊤ := Submodule.comap_subtype_self _
    have h5' : Nat.card (↥(line W (Qq := Qq) p b) ⧸ Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b)) =
      p ^ (n' * 1) := h5
    rw [htop] at h5'
    have h6 : Nat.card (↥(line W (Qq := Qq) p b) ⧸ (⊤ : Submodule W ↥(line W (Qq := Qq) p b))) = 1 :=
      Nat.card_unique
    rw [h6] at h5'
    have h7 : 1 < p ^ (n' * 1) := Nat.one_lt_pow (by have := h.two_le; omega) (by have := h.five_le; omega)
    omega
end Formalism.MainNotions.G.Inhab
