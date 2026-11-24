-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:47.098831+00:00
-- url     : https://prove2.me/submissions/5598f719-5bf8-4495-bbcc-71d779d1d4c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_le_two_totient_sq

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  have hord : orderOf g = Units.torsionOrder E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rfl
  have hpos : 0 < Units.torsionOrder E := hord ▸ orderOf_pos g
  let f : NumberField.Units.torsion E →* E :=
    ((algebraMap (𝓞 E) E : 𝓞 E →+* E) : 𝓞 E →* E).comp
      ((Units.coeHom (𝓞 E)).comp (NumberField.Units.torsion E).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    exact (FaithfulSMul.algebraMap_injective (𝓞 E) E) hxy
  have hζ : IsPrimitiveRoot (f g) (Units.torsionOrder E) :=
    hord ▸ (IsPrimitiveRoot.orderOf g).map_of_injective hf
  have hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E := by
    rw [← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ hpos]
    exact minpoly.natDegree_le _
  calc Units.torsionOrder E ≤ 2 * (Units.torsionOrder E).totient ^ 2 := le_two_totient_sq _
    _ ≤ 2 * (Module.finrank ℚ E) ^ 2 := by gcongr
end Formalism.L2.SG.NGCut.TorsionTotientBound
