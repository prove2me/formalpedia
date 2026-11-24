-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.sub_smul_mem_span_init
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:46.076015+00:00
-- url     : https://prove2.me/submissions/c8069a3b-0381-423c-a54f-5344b691ab77

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution {n : ℕ} (w : Fin (n + 1) → V) (f : V →ₗ[E] E)
    (hf1 : f (w (Fin.last n)) = 1) (hf0 : ∀ i : Fin n, f (w i.castSucc) = 0) {x : V}
    (hx : x ∈ Submodule.span E (Set.range w)) :
    x - f x • w (Fin.last n) ∈ Submodule.span E (Set.range (Fin.init w)) := by
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  rw [Fin.sum_univ_castSucc]
  have hfx : f (∑ i : Fin n, k i.castSucc • w i.castSucc + k (Fin.last n) • w (Fin.last n)) =
      k (Fin.last n) := by
    simp [map_sum, hf0, hf1]
  rw [hfx, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.L2.SG.Pf.LatEx
